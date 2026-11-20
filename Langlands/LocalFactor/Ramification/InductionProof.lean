import Langlands.LocalFactor.Ramification.InductionStatement
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Proof of the conductor formula for induced finite-Galois representations

The proof counts fixed vectors. For a normal subgroup `N` of a finite group `G` and an
injective homomorphism `φ : H →* G`, the `N`-fixed vectors of `Ind_H^G ψ` have dimension
`[G : φ(H) N] · dim ψ^(φ⁻¹ N)`. The lower ramification groups of `Gal(F/K')` are the
preimages of those of `Gal(F/K)`, and the conductor formula follows term by term.
-/

noncomputable section

namespace Langlands.InducedFixedVectors

open Module

universe uk uG uH uV

section Fixed

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]

theorem mem_fixedVectors_iff {ρ : Representation k G V} {K : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ K ↔ ∀ g ∈ K, ρ g v = v := by
  simp [fixedVectors, Representation.mem_invariants]

theorem fixedVectors_bot (ρ : Representation k G V) : fixedVectors ρ ⊥ = ⊤ := by
  ext v
  simp only [mem_fixedVectors_iff, Subgroup.mem_bot, forall_eq, map_one,
    Module.End.one_apply, Submodule.mem_top]

theorem fixedVectors_trivial (K : Subgroup G) :
    fixedVectors (Representation.trivial k G V) K = ⊤ := by
  ext v
  simp only [mem_fixedVectors_iff, Representation.trivial_apply, implies_true,
    Submodule.mem_top]

end Fixed

section Coind

variable {k : Type uk} [Field k] {G : Type uG} {H : Type uH} [Group G] [Group H]
  {V : Type uV} [AddCommGroup V] [Module k V]
  (φ : H →* G) (ψ : Representation k H V) (N : Subgroup G) [hN : N.Normal]

/-- Right cosets of the subgroup `φ(H) N`. -/
abbrev Cosets := Quotient (QuotientGroup.rightRel (φ.range ⊔ N))

/-- The right coset of `g` modulo `φ(H) N`. -/
def coset (g : G) : Cosets φ N := Quotient.mk _ g

omit hN in
theorem coset_out (q : Cosets φ N) : coset φ N q.out = q := Quotient.out_eq q

omit hN in
theorem mul_out_inv_mem (g : G) : g * (coset φ N g).out⁻¹ ∈ φ.range ⊔ N :=
  QuotientGroup.rightRel_apply.mp (Quotient.exact (coset_out φ N (coset φ N g)))

omit hN in
theorem coset_eq_of_mul_inv_mem {g g' : G} (h : g' * g⁻¹ ∈ φ.range ⊔ N) :
    coset φ N g = coset φ N g' :=
  Quotient.sound (QuotientGroup.rightRel_apply.mpr h)

omit hN in
theorem exists_factor [N.Normal] {x : G} (hx : x ∈ φ.range ⊔ N) :
    ∃ h : H, (φ h)⁻¹ * x ∈ N := by
  obtain ⟨y, ⟨h, rfl⟩, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  exact ⟨h, by simpa using hz⟩

/-- A chosen `h` with `g ∈ φ(h) N (coset representative of g)`. -/
def factor (g : G) : H := (exists_factor φ N (mul_out_inv_mem φ N g)).choose

theorem factor_spec (g : G) :
    (φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹) ∈ N :=
  (exists_factor φ N (mul_out_inv_mem φ N g)).choose_spec

omit hN in
theorem apply_eq_of_mem {v : V} (hv : v ∈ fixedVectors ψ (N.comap φ)) {h₁ h₂ : H}
    (h : (φ h₁)⁻¹ * φ h₂ ∈ N) : ψ h₁ v = ψ h₂ v := by
  have h' : h₁⁻¹ * h₂ ∈ N.comap φ := by simpa [Subgroup.mem_comap] using h
  have hfix := (mem_fixedVectors_iff.mp hv) _ h'
  calc ψ h₁ v = ψ h₁ (ψ (h₁⁻¹ * h₂) v) := by rw [hfix]
    _ = ψ h₂ v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- Evaluation of an `N`-fixed equivariant function at the chosen coset representatives. -/
def fixedCoindToCosets :
    fixedVectors (Representation.coind φ ψ) N →ₗ[k]
      (Cosets φ N → fixedVectors ψ (N.comap φ)) where
  toFun f q := ⟨(f : Representation.coindV φ ψ).1 q.out, by
    rw [mem_fixedVectors_iff]
    intro h hh
    have hn : (q.out)⁻¹ * φ h * q.out ∈ N := hN.conj_mem' _ hh _
    have hf := (mem_fixedVectors_iff.mp f.2) _ hn
    calc ψ h ((f : Representation.coindV φ ψ).1 q.out)
        = (f : Representation.coindV φ ψ).1 (φ h * q.out) :=
          ((f : Representation.coindV φ ψ).2 h q.out).symm
      _ = (f : Representation.coindV φ ψ).1 (q.out * ((q.out)⁻¹ * φ h * q.out)) :=
          congrArg _ (by group)
      _ = ((Representation.coind φ ψ ((q.out)⁻¹ * φ h * q.out))
            (f : Representation.coindV φ ψ)).1 q.out := rfl
      _ = (f : Representation.coindV φ ψ).1 q.out := by rw [hf]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `N`-fixed equivariant function with prescribed values at the coset representatives. -/
def cosetsToFixedCoind :
    (Cosets φ N → fixedVectors ψ (N.comap φ)) →ₗ[k]
      fixedVectors (Representation.coind φ ψ) N where
  toFun v := ⟨⟨fun g => ψ (factor φ N g) (v (coset φ N g)), by
      intro h g
      have hc : coset φ N (φ h * g) = coset φ N g := coset_eq_of_mul_inv_mem φ N (by
        have he : g * (φ h * g)⁻¹ = (φ h)⁻¹ := by group
        rw [he]
        exact Subgroup.mem_sup_left (Subgroup.inv_mem _ ⟨h, rfl⟩))
      have h1 := factor_spec φ N (φ h * g)
      have h2 := factor_spec φ N g
      rw [hc] at h1
      simp only
      rw [hc, ← Module.End.mul_apply, ← map_mul]
      apply apply_eq_of_mem φ ψ N (v (coset φ N g)).2
      have he : (φ (factor φ N (φ h * g)))⁻¹ * φ (h * factor φ N g) =
          ((φ (factor φ N (φ h * g)))⁻¹ * (φ h * g * (coset φ N g).out⁻¹)) *
            ((φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹))⁻¹ := by
        rw [map_mul]; group
      rw [he]
      exact N.mul_mem h1 (N.inv_mem h2)⟩, by
    rw [mem_fixedVectors_iff]
    intro n hn
    apply Subtype.ext
    funext g
    change ψ (factor φ N (g * n)) (v (coset φ N (g * n))) =
      ψ (factor φ N g) (v (coset φ N g))
    have hc : coset φ N (g * n) = coset φ N g := coset_eq_of_mul_inv_mem φ N (by
      have he : g * (g * n)⁻¹ = g * n⁻¹ * g⁻¹ := by group
      rw [he]
      exact Subgroup.mem_sup_right (hN.conj_mem _ (N.inv_mem hn) g))
    have h1 := factor_spec φ N (g * n)
    have h2 := factor_spec φ N g
    rw [hc] at h1
    rw [hc]
    apply apply_eq_of_mem φ ψ N (v (coset φ N g)).2
    have h3 : (coset φ N g).out * n⁻¹ * (coset φ N g).out⁻¹ ∈ N :=
      hN.conj_mem _ (N.inv_mem hn) _
    have he : (φ (factor φ N (g * n)))⁻¹ * φ (factor φ N g) =
        ((φ (factor φ N (g * n)))⁻¹ * (g * n * (coset φ N g).out⁻¹)) *
          ((coset φ N g).out * n⁻¹ * (coset φ N g).out⁻¹) *
            ((φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹))⁻¹ := by
      group
    rw [he]
    exact N.mul_mem (N.mul_mem h1 h3) (N.inv_mem h2)⟩
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    simp
  map_smul' c v := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    simp

/-- `N`-fixed vectors of a coinduced representation are determined by their values at
coset representatives of `φ(H) N`, which are arbitrary `φ⁻¹ N`-fixed vectors. -/
def fixedCoindEquiv :
    fixedVectors (Representation.coind φ ψ) N ≃ₗ[k]
      (Cosets φ N → fixedVectors ψ (N.comap φ)) :=
  { fixedCoindToCosets φ ψ N with
    invFun := cosetsToFixedCoind φ ψ N
    left_inv := by
      intro f
      apply Subtype.ext
      apply Subtype.ext
      funext g
      change ψ (factor φ N g) ((f : Representation.coindV φ ψ).1 (coset φ N g).out) =
        (f : Representation.coindV φ ψ).1 g
      have hn := factor_spec φ N g
      have hn' : ((coset φ N g).out)⁻¹ *
          ((φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹)) * (coset φ N g).out ∈ N :=
        hN.conj_mem' _ hn _
      have hf := (mem_fixedVectors_iff.mp f.2) _ hn'
      calc ψ (factor φ N g) ((f : Representation.coindV φ ψ).1 (coset φ N g).out)
          = ψ (factor φ N g) (((Representation.coind φ ψ (((coset φ N g).out)⁻¹ *
              ((φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹)) * (coset φ N g).out))
              (f : Representation.coindV φ ψ)).1 (coset φ N g).out) := by rw [hf]
        _ = ψ (factor φ N g) ((f : Representation.coindV φ ψ).1 ((coset φ N g).out *
              (((coset φ N g).out)⁻¹ * ((φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹)) *
                (coset φ N g).out))) := rfl
        _ = (f : Representation.coindV φ ψ).1 (φ (factor φ N g) * ((coset φ N g).out *
              (((coset φ N g).out)⁻¹ * ((φ (factor φ N g))⁻¹ * (g * (coset φ N g).out⁻¹)) *
                (coset φ N g).out))) :=
            ((f : Representation.coindV φ ψ).2 _ _).symm
        _ = (f : Representation.coindV φ ψ).1 g := congrArg _ (by group)
    right_inv := by
      intro v
      funext q
      apply Subtype.ext
      change ψ (factor φ N q.out) (v (coset φ N q.out) : V) = (v q : V)
      have h1 := factor_spec φ N q.out
      rw [coset_out] at h1
      rw [coset_out]
      have hmem : factor φ N q.out ∈ N.comap φ := by
        simpa [Subgroup.mem_comap] using h1
      exact (mem_fixedVectors_iff.mp (v q).2) _ hmem }

theorem finrank_fixedVectors_coind [Finite G] [FiniteDimensional k V] :
    finrank k (fixedVectors (Representation.coind φ ψ) N) =
      (φ.range ⊔ N).index * finrank k (fixedVectors ψ (N.comap φ)) := by
  classical
  let : Fintype (Cosets φ N) := Fintype.ofFinite _
  rw [(fixedCoindEquiv φ ψ N).finrank_eq, Module.finrank_pi_fintype k]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  rw [Subgroup.index, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)

end Coind

section Ind

variable {k : Type} [Field k] {G : Type uG} {H : Type uH} [Group G] [Group H]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {φ : H →* G} (hφ : Function.Injective φ) (ψ : Representation k H V)

/-- The representation of the range of `φ` corresponding to `ψ`. -/
def rangeRep : Representation k φ.range V :=
  ψ.comp (MonoidHom.ofInjective hφ).symm.toMonoidHom

@[simp]
theorem rangeRep_ofInjective (h : H) : rangeRep hφ ψ (MonoidHom.ofInjective hφ h) = ψ h := by
  simp [rangeRep]

/-- Induction along an injective homomorphism agrees with induction from its range:
both are quotients of `k[G] ⊗ V` by the same submodule. -/
def indRangeEquiv :
    (Representation.ind φ ψ).Equiv (Representation.ind φ.range.subtype (rangeRep hφ ψ)) := by
  have hρ (h : H) :
      Representation.tprod ((Representation.leftRegular k G).comp φ.range.subtype)
          (rangeRep hφ ψ) (MonoidHom.ofInjective hφ h) =
        Representation.tprod ((Representation.leftRegular k G).comp φ) ψ h := by
    simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, MonoidHom.ofInjective_apply, rangeRep_ofInjective]
  refine Representation.Equiv.mk
    { toLinearMap := Representation.Coinvariants.lift _
        (Representation.Coinvariants.mk _) (fun h => by
          rw [← hρ h]
          exact LinearMap.ext fun x => Representation.Coinvariants.mk_self_apply _ _ x)
      invFun := Representation.Coinvariants.lift _
        (Representation.Coinvariants.mk _) (fun s => by
          obtain ⟨h, rfl⟩ := (MonoidHom.ofInjective hφ).surjective s
          rw [hρ h]
          exact LinearMap.ext fun x => Representation.Coinvariants.mk_self_apply _ _ x)
      left_inv := fun x => by
        induction x using Representation.Coinvariants.induction_on with
        | h v => rfl
      right_inv := fun x => by
        induction x using Representation.Coinvariants.induction_on with
        | h v => rfl } ?_
  intro g
  ext h v
  simp

/-- The composite equivalence from Mathlib's induction to coinduction along an injective
homomorphism of finite-index range. -/
def indCoindEquiv [φ.range.FiniteIndex] :
    (Representation.ind φ ψ).Equiv (Representation.coind φ ψ) := by
  classical
  have hcoind : Representation.coindV φ.range.subtype (rangeRep hφ ψ) =
      Representation.coindV φ ψ := by
    ext f
    simp only [Representation.mem_coindV]
    constructor
    · intro hf h g
      simpa [MonoidHom.ofInjective_apply] using hf (MonoidHom.ofInjective hφ h) g
    · intro hf s g
      obtain ⟨h, rfl⟩ := (MonoidHom.ofInjective hφ).surjective s
      simpa [MonoidHom.ofInjective_apply] using hf h g
  let e₃ : (Representation.coind φ.range.subtype (rangeRep hφ ψ)).Equiv
      (Representation.coind φ ψ) :=
    Representation.Equiv.mk (LinearEquiv.ofEq _ _ hcoind) (fun g => by
      ext f x
      rfl)
  let e₂ : (Representation.ind φ.range.subtype (rangeRep hφ ψ)).Equiv
      (Representation.coind φ.range.subtype (rangeRep hφ ψ)) :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of (rangeRep hφ ψ)))
  exact (indRangeEquiv hφ ψ).trans (e₂.trans e₃)

include hφ in
/-- Fixed vectors of an induced representation under a normal subgroup. -/
theorem finrank_fixedVectors_ind [Finite G] [FiniteDimensional k V]
    (N : Subgroup G) [N.Normal] :
    finrank k (fixedVectors (Representation.ind φ ψ) N) =
      (φ.range ⊔ N).index * finrank k (fixedVectors ψ (N.comap φ)) := by
  rw [(fixedVectorsEquiv (indCoindEquiv hφ ψ) N).finrank_eq]
  exact finrank_fixedVectors_coind φ ψ N

include hφ in
/-- The dimension of an induced representation. -/
theorem finrank_ind [Finite G] [FiniteDimensional k V] :
    finrank k (Representation.IndV φ ψ) = φ.range.index * finrank k V := by
  have h := finrank_fixedVectors_ind hφ ψ (⊥ : Subgroup G)
  rw [fixedVectors_bot, finrank_top, sup_bot_eq, MonoidHom.comap_bot,
    (MonoidHom.ker_eq_bot_iff φ).mpr hφ, fixedVectors_bot, finrank_top] at h
  exact h

end Ind

end Langlands.InducedFixedVectors

namespace Langlands.Ramification.Padic

open Module Langlands.InducedFixedVectors

universe uK uK' uL uV uW

section Sum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- The Artin expression as a finite sum over any proved termination bound of the lower
filtration. -/
theorem artinConductor_eq_sum (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W) (b : ℕ)
    (hb : ∀ i ≥ b, lowerRamificationGroup T K i = ⊥) :
    artinConductor T K ρ = ∑ i ∈ Finset.range b,
      (Nat.card (lowerRamificationGroup T K i) : ℚ) / Nat.card (lowerRamificationGroup T K 0) *
        ((finrank ℂ W : ℚ) - finrank ℂ (fixedVectors ρ (lowerRamificationGroup T K i))) := by
  let := integerAction T K
  have : FaithfulSMul (F.Carrier ≃ₐ[K] F.Carrier) T.Integers := by
    let := T.valuativeRel
    have : IsFractionRing T.Integers F.Carrier :=
      inferInstanceAs (IsFractionRing
        (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
    refine ⟨fun {σ τ} h => ?_⟩
    have heq : σ.toRingHom = τ.toRingHom :=
      IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
        congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
    exact AlgEquiv.ext fun x => RingHom.congr_fun heq x
  have : IsNoetherianRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  have : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
    have : FiniteDimensional K F.Carrier :=
      Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
    infer_instance
  change Ramification.artinConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ = _
  rw [Ramification.artinConductor_eq_sum_range T.Integers _ ρ b hb]
  apply Finset.sum_congr rfl
  intro i _
  show (Nat.card (lowerRamificationGroup T K i) : ℚ) / Nat.card (lowerRamificationGroup T K 0) *
      ((finrank ℂ W - finrank ℂ (fixedVectors ρ (lowerRamificationGroup T K i)) : ℕ) : ℚ) = _
  rw [Nat.cast_sub (Submodule.finrank_le _)]

end Sum

section Main

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  (K' : Type uK') [Field K'] [Algebra (Padic p) K'] [Algebra K K']
  [Algebra K' F.Carrier] [IsScalarTower (Padic p) K' F.Carrier]
  [IsScalarTower K K' F.Carrier]

/-- The lower ramification groups of `Gal(F/K')` are the preimages of those of `Gal(F/K)`
under restriction of scalars. -/
theorem lowerRamificationGroup_comap (i : ℕ) :
    (lowerRamificationGroup T K i).comap
        (AlgEquiv.restrictScalarsHom (S := K') (A := F.Carrier) K) =
      lowerRamificationGroup T K' i := by
  ext σ
  rw [Subgroup.mem_comap, mem_lowerRamificationGroup, mem_lowerRamificationGroup]
  have h (x : T.Integers) : integerAutomorphism T K
      (AlgEquiv.restrictScalarsHom (S := K') (A := F.Carrier) K σ) x =
      integerAutomorphism T K' σ x := Subtype.ext rfl
  simp only [h]

/-- The rational identity behind each summand of the induction formula. -/
theorem induction_term_identity {gi g0 hi h0 d n r I J a b ci cG cH : ℚ}
    (hg0 : g0 ≠ 0) (hbh0 : b * h0 ≠ 0)
    (r1 : J * I = ci) (r2 : ci * gi = cG) (r3 : J * hi = cH) (r4 : a * g0 = cG)
    (r5 : b * h0 = cH) :
    gi / g0 * (r * d - I * n) = d * (gi / g0 * (r * 1 - I * 1)) + a / b * (hi / h0 * (d - n)) := by
  have key : gi / g0 * I = a / b * (hi / h0) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm, div_eq_div_iff hg0 hbh0]
    linear_combination gi * I * r5 - gi * I * r3 + gi * hi * r1 + hi * r2 - hi * r4
  linear_combination (d - n) * key

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Induction formula** (Serre, *Local Fields*, VI.2, Prop. 4, Cor.) for the published
Artin expressions of finite subextensions of a p-adic field. -/
theorem finiteGaloisInducedConductor :
    FiniteGaloisInducedConductorStatement T K K' (V := V) := by
  unfold FiniteGaloisInducedConductorStatement
  intro _ ψ φ
  classical
  have hφ : Function.Injective φ := AlgEquiv.restrictScalarsHom_injective K
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  have : Finite (F.Carrier ≃ₐ[K] F.Carrier) := inferInstance
  have : Finite (F.Carrier ≃ₐ[K'] F.Carrier) := Finite.of_injective φ hφ
  obtain ⟨b, hb⟩ := exists_lowerRamificationGroup_eq_bot T K
  have hcomap (i : ℕ) :
      (lowerRamificationGroup T K i).comap φ = lowerRamificationGroup T K' i :=
    lowerRamificationGroup_comap T K K' i
  have hb' : ∀ i ≥ b, lowerRamificationGroup T K' i = ⊥ := by
    intro i hi
    rw [← hcomap, hb i hi, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff φ).mpr hφ]
  rw [← lowerRamificationGroup_zero T K, ← lowerRamificationGroup_zero T K',
    artinConductor_eq_sum T K _ b hb, artinConductor_eq_sum T K _ b hb,
    artinConductor_eq_sum T K' ψ b hb', Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [finrank_ind hφ, finrank_ind hφ, finrank_fixedVectors_ind hφ,
    finrank_fixedVectors_ind hφ, hcomap, fixedVectors_trivial, finrank_top,
    Module.finrank_self]
  have r1 : ((lowerRamificationGroup T K' i).index : ℚ) *
      (φ.range ⊔ lowerRamificationGroup T K i).index =
        (lowerRamificationGroup T K i).index := by
    rw [← hcomap, Subgroup.index_comap, ← Subgroup.relIndex_sup_right]
    exact_mod_cast Subgroup.relIndex_mul_index le_sup_right
  have r2 : ((lowerRamificationGroup T K i).index : ℚ) *
      Nat.card (lowerRamificationGroup T K i) = Nat.card (F.Carrier ≃ₐ[K] F.Carrier) := by
    exact_mod_cast Subgroup.index_mul_card _
  have r3 : ((lowerRamificationGroup T K' i).index : ℚ) *
      Nat.card (lowerRamificationGroup T K' i) = Nat.card (F.Carrier ≃ₐ[K'] F.Carrier) := by
    exact_mod_cast Subgroup.index_mul_card _
  have r4 : ((lowerRamificationGroup T K 0).index : ℚ) *
      Nat.card (lowerRamificationGroup T K 0) = Nat.card (F.Carrier ≃ₐ[K] F.Carrier) := by
    exact_mod_cast Subgroup.index_mul_card _
  have r5 : ((lowerRamificationGroup T K' 0).index : ℚ) *
      Nat.card (lowerRamificationGroup T K' 0) = Nat.card (F.Carrier ≃ₐ[K'] F.Carrier) := by
    exact_mod_cast Subgroup.index_mul_card _
  have hg0 : (Nat.card (lowerRamificationGroup T K 0) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hbh0 : ((lowerRamificationGroup T K' 0).index : ℚ) *
      Nat.card (lowerRamificationGroup T K' 0) ≠ 0 := by
    rw [r5]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  exact induction_term_identity hg0 hbh0 r1 r2 r3 r4 r5

end Main

/-- The published induction family holds at all universe levels. -/
theorem finiteGaloisConductorInduction :
    FiniteGaloisConductorInductionStatement.{uK, uK', uL, uV} :=
  fun _ _ _ T K _ _ _ _ K' _ _ _ _ _ _ _ _ _ _ => finiteGaloisInducedConductor T K K'

end Langlands.Ramification.Padic

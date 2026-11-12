import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Invariant Laurent algebras under finite groups of characters

Let `Λ` be a free abelian group of finite rank `d` and `X` a group identified with
its complex characters by `D`. Let `E` evaluate the group algebra `ℂ[Λ]` faithfully
on `X`. For a finite subgroup `S` of `X`, the `S`-invariant evaluations form a
Laurent algebra in `d` variables, every complex point of it comes from `X`, and
two points of `X` are separated by it exactly when they are not congruent
modulo `S`.
-/

noncomputable section

open AddMonoidAlgebra

namespace Langlands.CuspidalSupport.OrbitTorus

universe u v

section Divisible

/-- Every nonzero integer power map of `ℂˣ` is surjective. -/
theorem complexUnits_zpow_surjective {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun u : ℂˣ => u ^ n) := by
  intro x
  obtain ⟨m, hm⟩ := Int.eq_nat_or_neg n
  have hm0 : 0 < m := by
    rcases hm with rfl | rfl <;> omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) hm0
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hz, zero_pow hm0.ne'])
  have hu : Units.mk0 z hz0 ^ m = x := Units.ext (by simp [hz])
  rcases hm with rfl | rfl
  · exact ⟨Units.mk0 z hz0, by
      change (Units.mk0 z hz0) ^ (m : ℤ) = x
      rw [zpow_natCast, hu]⟩
  · exact ⟨(Units.mk0 z hz0)⁻¹, by
      change ((Units.mk0 z hz0)⁻¹) ^ (-(m : ℤ)) = x
      rw [zpow_neg, zpow_natCast, inv_pow, inv_inv, hu]⟩

/-- Complex characters of a subgroup of an abelian group extend to the whole
group, because `ℂˣ` is divisible. -/
theorem exists_character_extension {Λ : Type u} [CommGroup Λ]
    (L : Submodule ℤ (Additive Λ)) (ψ : L →+ Additive ℂˣ) :
    ∃ χ : Λ →* ℂˣ, ∀ a : L, χ (a : Additive Λ).toMul = (ψ a).toMul := by
  let : DivisibleBy (Additive ℂˣ) ℤ :=
    divisibleByOfSMulRightSurj (Additive ℂˣ) ℤ (fun {n} hn x => by
      obtain ⟨u, hu⟩ := complexUnits_zpow_surjective hn x.toMul
      refine ⟨Additive.ofMul u, ?_⟩
      change n • Additive.ofMul u = x
      rw [← ofMul_zpow]
      exact congrArg Additive.ofMul hu)
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    L.subtype.toAddMonoidHom Subtype.val_injective ψ
  refine ⟨MonoidHom.toAdditive.symm h, fun a => ?_⟩
  change (h (a : Additive Λ)).toMul = (ψ a).toMul
  rw [← hh]
  rfl

end Divisible

variable {Λ : Type u} [CommGroup Λ] {X : Type v} [CommGroup X]
  (D : X →* (Λ →* ℂˣ)) (S : Subgroup X)

/-- The lattice of elements of `Λ` on which every character in `S` is trivial. -/
def annihilatorLattice : Submodule ℤ (Additive Λ) where
  carrier := {a | ∀ s ∈ S, D s a.toMul = 1}
  add_mem' := by
    intro a b ha hb s hs
    simp only [toMul_add, map_mul, ha s hs, hb s hs, mul_one]
  zero_mem' := by
    intro s _
    simp
  smul_mem' := by
    intro n a ha s hs
    simp only [toMul_zsmul, map_zpow, ha s hs, one_zpow]

variable {D S}

theorem mem_annihilatorLattice {a : Additive Λ} :
    a ∈ annihilatorLattice D S ↔ ∀ s ∈ S, D s a.toMul = 1 := Iff.rfl

/-- Multiples by the order of `S` lie in the annihilator lattice. -/
theorem card_smul_mem_annihilatorLattice (a : Additive Λ) :
    ((Nat.card S : ℕ) : ℤ) • a ∈ annihilatorLattice D S := by
  intro s hs
  have hpow : s ^ Nat.card S = 1 := by
    have h1 := congrArg (fun y : S => (y : X)) (pow_card_eq_one' (x := (⟨s, hs⟩ : S)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
  rw [toMul_zsmul, zpow_natCast, map_pow, ← MonoidHom.pow_apply, ← map_pow, hpow, map_one,
    MonoidHom.one_apply]

/-- The annihilator lattice of a finite subgroup has full rank. -/
theorem exists_basis_annihilatorLattice [Finite S] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ (Additive Λ)) :
    Nonempty (Module.Basis (Fin d) ℤ (annihilatorLattice D S)) := by
  obtain ⟨n, bL⟩ := Submodule.basisOfPid b (annihilatorLattice D S)
  have : Module.Finite ℤ (Additive Λ) := Module.Finite.of_basis b
  have : Module.Finite ℤ (annihilatorLattice D S) := Module.Finite.of_basis bL
  have hle : n ≤ d := by
    have := Submodule.finrank_le (annihilatorLattice D S)
    rwa [Module.finrank_eq_card_basis bL, Module.finrank_eq_card_basis b, Fintype.card_fin,
      Fintype.card_fin] at this
  have hge : d ≤ n := by
    have hN : ((Nat.card S : ℕ) : ℤ) ≠ 0 := by
      have : 0 < Nat.card S := Nat.card_pos
      omega
    let f : Additive Λ →ₗ[ℤ] Additive Λ := ((Nat.card S : ℕ) : ℤ) • LinearMap.id
    have hf : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      have hx' : ((Nat.card S : ℕ) : ℤ) • x = 0 := hx
      exact (b.smul_eq_zero.mp hx').resolve_left hN
    let v : Fin d → annihilatorLattice D S := fun i =>
      ⟨((Nat.card S : ℕ) : ℤ) • b i, card_smul_mem_annihilatorLattice (b i)⟩
    have hv : LinearIndependent ℤ v :=
      LinearIndependent.of_comp (annihilatorLattice D S).subtype
        (b.linearIndependent.map' f hf)
    have := hv.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis bL, Fintype.card_fin] at this
  obtain rfl : n = d := le_antisymm hle hge
  exact ⟨bL⟩

/-- Finite duality: if `t` is trivial on the annihilator lattice of a finite
subgroup `S`, then `t ∈ S`. -/
theorem mem_of_forall_annihilator [Finite S] (hD : Function.Injective D) {t : X}
    (ht : ∀ a : Λ, (∀ s ∈ S, D s a = 1) → D t a = 1) : t ∈ S := by
  have : NeZero ((Monoid.exponent S : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  let ev : Λ →* (S →* ℂˣ) := (D.comp S.subtype).flip
  have hev : ∀ (a : Λ) (s : S), ev a s = D s a := fun _ _ => rfl
  have hsurj : Function.Surjective ev := by
    intro φ
    have hmem : φ ∈ (CommGroup.subgroupOrderIsoSubgroupMonoidHom S ℂ
        ((CommGroup.subgroupOrderIsoSubgroupMonoidHom S ℂ).symm
          (OrderDual.toDual ev.range))).ofDual := by
      rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff]
      intro g hg
      rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff] at hg
      have hg1 : g = 1 := by
        apply Subtype.ext
        apply hD
        refine MonoidHom.ext fun a => ?_
        have h1 := hg (ev a) ⟨a, rfl⟩
        rw [hev] at h1
        rw [h1, OneMemClass.coe_one, map_one, MonoidHom.one_apply]
      rw [hg1, map_one]
    rw [OrderIso.apply_symm_apply, OrderDual.ofDual_toDual] at hmem
    exact hmem
  have hker : ev.ker ≤ (D t).ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    refine ht a fun s hs => ?_
    have h1 := DFunLike.congr_fun ha ⟨s, hs⟩
    rwa [hev, MonoidHom.one_apply] at h1
  let τ : (S →* ℂˣ) →* ℂˣ := ev.liftOfSurjective hsurj ⟨D t, hker⟩
  have hτ : ∀ a, τ (ev a) = D t a := fun a =>
    ev.liftOfRightInverse_comp_apply _ _ ⟨D t, hker⟩ a
  let s0 : S := CommGroup.monoidHomMonoidHomEquiv S ℂ τ
  have hs0 : ∀ φ : S →* ℂˣ, φ s0 = τ φ := fun φ =>
    CommGroup.apply_monoidHomMonoidHomEquiv ℂ φ τ
  have hts : t = s0 := by
    apply hD
    refine MonoidHom.ext fun a => ?_
    rw [← hτ, ← hs0, hev]
  rw [hts]
  exact s0.2

variable (D) in
/-- Multiply the coefficient of `a` by `s(a)`: translation by `s` on evaluations. -/
def characterTwist (s : X) :
    AddMonoidAlgebra ℂ (Additive Λ) →ₐ[ℂ] AddMonoidAlgebra ℂ (Additive Λ) :=
  AddMonoidAlgebra.lift ℂ (AddMonoidAlgebra ℂ (Additive Λ)) (Additive Λ)
    { toFun := fun a => single a.toAdd (D s a.toAdd.toMul : ℂ)
      map_one' := by simp [one_def]
      map_mul' := fun a b => by
        rw [single_mul_single, toAdd_mul, toMul_add, map_mul, Units.val_mul] }

theorem characterTwist_single (s : X) (a : Additive Λ) (c : ℂ) :
    characterTwist D s (single a c) = single a (c * (D s a.toMul : ℂ)) := by
  rw [characterTwist, AddMonoidAlgebra.lift_single]
  change c • single a (D s a.toMul : ℂ) = _
  rw [smul_single']

theorem coeff_characterTwist (s : X) (p : AddMonoidAlgebra ℂ (Additive Λ)) (a : Additive Λ) :
    (characterTwist D s p).coeff a = (D s a.toMul : ℂ) * p.coeff a := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply,
      hp, hq, mul_add]
  | single b c =>
    rw [characterTwist_single, coeff_single, coeff_single, Finsupp.single_apply,
      Finsupp.single_apply]
    split_ifs with h
    · rw [h, mul_comm]
    · rw [mul_zero]

variable {E : AddMonoidAlgebra ℂ (Additive Λ) →ₐ[ℂ] (X → ℂ)}

theorem apply_characterTwist
    (hE : ∀ (a : Additive Λ) (c : ℂ) (χ : X), E (single a c) χ = c * (D χ a.toMul : ℂ))
    (s : X) (p : AddMonoidAlgebra ℂ (Additive Λ)) (χ : X) :
    E (characterTwist D s p) χ = E p (χ * s) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | single a c =>
    rw [characterTwist_single, hE, hE, map_mul, MonoidHom.mul_apply, Units.val_mul]
    ring

/-- The invariant Laurent algebra of a finite group of characters. -/
theorem exists_invariant_laurent [Finite S] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ (Additive Λ)) (hD : Function.Bijective D)
    (hE : ∀ (a : Additive Λ) (c : ℂ) (χ : X), E (single a c) χ = c * (D χ a.toMul : ℂ))
    (hEi : Function.Injective E) :
    ∃ Φ : AddMonoidAlgebra ℂ (Fin d → ℤ) →ₐ[ℂ] (X → ℂ),
      Function.Injective Φ ∧
      Set.range Φ = {f | f ∈ E.range ∧ ∀ s ∈ S, ∀ χ, f (χ * s) = f χ} ∧
      (∀ φ : AddMonoidAlgebra ℂ (Fin d → ℤ) →ₐ[ℂ] ℂ, ∃ χ, ∀ p, φ p = Φ p χ) ∧
      ∀ χ χ' : X, (χ⁻¹ * χ' ∈ S ↔
        ∀ f ∈ {f | f ∈ E.range ∧ ∀ s ∈ S, ∀ χ, f (χ * s) = f χ}, f χ = f χ') := by
  obtain ⟨bL⟩ := exists_basis_annihilatorLattice (D := D) (S := S) b
  let L := annihilatorLattice D S
  let μ : (Fin d → ℤ) →+ Additive Λ :=
    (L.subtype.comp bL.equivFun.symm.toLinearMap).toAddMonoidHom
  have hμ : ∀ m, μ m = (bL.equivFun.symm m : Additive Λ) := fun _ => rfl
  have hμL : ∀ m, μ m ∈ L := fun m => (bL.equivFun.symm m).2
  have hμi : Function.Injective μ :=
    Subtype.val_injective.comp bL.equivFun.symm.injective
  have hμs : ∀ a ∈ L, ∃ m, μ m = a := fun a ha =>
    ⟨bL.equivFun ⟨a, ha⟩, by rw [hμ, LinearEquiv.symm_apply_apply]⟩
  let Φ := E.comp (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ μ)
  have hΦ : ∀ m c χ, Φ (single m c) χ = c * (D χ (μ m).toMul : ℂ) := by
    intro m c χ
    change E (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ μ (single m c)) χ = _
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, hE]
  have hinv : ∀ q, ∀ s ∈ S, ∀ χ, Φ q (χ * s) = Φ q χ := by
    intro q s hs χ
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, Pi.add_apply, Pi.add_apply, hp, hq]
    | single m c =>
      rw [hΦ, hΦ, map_mul, MonoidHom.mul_apply, hμL m s hs, mul_one]
  have hevinv : ∀ a ∈ L, ∀ s ∈ S, ∀ ξ, E (single a 1) (ξ * s) = E (single a 1) ξ := by
    intro a ha s hs ξ
    rw [hE, hE, map_mul, MonoidHom.mul_apply, ha s hs, mul_one]
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro p q h
    exact AddMonoidAlgebra.mapDomain_injective hμi (hEi h)
  · ext f
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨⟨AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ μ q, rfl⟩, fun s hs χ => hinv q s hs χ⟩
    · rintro ⟨⟨p, rfl⟩, hf⟩
      have hsupp : ↑p.coeff.support ⊆ Set.range μ := by
        intro a ha
        apply hμs
        intro s hs
        have htw : characterTwist D s p = p :=
          hEi (funext fun χ => (apply_characterTwist hE s p χ).trans (hf s hs χ))
        have hc := congrArg (fun q => q.coeff a) htw
        simp only [coeff_characterTwist] at hc
        have hpa : p.coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
        have h1 : (D s a.toMul : ℂ) = 1 := mul_right_cancel₀ hpa (by rw [hc, one_mul])
        exact Units.val_eq_one.mp h1
      refine ⟨AddMonoidAlgebra.comapDomain μ hμi p, ?_⟩
      change E (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ μ _) = _
      rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_comapDomain hsupp]
      rfl
  · intro φ
    let ψ0 : Multiplicative (Fin d → ℤ) →* ℂˣ :=
      ((φ : AddMonoidAlgebra ℂ (Fin d → ℤ) →* ℂ).comp
        (AddMonoidAlgebra.of ℂ (Fin d → ℤ))).toHomUnits
    let ψ : L →+ Additive ℂˣ :=
      (MonoidHom.toAdditiveRight ψ0).comp bL.equivFun.toLinearMap.toAddMonoidHom
    obtain ⟨χ0, hχ0⟩ := exists_character_extension L ψ
    obtain ⟨χ, hχ⟩ := hD.2 χ0
    refine ⟨χ, fun p => ?_⟩
    have hφ : φ = (Pi.evalAlgHom ℂ (fun _ : X => ℂ) χ).comp Φ := by
      apply AddMonoidAlgebra.algHom_ext
      · intro m
        rw [AlgHom.comp_apply, Pi.evalAlgHom_apply, hΦ, one_mul, hχ, hμ, hχ0]
        change φ (single m 1) = ((ψ0 (Multiplicative.ofAdd
          (bL.equivFun (bL.equivFun.symm m))) : ℂˣ) : ℂ)
        rw [LinearEquiv.apply_symm_apply]
        rfl
      · exact Subsingleton.elim _ _
    rw [hφ]
    rfl
  · intro χ χ'
    constructor
    · rintro h f ⟨_, hf⟩
      have h1 := hf _ h χ
      rw [mul_inv_cancel_left] at h1
      exact h1.symm
    · intro h
      apply mem_of_forall_annihilator hD.1
      intro a ha
      have ha' : Additive.ofMul a ∈ L := ha
      have h1 := h (E (single (Additive.ofMul a) 1))
        ⟨⟨_, rfl⟩, hevinv (Additive.ofMul a) ha'⟩
      rw [hE, hE, one_mul, one_mul] at h1
      have h2 : D χ a = D χ' a := Units.ext h1
      rw [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply]
      change (D χ a)⁻¹ * D χ' a = 1
      rw [h2, inv_mul_cancel]

end Langlands.CuspidalSupport.OrbitTorus

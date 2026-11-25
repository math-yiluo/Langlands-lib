/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement

/-!
# Frobenius elements are conjugate in the Weil group

Let `X₀` be a connected scheme over a finite field `k₀`, `s` a geometric point and
`G = π₁(X₀, s)`. Two Frobenius elements `f₁, f₂` at a point `x` with finite residue field are
conjugate in `G`, since the paths from `x̄` to `s` form a torsor under `G`. They are even conjugate
by an element of the Weil group `W(X₀, s)`
(`AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement.exists_mem_weilGroup_conj`), so the
Frobenius conjugacy class at `x` is a conjugacy class of `W(X₀, s)` (blueprint
`definition-weil-representation--1`).

## Proof

Let `f₂ = c f₁ c⁻¹` with `c ∈ G`, and let `A` be the closure of the powers of `f₁`, which commutes
with `f₁`. Write `e = [κ(x) : k₀]`. It suffices to find `a ∈ A` and `0 ≤ j < e` such that `c a`
acts on the geometric fibres of all constant covers as the `j`-th power of the geometric
Frobenius. On the constant cover of a finite subfield `R` of degree `N`, `c` acts as some power
`Φ ^ m`, `f₁ ^ k` as `Φ ^ (e k)`, and `Φ ^ N` trivially, so `c f₁ ^ k` acts as `Φ ^ j` for
`j = m mod gcd(e, N)` and a suitable `k`, by Bézout. The admissible `j` and `a` then form
directed systems of nonempty closed subsets of compact spaces.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

/-- The morphism of constant covers induced by the `k`-th power of the `q`-power Frobenius of
`A` acts on geometric fibres as the `k`-th power of the arithmetic Frobenius. -/
lemma fiber_map_constantCoverHom_frobeniusAlgHom_pow [Fintype K] (A : FiniteEtaleAlgebra K)
    (k : ℕ) (y : (fiber s).obj (constantCover p A)) :
    (fiber s).map (constantCoverHom p (FiniteField.frobeniusAlgHom K A.1 ^ k)) y =
      ((geometricFrobenius p s A)⁻¹ ^ k) y := by
  have hfrob : FiniteField.frobeniusAlgHom K A.1 = A.frobenius.toAlgHom := by
    ext a
    change a ^ Fintype.card K = A.frobenius a
    rw [FiniteEtaleAlgebra.frobenius_apply, Nat.card_eq_fintype_card]
  induction k generalizing y with
  | zero =>
    change (fiber s).map (constantCoverHom p (AlgHom.id K A.1)) y = y
    rw [← constantCoverMap_eq_constantCoverHom, constantCoverMap_id, CategoryTheory.Functor.map_id]
    rfl
  | succ k ih =>
    rw [pow_succ', show FiniteField.frobeniusAlgHom K A.1 * FiniteField.frobeniusAlgHom K A.1 ^ k =
      (FiniteField.frobeniusAlgHom K A.1).comp (FiniteField.frobeniusAlgHom K A.1 ^ k) from rfl,
      constantCoverHom_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, ih, pow_succ, Equiv.Perm.mul_apply, hfrob]
    rfl

variable (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)]

section Subfield

variable [Algebra K Ω] {p s} (hκ : baseRingHom p s = algebraMap K Ω)
include hκ

/-- Every point of the geometric fibre of the constant cover of a finite intermediate field `R`
is the image of the inclusion point under a power of the geometric Frobenius. -/
lemma exists_eq_geometricFrobenius_zpow_inclusionPoint (R : IntermediateField K Ω)
    [FiniteDimensional K R]
    (z : (fiber s).obj (constantCover p (finiteEtaleAlgebraOfIntermediateField R))) :
    ∃ m : ℤ, z = (geometricFrobenius p s _ ^ m) (inclusionPoint hκ R) := by
  obtain ⟨σ, rfl⟩ := exists_eq_fiber_map_inclusionPoint hκ R z
    (fiberConstantCoverEquiv_mem hκ R z)
  have : Finite R := Module.finite_of_finite K
  let := Fintype.ofFinite K
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow K R).2 σ
  refine ⟨-(n : ℕ), ?_⟩
  rw [← hn]
  change (fiber s).map (constantCoverHom p
    (FiniteField.frobeniusAlgHom K (finiteEtaleAlgebraOfIntermediateField R).1 ^ (n : ℕ))) _ = _
  rw [fiber_map_constantCoverHom_frobeniusAlgHom_pow, zpow_neg, zpow_natCast, inv_pow]

/-- The `N`-th power of the geometric Frobenius fixes the inclusion point of an intermediate field
of degree `N`, hence so do the powers `Φ ^ (N t)`. -/
lemma geometricFrobenius_zpow_mul_finrank_inclusionPoint (R : IntermediateField K Ω)
    [FiniteDimensional K R] (t : ℤ) :
    (geometricFrobenius p s _ ^ ((Module.finrank K R : ℤ) * t)) (inclusionPoint hκ R) =
      inclusionPoint hκ R := by
  have : Finite R := Module.finite_of_finite K
  let := Fintype.ofFinite K
  have h1 : FiniteField.frobeniusAlgHom K (finiteEtaleAlgebraOfIntermediateField R).1 ^
      Module.finrank K R = 1 := by
    rw [← FiniteField.orderOf_frobeniusAlgHom K R]
    exact pow_orderOf_eq_one _
  have h2 : ((geometricFrobenius p s (finiteEtaleAlgebraOfIntermediateField R))⁻¹ ^
      Module.finrank K R) (inclusionPoint hκ R) = inclusionPoint hκ R := by
    rw [← fiber_map_constantCoverHom_frobeniusAlgHom_pow, h1]
    change (fiber s).map (constantCoverHom p (AlgHom.id K _)) _ = _
    rw [← constantCoverMap_eq_constantCoverHom, constantCoverMap_id, CategoryTheory.Functor.map_id]
    rfl
  set P := geometricFrobenius p s (finiteEtaleAlgebraOfIntermediateField R)
  have h3 : P ^ (Module.finrank K R : ℤ) ∈ MulAction.stabilizer (Equiv.Perm _)
      (inclusionPoint hκ R) := by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, zpow_natCast]
    conv_lhs => rw [← h2]
    rw [← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]
  have := (MulAction.stabilizer (Equiv.Perm _) (inclusionPoint hκ R)).zpow_mem h3 t
  rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, ← zpow_mul] at this

end Subfield

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace X₀]
  [IsFundamentalGroup (fiber s) G]

/-- Two Frobenius elements at the same point are conjugate in `π₁(X₀, s)`. -/
lemma IsFrobeniusElement.exists_conj {x : X₀} [Finite (X₀.residueField x)] {f₁ f₂ : G}
    (h₁ : IsFrobeniusElement s G x f₁) (h₂ : IsFrobeniusElement s G x f₂) :
    ∃ c : G, c * f₁ * c⁻¹ = f₂ := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  obtain ⟨c, hc⟩ := (toAut_bijective (fiber s) G).2 (.of (σ₁.symm ≪≫ σ₂))
  have hcact (P : X₀.FiniteEtale) (y : (fiber (residueFieldPoint X₀ x)).obj P) :
      c • σ₁.hom.app P y = σ₂.hom.app P y := by
    rw [← toAut_hom_app_apply, hc]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [← ConcreteCategory.comp_apply (σ₁.hom.app P) (σ₁.inv.app P), σ₁.hom_inv_id_app]
    rfl
  have key (P : X₀.FiniteEtale) (z : (fiber s).obj P) : (c * f₁ * c⁻¹) • z = f₂ • z := by
    obtain ⟨y, rfl⟩ : ∃ y, σ₂.hom.app P y = z :=
      ⟨σ₂.inv.app P z, ConcreteCategory.congr_hom (σ₂.inv_hom_id_app P) z⟩
    rw [hσ₂, mul_smul, mul_smul, ← hcact, inv_smul_smul, hσ₁, hcact]
  refine ⟨c, ?_⟩
  rw [← mul_inv_eq_one]
  apply IsFundamentalGroup.non_trivial (F := fiber s)
  intro P z
  rw [mul_smul, key, smul_inv_smul]

/-- **Frobenius elements are conjugate in the Weil group.** Two Frobenius elements `f₁, f₂` at
the same point `x` are conjugate by an element of the Weil group `W(X₀, s)`. -/
theorem IsFrobeniusElement.exists_mem_weilGroup_conj [GeometricallyConnected p] {x : X₀}
    [Finite (X₀.residueField x)] {f₁ f₂ : G} (h₁ : IsFrobeniusElement s G x f₁)
    (h₂ : IsFrobeniusElement s G x f₂) :
    ∃ (c : G) (n : Multiplicative ℤ), (c, n) ∈ weilGroup p s G ∧ c * f₁ * c⁻¹ = f₂ := by
  open scoped FintypeCatDiscrete in
  have hW₁ := h₁.mem_weilGroup p
  obtain ⟨c₀, hconj⟩ := h₁.exists_conj s G h₂
  have : T2Space G := (toAutHomeo (fiber s) G).isEmbedding.t2Space
  let cl : Set G := closure (Subgroup.zpowers f₁ : Set G)
  have hcomm : ∀ a ∈ cl, a * f₁ = f₁ * a := by
    refine fun a ha ↦ (closure_minimal (s := (Subgroup.zpowers f₁ : Set G))
      (t := {a | a * f₁ = f₁ * a}) ?_ (isClosed_eq (continuous_id.mul continuous_const)
        (continuous_const.mul continuous_id))) ha
    rintro _ ⟨k, rfl⟩
    exact ((Commute.refl f₁).zpow_left k).eq
  have hpow (k : ℤ) : f₁ ^ k ∈ cl := subset_closure ⟨k, rfl⟩
  set e := p.degreeOver x with he_def
  have he : 0 < e := Nat.pos_of_ne_zero (p.degreeOver_ne_zero (X₀.mem_finitePoints.2 inferInstance))
  -- `f₁ ^ k` acts as `Φ ^ (k e)`
  have hf₁ (k : ℤ) (B : FiniteEtaleAlgebra K) (y : (fiber s).obj (constantCover p B)) :
      f₁ ^ k • y = (geometricFrobenius p s B ^ (k * e : ℤ)) y := by
    have := (mem_weilGroup_iff p s G).1 ((weilGroup p s G).zpow_mem hW₁ k) B y
    simpa [mul_comm] using this
  let := (baseRingHom p s).toAlgebra
  have hκ : baseRingHom p s = algebraMap K Ω := rfl
  let ι := {R : IntermediateField K Ω // FiniteDimensional K R}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  let A (R : ι) : FiniteEtaleAlgebra K :=
    haveI := R.2; finiteEtaleAlgebraOfIntermediateField R.1
  let y₀ (R : ι) : (fiber s).obj (constantCover p (A R)) := haveI := R.2; inclusionPoint hκ R.1
  let Φ (R : ι) := geometricFrobenius p s (A R)
  -- monotonicity in the subfield
  have hmono (R R' : ι) (hRR' : R.1 ≤ R'.1) (g : G) (j : ℤ)
      (hg : g • y₀ R' = (Φ R' ^ j) (y₀ R')) : g • y₀ R = (Φ R ^ j) (y₀ R) := by
    have := R.2
    have := R'.2
    exact smul_eq_geometricFrobenius_zpow_of_mem G hκ R'.1 g j hg _ fun a ↦ hRR' (by
      rw [fiberConstantCoverEquiv_inclusionPoint]
      exact a.2)
  -- the admissible exponents for a subfield
  let J (R : ι) : Set (Fin e) := {j | ∃ a ∈ cl, (c₀ * a) • y₀ R = (Φ R ^ (j : ℤ)) (y₀ R)}
  have hJne (R : ι) : (J R).Nonempty := by
    have := R.2
    obtain ⟨m, hm⟩ := exists_eq_geometricFrobenius_zpow_inclusionPoint hκ R.1 (c₀ • y₀ R)
    have hc₀ (z) := smul_eq_geometricFrobenius_zpow_of_mem G hκ R.1 c₀ m hm z
      (fiberConstantCoverEquiv_mem hκ R.1 z)
    set N := Module.finrank K R.1
    set d := Nat.gcd e N
    have hd : 0 < d := Nat.gcd_pos_of_pos_left N he
    have hde : d ≤ e := Nat.le_of_dvd he (Nat.gcd_dvd_left e N)
    set j := m % d
    set t := m / d
    have hj0 : 0 ≤ j := Int.emod_nonneg _ (by exact_mod_cast hd.ne')
    have hjd : j < d := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
    have hbez : (d : ℤ) = e * Nat.gcdA e N + N * Nat.gcdB e N := Nat.gcd_eq_gcd_ab _ _
    have hmt : m = d * t + j := by have := Int.mul_ediv_add_emod m d; linarith
    refine ⟨⟨j.toNat, by omega⟩, f₁ ^ (-(Nat.gcdA e N * t)), hpow _, ?_⟩
    rw [mul_smul, hf₁, hc₀, ← Equiv.Perm.mul_apply, ← zpow_add]
    have hexp : m + -(Nat.gcdA e N * t) * e = (j.toNat : ℤ) + N * (Nat.gcdB e N * t) := by
      rw [Int.toNat_of_nonneg hj0]
      linear_combination hmt + t * hbez
    rw [hexp, zpow_add, Equiv.Perm.mul_apply]
    exact congrArg _ (geometricFrobenius_zpow_mul_finrank_inclusionPoint hκ R.1 _)
  have hJdir : Directed (· ⊇ ·) J := by
    intro R₁ R₂
    have := R₁.2
    have := R₂.2
    refine ⟨⟨R₁.1 ⊔ R₂.1, inferInstance⟩, ?_, ?_⟩ <;> rintro j ⟨a, ha, h⟩ <;>
      exact ⟨a, ha, hmono _ _ (by simp) _ _ h⟩
  have : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  obtain ⟨j₀, hj₀⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed J hJdir
    hJne (fun R ↦ (Set.toFinite _).isCompact) (fun R ↦ isClosed_discrete _)
  simp only [Set.mem_iInter] at hj₀
  -- the admissible elements of `cl` for the exponent `j₀`
  let T (R : ι) : Set G := cl ∩ {a | (c₀ * a) • y₀ R = (Φ R ^ (j₀ : ℤ)) (y₀ R)}
  have hTne (R : ι) : (T R).Nonempty := by
    obtain ⟨a, ha, h⟩ := hj₀ R
    exact ⟨a, ha, h⟩
  have hTcl (R : ι) : IsClosed (T R) :=
    isClosed_closure.inter (isClosed_eq ((continuous_const.mul continuous_id).smul
      continuous_const) continuous_const)
  have hTdir : Directed (· ⊇ ·) T := by
    intro R₁ R₂
    have := R₁.2
    have := R₂.2
    refine ⟨⟨R₁.1 ⊔ R₂.1, inferInstance⟩, ?_, ?_⟩ <;> rintro a ⟨ha, h⟩ <;>
      exact ⟨ha, hmono _ _ (by simp) _ _ h⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hTdir
    hTne (fun R ↦ (hTcl R).isCompact) hTcl
  simp only [Set.mem_iInter] at ha
  have hacl : a ∈ cl := (ha ⟨⊥, inferInstance⟩).1
  refine ⟨c₀ * a, Multiplicative.ofAdd (j₀ : ℤ), (mem_weilGroup_iff p s G).2 fun B y ↦ ?_, ?_⟩
  · obtain ⟨R, _, hR⟩ := exists_forall_mem_intermediateField hκ B
    exact smul_eq_geometricFrobenius_zpow_of_mem G hκ R _ _ (ha ⟨R, inferInstance⟩).2 y (hR y)
  · have : a * f₁ * a⁻¹ = f₁ := by rw [hcomm a hacl, mul_inv_cancel_right]
    calc c₀ * a * f₁ * (c₀ * a)⁻¹ = c₀ * (a * f₁ * a⁻¹) * c₀⁻¹ := by group
      _ = f₂ := by rw [this, hconj]

end AlgebraicGeometry.Scheme.FiniteEtale

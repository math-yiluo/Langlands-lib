/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ResidueFieldTrdeg

/-!
# Transcendence degrees of residue fields of schemes over a field

Let `b : X ⟶ Spec K` be a scheme over a field. On an affine open `V ∋ y`, the transcendence degree
`trdeg κ(y)` (over the residue field `κ(b y) ≅ K`) is `trdeg_K Γ(X, V) ⧸ 𝔭_y`
(`AlgebraicGeometry.Scheme.Hom.trdegAt_eq_trdeg_quotient`). Consequently:

* `AlgebraicGeometry.Scheme.Hom.trdegAt_le_of_specializes`: it decreases along specializations;
* `AlgebraicGeometry.Scheme.Hom.trdegAt_lt_aleph0`: it is finite if `b` is locally of finite type.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The residue field of the spectrum of a field `K` at its point is `K`. -/
lemma bijective_ΓSpecIso_inv_Γevaluation (s : Spec (.of K)) :
    Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation s).hom := by
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  have he (a : Γ(Spec (.of K), ⊤)) :
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation s).hom
        ((Scheme.ΓSpecIso (.of K)).hom a) = (Spec (.of K)).Γevaluation s a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id_assoc]
  obtain ⟨a, c, hc, hac⟩ :=
    (isAffineOpen_top (Spec (.of K))).exists_mul_evaluation_eq s trivial z
  refine ⟨(Scheme.ΓSpecIso (.of K)).hom a / (Scheme.ΓSpecIso (.of K)).hom c, ?_⟩
  rw [map_div₀, he, he, div_eq_iff hc, hac]

variable (b : X ⟶ Spec (.of K))

/-- On an affine open `V ∋ y` of a scheme `b : X ⟶ Spec K` over a field, the transcendence degree
of `κ(y)` is that of the quotient of `Γ(X, V)` by the prime ideal of `y`. -/
lemma Hom.trdegAt_eq_trdeg_quotient {V : X.Opens} (hV : IsAffineOpen V) (y : X) (hy : y ∈ V) :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appLE ⊤ V (by simp)).hom.toAlgebra
    b.trdegAt y = Algebra.trdeg K (Γ(X, V) ⧸ RingHom.ker (X.evaluation V y hy).hom) := by
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appLE ⊤ V (by simp)).hom.toAlgebra
  let ρ := (Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation (b y)
  let : Algebra K ((Spec (.of K)).residueField (b y)) := ρ.hom.toAlgebra
  let : Algebra ((Spec (.of K)).residueField (b y)) (X.residueField y) :=
    (b.residueFieldMap y).hom.toAlgebra
  let : Algebra K (X.residueField y) := (ρ ≫ b.residueFieldMap y).hom.toAlgebra
  have : IsScalarTower K ((Spec (.of K)).residueField (b y)) (X.residueField y) :=
    .of_algebraMap_eq' rfl
  have h1 : b.trdegAt y = Algebra.trdeg K (X.residueField y) :=
    (Algebra.trdeg_eq_of_bijective_algebraMap (bijective_ΓSpecIso_inv_Γevaluation (b y))).symm
  rw [h1]
  have hres (s : Γ(X, b ⁻¹ᵁ ⊤)) :
      X.evaluation V y hy (X.presheaf.map (homOfLE (by simp : V ≤ b ⁻¹ᵁ ⊤)).op s) =
        X.evaluation (b ⁻¹ᵁ ⊤) y trivial s := by
    rw [← germ_residue, ← germ_residue, ← CommRingCat.comp_apply, ← Category.assoc,
      TopCat.Presheaf.germ_res]
  have : (RingHom.ker (X.evaluation V y hy).hom).IsPrime := RingHom.ker_isPrime _
  let φ : Γ(X, V) →ₐ[K] X.residueField y :=
    { (X.evaluation V y hy).hom with
      commutes' r := (hres _).trans (evaluation_naturality_apply b y (V := ⊤) trivial _).symm }
  refine le_antisymm ?_ (trdeg_le_of_injective (Ideal.kerLiftAlg φ)
    (Ideal.kerLiftAlg_injective φ))
  refine Algebra.trdeg_le_of_isAlgebraic_adjoin_range (Ideal.kerLiftAlg φ)
    (Ideal.kerLiftAlg_injective φ) ⟨fun z ↦ ?_⟩
  have hmem (a : Γ(X, V)) : φ a ∈ Algebra.adjoin K (Set.range (Ideal.kerLiftAlg φ)) :=
    Algebra.subset_adjoin ⟨Ideal.Quotient.mk _ a, rfl⟩
  obtain ⟨a, c, hc, hac⟩ := hV.exists_mul_evaluation_eq y hy z
  have hz : z = φ a * (φ c)⁻¹ := by
    rw [← mul_inv_cancel_right₀ hc z]
    exact congrArg (· * (φ c)⁻¹) hac
  rw [hz]
  exact (isAlgebraic_algebraMap (⟨_, hmem a⟩ : Algebra.adjoin K _)).mul
    (isAlgebraic_algebraMap (⟨_, hmem c⟩ : Algebra.adjoin K _)).inv

/-- **The transcendence degree of residue fields decreases along specializations** in a scheme
over a field. -/
theorem Hom.trdegAt_le_of_specializes {x y : X} (h : x ⤳ y) : b.trdegAt y ≤ b.trdegAt x := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxV : x ∈ V := h.mem_open V.isOpen hyV
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appLE ⊤ V (by simp)).hom.toAlgebra
  rw [b.trdegAt_eq_trdeg_quotient hV y hyV, b.trdegAt_eq_trdeg_quotient hV x hxV]
  have hle : RingHom.ker (X.evaluation V x hxV).hom ≤ RingHom.ker (X.evaluation V y hyV).hom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [evaluation_eq_zero_iff_notMem_basicOpen] at ha ⊢
    exact fun hy' ↦ ha (h.mem_open (X.basicOpen a).isOpen hy')
  exact trdeg_le_of_surjective (Ideal.Quotient.factorₐ K hle)
    (Ideal.Quotient.factor_surjective hle)

/-- The residue fields of a scheme locally of finite type over a field have finite transcendence
degree. -/
theorem Hom.trdegAt_lt_aleph0 [LocallyOfFiniteType b] (y : X) :
    b.trdegAt y < Cardinal.aleph0 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appLE ⊤ V (by simp)).hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, V) := by
    have hft : RingHom.FiniteType (b.appLE ⊤ V (by simp)).hom :=
      b.finiteType_appLE (isAffineOpen_top _) hV (by simp)
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  have : (RingHom.ker (X.evaluation V y hyV).hom).IsPrime := RingHom.ker_isPrime _
  rw [b.trdegAt_eq_trdeg_quotient hV y hyV]
  exact trdeg_lt_aleph0_of_finiteType

end AlgebraicGeometry.Scheme

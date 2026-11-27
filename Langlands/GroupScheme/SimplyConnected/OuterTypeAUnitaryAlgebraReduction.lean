import Langlands.LinearAlgebra.UnitaryTwistedChart
import Langlands.GroupScheme.Examples.UnitaryAlgebraGroupScheme
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitReduction
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraPresentationStatement

/-!
# Outer type A groups as special unitary groups from the Tits cocycle

Let `G` be a simply connected absolutely almost-simple group of outer type `A_n` over a field
`K`. The Tits cocycle (`SpecialLinearTitsCocycleStatement`) gives a finite Galois extension
`M/K`, a local isomorphism `E` from `SL_(n+1)` to `G` over `Spec M`, and discrepancy matrices
`x σ`, inner for the automorphisms fixing the star field `F ⊆ M` and outer for the others.
They form a twisted unitary cocycle (`UnitaryTwistedChart.Cocycle`), whose descended algebra
`B` is central simple over `F` with a unitary involution `τ`. This module composes the charts
`SU(B, τ)(S) ≅ SL_(n+1)(S)` at the cover points with `E`, shows that the resulting local
isomorphisms are Galois invariant, descends them to an isomorphism `SU(B, τ) ≅ G`, and proves
`OuterTypeAUnitaryAlgebraPresentationStatement` from `SpecialLinearTitsCocycleStatement`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.OuterTypeAUnitaryAlgebra

open SpecialLinearTitsCocycle Matrix Langlands.LinearAlgebra.UnitaryTwistedChart
open OuterTypeAUnitarySplit

section Coefficients

variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- The coefficient map of a cover point, as a `K`-algebra map into the relative global
sections. -/
def coefficientHom {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    M →ₐ[K] ((algΓ (CommRingCat.of K)).obj Z).unop where
  toRingHom := coefficients a
  commutes' := OuterTypeAHermitian.coefficients_algebraMap a

/-- The coefficient maps are natural in the test scheme. -/
theorem coefficientHom_naturality {Z W : Over (Spec (CommRingCat.of K))} (t : W ⟶ Z)
    (a : Z ⟶ cover K M) :
    coefficientHom (t ≫ a) =
      ((algΓ (CommRingCat.of K)).map t).unop.hom.comp (coefficientHom a) := by
  ext l
  exact congrArg (fun f => f l) (coefficients_naturality t a)

/-- Translating a cover point by `σ` composes its coefficient map with `σ`. -/
theorem coefficientHom_coverAut {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (σ : M ≃ₐ[K] M) :
    coefficientHom (a ≫ coverAut K M σ) = (coefficientHom a).comp σ.toAlgHom := by
  ext l
  exact congrArg (fun f => f l) (coefficients_coverAut a σ)

end Coefficients

section Local

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  {F : IntermediateField K M} [Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F]
  [Normal K F] {n : ℕ} (c : Langlands.LinearAlgebra.UnitaryTwistedChart.Cocycle F (Fin (n + 1)))
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- The local isomorphism from `SU(B, τ)` to `G` at a cover point: the chart along the
coefficient map, followed by `E`. -/
def localEquiv {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    (Z ⟶ (UnitaryAlgebra.groupScheme F c.involution).X) ≃* (Z ⟶ G.X) :=
  (UnitaryAlgebra.pointsEquiv F c.involution Z).trans ((c.suChart (coefficientHom a)).trans
    ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm.trans (E.toFun a)))

/-- The value of the local isomorphism. -/
theorem localEquiv_apply {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (y : Z ⟶ (UnitaryAlgebra.groupScheme F c.involution).X) :
    localEquiv c E a y = E.toFun a
      ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm
        (c.suChart (coefficientHom a) (UnitaryAlgebra.pointsEquiv F c.involution Z y))) := rfl

/-- The local isomorphisms are natural in the test scheme. -/
theorem localEquiv_naturality {Z W : Over (Spec (CommRingCat.of K))} (t : W ⟶ Z)
    (a : Z ⟶ cover K M) (y : Z ⟶ (UnitaryAlgebra.groupScheme F c.involution).X) :
    localEquiv c E (t ≫ a) (t ≫ y) = t ≫ localEquiv c E a y := by
  rw [localEquiv_apply, localEquiv_apply, ← E.naturality]
  congr 1
  apply (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W).injective
  rw [MulEquiv.apply_symm_apply, SpecialLinear.pointsEquiv_naturality,
    MulEquiv.apply_symm_apply]
  apply Subtype.ext
  have h := c.suChart_naturality (coefficientHom a) ((algΓ (CommRingCat.of K)).map t).unop.hom
    (UnitaryAlgebra.pointsEquiv F c.involution Z y)
  rw [UnitaryAlgebra.pointsEquiv_naturality]
  have e := coefficientHom_naturality t a
  refine (congrArg (fun ψ => ((c.suChart ψ (CentralSimple.UnitaryPoints.specialUnitaryMap (↥F)
    c.involution ((algΓ (CommRingCat.of K)).map t).unop.hom
      (UnitaryAlgebra.pointsEquiv F c.involution Z y)) :
        SpecialLinearGroup (Fin (n + 1)) ((algΓ (CommRingCat.of K)).obj W).unop) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ((algΓ (CommRingCat.of K)).obj W).unop)) e).trans ?_
  exact h

/-- Cancelling a conjugation inside a conjugation. -/
theorem conj_conj_cancel {R : Type*} [CommRing R] (X : GeneralLinearGroup (Fin (n + 1)) R)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        ((((X⁻¹ : GeneralLinearGroup (Fin (n + 1)) R)) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
          g * (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) *
        ((X⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      g := by
  simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- The inverse of a conjugated inverse transpose. -/
theorem inv_transpose_conj {R : Type*} [CommRing R] (Y : GeneralLinearGroup (Fin (n + 1)) R)
    (g h : SpecialLinearGroup (Fin (n + 1)) R)
    (hh : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (((Y⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        ((g⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R))ᵀ) :
    ((h⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)ᵀ =
      ((Y⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  have hg : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
      ((g⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 :=
    congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) R =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) (mul_inv_cancel g)
  have h1 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
      (((Y⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R))ᵀ = 1 := by
    rw [hh]
    exact Cocycle.transpose_conj_mul Y hg
  have h2 : ((h⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
      (h : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 :=
    congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) R =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) (inv_mul_cancel h)
  have h3 : ((h⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (((Y⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R))ᵀ := by
    rw [← Matrix.one_mul (((Y⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) * (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R))ᵀ, ← h2, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [h3, Matrix.transpose_transpose]

/-- The inner discrepancy undoes a conjugation. -/
theorem inner_cancel {R : Type*} [CommRing R] (X : GeneralLinearGroup (Fin (n + 1)) R)
    (g h : SpecialLinearGroup (Fin (n + 1)) R)
    (hh : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      ((X⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) :
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        ((X⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  rw [hh]
  exact conj_conj_cancel X _

/-- The outer discrepancy undoes a conjugated inverse transpose. -/
theorem outer_cancel {R : Type*} [CommRing R] (X : GeneralLinearGroup (Fin (n + 1)) R)
    (g h : SpecialLinearGroup (Fin (n + 1)) R)
    (hh : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (((X⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        ((g⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R))ᵀ) :
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        ((h⁻¹ : SpecialLinearGroup (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R).transpose *
        ((X⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  rw [inv_transpose_conj X g h hh]
  exact conj_conj_cancel X _

/-- Under the inner and outer discrepancy formulas, the local isomorphisms are invariant under
every Galois translation of the cover point. -/
theorem localEquiv_coverAut
    (hin : ∀ σ ∈ F.fixingSubgroup, IsInnerMatrixFormula E σ (c.x σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, IsOuterMatrixFormula E σ (c.x σ))
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) (σ : M ≃ₐ[K] M)
    (y : Z ⟶ (UnitaryAlgebra.groupScheme F c.involution).X) :
    localEquiv c E (a ≫ coverAut K M σ) y = localEquiv c E a y := by
  rw [localEquiv_apply, localEquiv_apply]
  have e := coefficientHom_coverAut a σ
  have hs : c.suChart (coefficientHom (a ≫ coverAut K M σ))
      (UnitaryAlgebra.pointsEquiv F c.involution Z y) =
      c.suChart ((coefficientHom a).comp σ.toAlgHom)
        (UnitaryAlgebra.pointsEquiv F c.involution Z y) :=
    congrArg (fun ψ => c.suChart ψ (UnitaryAlgebra.pointsEquiv F c.involution Z y)) e
  rw [hs]
  apply OuterTypeAHermitian.toFun_coverAut_of_discrepancy E σ a
  apply Subtype.ext
  by_cases hσ : σ ∈ F.fixingSubgroup
  · have hh := c.suChart_comp_of_mem (coefficientHom a) hσ
      (UnitaryAlgebra.pointsEquiv F c.involution Z y)
    rw [hin σ hσ Z a]
    exact inner_cancel (c.cocycleMatrix (coefficientHom a) σ) _ _ hh
  · have hh := c.suChart_comp_of_not_mem (coefficientHom a) hσ
      (UnitaryAlgebra.pointsEquiv F c.involution Z y)
    rw [hout σ hσ Z a]
    exact outer_cancel (c.cocycleMatrix (coefficientHom a) σ) _ _ hh

/-- The local isomorphisms from `SU(B, τ)` to `G` over the cover. -/
def localIso : LocalGroupIso (UnitaryAlgebra.groupScheme F c.involution) G (cover K M) where
  toFun a := localEquiv c E a
  naturality t a y := localEquiv_naturality c E t a y

/-- The local isomorphisms are invariant under every Galois automorphism of the cover. -/
theorem localIso_isInvariant
    (hin : ∀ σ ∈ F.fixingSubgroup, IsInnerMatrixFormula E σ (c.x σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, IsOuterMatrixFormula E σ (c.x σ)) (σ : M ≃ₐ[K] M) :
    (localIso c E).IsInvariant (algebraBaseMap K M) (galoisBaseMap K M σ)
      (galoisBaseMap_over K M σ) :=
  fun a y => localEquiv_coverAut c E hin hout a σ y

/-- The isomorphism `SU(B, τ) ≅ G` descended from the local isomorphisms. -/
def descendedIso [IsAffineHom G.X.hom]
    (hin : ∀ σ ∈ F.fixingSubgroup, IsInnerMatrixFormula E σ (c.x σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, IsOuterMatrixFormula E σ (c.x σ)) :
    UnitaryAlgebra.groupScheme F c.involution ≅ G :=
  LocalGroupIso.galoisDescendIso (localIso c E) (localIso_isInvariant c E hin hout)

end Local

section Discrepancy

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- An inner representative gives the matrix form of the inner discrepancy formula. -/
theorem isInnerMatrixFormula_of_hasInnerDiscrepancy {σ : M ≃ₐ[K] M}
    {X : GeneralLinearGroup (Fin (n + 1)) M} (hX : HasInnerDiscrepancy E σ X) :
    IsInnerMatrixFormula E σ X := by
  intro Z a g
  have h := congrArg Units.val (hX Z a g)
  rw [Units.val_mul, Units.val_mul, ← map_inv] at h
  exact h

end Discrepancy

/-- The Tits cocycle presentation of type-A groups implies that every outer form of type A is
the special unitary group of a central simple algebra with a unitary involution over its star
field. -/
theorem outerTypeAUnitaryAlgebraPresentation_of_specialLinearTitsCocycle
    (hcoc : SpecialLinearTitsCocycleStatement.{u}) :
    OuterTypeAUnitaryAlgebraPresentationStatement.{u} := by
  classical
  intro K _ G _ _ d n hsc has ⟨e, hA⟩ ⟨σ₀, v₀, hmove⟩
  have hnot : ¬ d.StarIsTrivial := fun h => hmove (h σ₀ v₀)
  have hstar := d.starImagePair_of_A e hA hnot
  have hn : 2 ≤ n := hstar.two_le
  have := hstar.isQuadraticExtension
  have := hstar.isGalois
  obtain ⟨M, _, _, _, _, ι₀, E, x, χ, hcoc1, -, -⟩ := hcoc K G d n e hsc has hA
  have hshape : HasStarDiscrepancy E d ι₀ x := fun σ τ hτ =>
    ⟨fun h => hasInnerDiscrepancy_of_matrix E fun Z a g => (hcoc1 σ τ hτ Z a g).1 h,
      fun h => hasOuterDiscrepancy_of_matrix E fun Z a g => (hcoc1 σ τ hτ Z a g).2 h⟩
  have hle := hshape.starField_le_cover E d hn
  let f := starFieldToCover d ι₀ hle
  let F : IntermediateField K M := f.fieldRange
  have : Algebra.IsQuadraticExtension K F :=
    ⟨(f.equivFieldRange.toLinearEquiv.finrank_eq).symm.trans hstar.finrank_starField⟩
  have : Algebra.IsSeparable K F := Algebra.isSeparable_tower_bot_of_isSeparable K F M
  have hfix (σ : M ≃ₐ[K] M) : σ ∈ F.fixingSubgroup ↔ ∀ z : d.starField, σ (f z) = f z := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h z
      exact h (f z) ⟨z, rfl⟩
    · rintro h y ⟨z, rfl⟩
      exact h z
  have hI : ∀ σ ∈ F.fixingSubgroup, HasInnerDiscrepancy E σ (x σ) := fun σ hσ =>
    hshape.inner_of_fixes_starField d ι₀ hle E σ ((hfix σ).mp hσ)
  have hO : ∀ σ ∉ F.fixingSubgroup, HasOuterDiscrepancy E σ (x σ) := by
    intro σ hσ
    apply hshape.outer_of_not_fixes_starField d ι₀ hle E σ
    by_contra! h
    exact hσ ((hfix σ).mpr h)
  have hH : F.fixingSubgroup.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  have hcyc := isTwistedProjectiveCocycle_of_discrepancy E hH hI hO
  obtain ⟨r, hr⟩ : ∃ r, r ∉ F.fixingSubgroup := by
    by_contra h
    push Not at h
    have htop : F.fixingSubgroup = ⊤ := eq_top_iff.mpr fun r _ => h r
    rw [htop, Subgroup.index_top] at hH
    exact absurd hH (by norm_num)
  let c : Langlands.LinearAlgebra.UnitaryTwistedChart.Cocycle F (Fin (n + 1)) :=
    ⟨x, hH, hcyc.1, hcyc.2, r, hr⟩
  have hIm : ∀ σ ∈ F.fixingSubgroup, IsInnerMatrixFormula E σ (c.x σ) := fun σ hσ =>
    isInnerMatrixFormula_of_hasInnerDiscrepancy E (hI σ hσ)
  have hOm : ∀ σ ∉ F.fixingSubgroup, IsOuterMatrixFormula E σ (c.x σ) := fun σ hσ =>
    isOuterMatrixFormula_of_hasOuterDiscrepancy E (hO σ hσ)
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, c.Alg, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    c.involution, c.involution_algebraMap, ?_,
    ⟨UnitaryAlgebra.Presentation.ofIso F c.involution (descendedIso c E hIm hOm)⟩⟩
  rw [c.finrank_alg, Fintype.card_fin, sq]

end Langlands.GroupScheme.OuterTypeAUnitaryAlgebra

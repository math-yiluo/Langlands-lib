import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitTorus
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianTorus
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleProof

/-! # Outer type-A Hermitian coordinates from unitary splitting -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (e : d.Vertex ≃ Fin n)
  (hstar : d.StarImagePair e Fin.revPerm)
  (ι₀ : M →ₐ[K] SeparableClosure K) (hle : d.starField ≤ ι₀.fieldRange)
  [IsGalois K M] [FiniteDimensional K M]
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))
  {x : (M ≃ₐ[K] M) → GeneralLinearGroup (Fin (n + 1)) M}

/-- Unitary splitting permits an inner correction preserving all split-torus
coordinates, with no distinguished-position hypothesis. -/
theorem HasStarDiscrepancy.exists_hermitian_coordinates_of_unitarySplitting
    (hK : UnitaryInvolutionSplitting K)
    (hshape : HasStarDiscrepancy E d ι₀ x)
    (χ : Fin (n + 1) → characterLattice d.splitTorus)
    (hdiag : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
      (s : Z ⟶ d.splitTorus.X),
      (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((E.toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        Matrix.diagonal fun i =>
          ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
            Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)))
    :
    haveI := hstar.isQuadraticExtension
    ∃ (P : GeneralLinearGroup (Fin (n + 1)) M)
      (J : HermitianMatrix.Form (SU3Root.fieldInvolution K d.starField) (Fin (n + 1))),
      HasTrivialDiscrepancy (coordinateChange E P)
        (starFieldToCover d ι₀ hle).fieldRange.fixingSubgroup ∧
      (∀ σ : M ≃ₐ[K] M, (∃ z : d.starField,
          σ (starFieldToCover d ι₀ hle z) ≠ starFieldToCover d ι₀ hle z) →
        HasOuterDiscrepancy (coordinateChange E P) σ
          (GeneralLinearGroup.map (starFieldToCover d ι₀ hle).toRingHom J.gram⁻¹)) ∧
      ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
        (s : Z ⟶ d.splitTorus.X),
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
          (((coordinateChange E P).toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          Matrix.diagonal fun i =>
            ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
              Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  classical
  have := hstar.isQuadraticExtension
  have := hstar.isGalois
  let f := starFieldToCover d ι₀ hle
  let H := f.fieldRange.fixingSubgroup
  let F : IntermediateField K M := f.fieldRange
  have : Algebra.IsQuadraticExtension K F :=
    ⟨(f.equivFieldRange.toLinearEquiv.finrank_eq).symm.trans hstar.finrank_starField⟩
  have hfix (σ : M ≃ₐ[K] M) : σ ∈ H ↔ ∀ z : d.starField, σ (f z) = f z := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h z
      exact h (f z) ⟨z, rfl⟩
    · rintro h y ⟨z, rfl⟩
      exact h z
  have hI : ∀ σ ∈ H, HasInnerDiscrepancy E σ (x σ) := fun σ hσ =>
    hshape.inner_of_fixes_starField d ι₀ hle E σ ((hfix σ).mp hσ)
  have hO : ∀ σ ∉ H, HasOuterDiscrepancy E σ (x σ) := by
    intro σ hσ
    apply hshape.outer_of_not_fixes_starField d ι₀ hle E σ
    by_contra! h
    exact hσ ((hfix σ).mpr h)
  have hH : H.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  have hcyc := isTwistedProjectiveCocycle_of_discrepancy E hH hI hO
  obtain ⟨P₀, hP₀⟩ :=
    Langlands.LinearAlgebra.UnitaryTwistedDescent.exists_conj_eq_scalar hK F hcyc.1 hcyc.2
  obtain ⟨P, htriv, hcoords⟩ :=
    exists_torus_preserving_correction_of_scalar E d.splitTorus d.splitInclusion χ hdiag H
      d.maximalSplit.1.1 hI P₀ hP₀
  obtain ⟨σ, hσ⟩ := exists_starFieldToCover_conjugation d e hstar ι₀ hle
  have hnontrivial : ∃ z : d.starField, (SU3Root.fieldInvolution K d.starField).bar z ≠ z := by
    by_contra! h
    apply SU3Root.conjugation_ne_one K d.starField
    exact AlgEquiv.ext h
  have hmoves : ∃ z : d.starField, σ (f z) ≠ f z := by
    obtain ⟨z, hz⟩ := hnontrivial
    refine ⟨z, ?_⟩
    rw [hσ]
    exact fun h => hz (f.injective h)
  have houter := (hshape.outer_of_not_fixes_starField d ι₀ hle E σ hmoves).coordinateChange E P
  obtain ⟨J, hJ⟩ := exists_hermitian_outer_representative (coordinateChange E P) f
    (SU3Root.fieldInvolution K d.starField) hnontrivial htriv σ hσ _ houter
  refine ⟨P, J, htriv, ?_, ?_⟩
  · intro τ hτ
    exact hJ τ (starFieldToCover_conjugation_of_not_fixed d e hstar ι₀ hle τ hτ)
  · exact hcoords

end Langlands.GroupScheme.SpecialLinearTitsCocycle

namespace Langlands.GroupScheme

open Matrix SpecialLinearTitsCocycle

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- An actual all-test Hermitian presentation retaining the original split-torus
weights and every simple-root restriction. -/
structure TypeAHermitianTorusCoordinates (L : Type u) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) where
  form : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin (n + 1))
  presentation : HermitianMatrix.SchemeModel.Presentation K L form G
  weights : Fin (n + 1) → characterLattice d.splitTorus
  torus_coordinates : ∀ (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ d.splitTorus.X),
    ((presentation.pointsEquiv T (s ≫ d.splitInclusion.hom.hom)).1 :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
      Matrix.diagonal fun i =>
        (show SpecialLinear.WeilRoot.tensorAlgebra K L T from
          Algebra.TensorProduct.includeRight (R := K) (A := L)
            (B := SpecialLinear.WeilRoot.sectionAlgebra K T)
            (show SpecialLinear.WeilRoot.sectionAlgebra K T from
              ((Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom (weights i)).hom.hom) :
                Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))))
  root_coordinates : ∀ i : Fin n,
    d.rootRestriction (e.symm i).val = weights i.castSucc - weights i.succ

/-- Unitary splitting constructs the full Hermitian torus presentation on the
actual star field without any distinguished-position hypothesis. -/
theorem TitsIndexData.nonempty_hermitianTorusCoordinates_of_unitarySplitting
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hstar : d.StarImagePair e Fin.revPerm) (hK : UnitaryInvolutionSplitting K)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) :
    haveI := hstar.isQuadraticExtension
    haveI := hstar.isGalois
    Nonempty (TypeAHermitianTorusCoordinates d.starField d e) := by
  classical
  obtain ⟨M, hMF, hMA, hMD, hMG, ι₀, E, x, χ, hformula, hdiag, hroot⟩ :=
    specialLinearTitsCocycle K G d n e hsc ha hcart
  let := hMF
  let := hMA
  let := hMD
  let := hMG
  have hshape : HasStarDiscrepancy E d ι₀ x := fun σ τ hτ =>
    ⟨fun h => OuterTypeAUnitarySplit.hasInnerDiscrepancy_of_matrix E
      fun Z a g => (hformula σ τ hτ Z a g).1 h,
      fun h => OuterTypeAUnitarySplit.hasOuterDiscrepancy_of_matrix E
      fun Z a g => (hformula σ τ hτ Z a g).2 h⟩
  have hle := hshape.starField_le_cover E d hstar.two_le
  let := hstar.isQuadraticExtension
  let := hstar.isGalois
  obtain ⟨P, J, htriv, hout, hcoords⟩ :=
    hshape.exists_hermitian_coordinates_of_unitarySplitting d e hstar ι₀ hle E hK χ hdiag
  let f := starFieldToCover d ι₀ hle
  let : Algebra d.starField M := f.toRingHom.toAlgebra
  let : IsScalarTower K d.starField M :=
    IsScalarTower.of_algebraMap_eq (fun k => (f.commutes k).symm)
  have hf : algebraMap d.starField M = f.toRingHom := rfl
  have hin : OuterTypeAHermitian.InnerTrivial d.starField (coordinateChange E P) := by
    intro σ hσ Z a g
    let σH : f.fieldRange.fixingSubgroup :=
      ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (by
        intro y hy
        obtain ⟨z, rfl⟩ := hy
        exact hσ z)⟩
    exact htriv σH Z a g
  have ho : OuterTypeAHermitian.OuterHermitian d.starField J (coordinateChange E P) := by
    intro σ hσ Z a g
    have h := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) =>
      (z : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) (hout σ hσ Z a g)
    simpa only [hf, f, Units.val_mul, map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Langlands.LinearAlgebra.SpecialLinearInverseTranspose.inverseTranspose,
      MonoidHom.coe_mk, OneHom.coe_mk, Matrix.SpecialLinearGroup.coe_transpose] using h
  obtain ⟨ρ, hρinj, hρrange, hρnat, hρtorus⟩ :=
    OuterTypeAHermitian.exists_hermitianPresentation (L := d.starField) (H := J)
      (E := coordinateChange E P) (incl := d.splitInclusion.hom.hom)
      (ch := fun i => (CommGroupScheme.groupHom (χ i)).hom.hom) hin ho hcoords
  let p := HermitianMatrix.SchemeModel.Presentation.ofMatrixPoints K d.starField J G
    ρ hρinj hρrange hρnat
  exact ⟨{
    form := J
    presentation := p
    weights := χ
    torus_coordinates := hρtorus
    root_coordinates := hroot }⟩

/-- Choose the established presentation, retaining the actual star field. -/
noncomputable def TitsIndexData.hermitianTorusCoordinatesOfUnitarySplitting
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hstar : d.StarImagePair e Fin.revPerm) (hK : UnitaryInvolutionSplitting K)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) :
    haveI := hstar.isQuadraticExtension
    haveI := hstar.isGalois
    TypeAHermitianTorusCoordinates d.starField d e :=
  Classical.choice
    (d.nonempty_hermitianTorusCoordinates_of_unitarySplitting e hstar hK hsc ha hcart)

end Langlands.GroupScheme

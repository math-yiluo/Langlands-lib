import Langlands.Global.AdelicProjectiveModels
import Langlands.AlgebraicGeometry.PointTopology.AffineLineOrigin
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs

/-! # Actual affine charts in projective scheme-point spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual homogeneous localization ring of a standard coordinate chart. -/
abbrev projectiveChartAlgebra (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :=
  HomogeneousLocalization.Away
    (Langlands.AlgebraicGeometry.projectiveSpaceGrading R n) (MvPolynomial.X j)

private instance (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    Algebra R (projectiveChartAlgebra R n j) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway R n j

/-- The standard polynomial affine chart as an actual relative scheme morphism. -/
def projectiveAffineChart (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    ringTest R (MvPolynomial {i : Fin (n + 1) // i ≠ j} R) ⟶ projectivePointScheme R n :=
  ringTestMap R
    (show MvPolynomial {i : Fin (n + 1) // i ≠ j} R ≃ₐ[R] projectiveChartAlgebra R n j from
      P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv
        (S := R) n j).symm.toAlgHom ≫
    Over.homMk ((Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover R n).openCover.f j)
      (Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover_comp_toSpec R n j)

instance projectiveAffineChart_isOpenImmersion
    (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    IsOpenImmersion (projectiveAffineChart R n j).left := by
  let e : MvPolynomial {i : Fin (n + 1) // i ≠ j} R ≃ₐ[R] projectiveChartAlgebra R n j :=
    P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv
      (S := R) n j
  let : IsIso (CommRingCat.ofHom e.symm.toRingHom) := by
    change IsIso e.symm.toRingEquiv.toCommRingCatIso.hom
    infer_instance
  let : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  let hSpec : IsOpenImmersion (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  let hChart : IsOpenImmersion
      ((Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover R n).openCover.f j) :=
    Langlands.AlgebraicGeometry.ProjectiveSpace.isOpenImmersion_affineOpenCover_f R n j
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    (Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover R n).openCover.f j)
  exact @IsOpenImmersion.comp _ _ _ _ _ hSpec hChart

private def lineChartVariableEquiv : Unit ≃ {i : Fin 2 // i ≠ 0} where
  toFun _ := ⟨1, by decide⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hi := i.property
    have hb := i.val.isLt
    have hn : i.val.val ≠ 0 := by
      intro h
      exact hi (Fin.ext h)
    change 1 = i.val.val
    omega

/-- The standard affine line inside projective one-space, with coordinate [1:a]. -/
def projectiveLineAffineInclusion (R : Type u) [CommRing R] :
    ringTest R (MvPolynomial Unit R) ⟶ projectivePointScheme R 1 :=
  ringTestMap R (MvPolynomial.renameEquiv R lineChartVariableEquiv).symm.toAlgHom ≫
    projectiveAffineChart R 1 0

instance projectiveLineAffineInclusion_isOpenImmersion (R : Type u) [CommRing R] :
    IsOpenImmersion (projectiveLineAffineInclusion R).left := by
  let e := MvPolynomial.renameEquiv R lineChartVariableEquiv
  let : IsIso (CommRingCat.ofHom e.symm.toRingHom) := by
    change IsIso e.symm.toRingEquiv.toCommRingCatIso.hom
    infer_instance
  let : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  let hSpec : IsOpenImmersion (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  let hChart : IsOpenImmersion (projectiveAffineChart R 1 0).left :=
    projectiveAffineChart_isOpenImmersion R 1 0
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    (projectiveAffineChart R 1 0).left)
  exact @IsOpenImmersion.comp _ _ _ _ _ hSpec hChart

/-- The actual point of projective one-space represented by [1:a]. -/
def projectiveLineAffinePoint (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) : RingPoint R (projectivePointScheme R 1) A :=
  (affineLinePointEquiv R A).symm a ≫ projectiveLineAffineInclusion R

theorem projectiveLineAffinePoint_injective (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] :
    Function.Injective (projectiveLineAffinePoint R A) := by
  intro a b h
  apply (affineLinePointEquiv R A).symm.injective
  apply RingPoint.ext
  apply (cancel_mono (projectiveLineAffineInclusion R).left).mp
  exact congrArg (fun p : RingPoint R (projectivePointScheme R 1) A => p.left) h

/-- The standard affine coordinate commutes with every actual coefficient map. -/
theorem projectiveLineAffinePoint_changeRing (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (a : A) :
    (projectiveLineAffinePoint R A a).changeRing f =
      projectiveLineAffinePoint R B (f a) := by
  change ringTestMap R f ≫
    (ringTestMap R (MvPolynomial.aeval (fun _ : Unit => a)) ≫ projectiveLineAffineInclusion R) =
    ringTestMap R (MvPolynomial.aeval (fun _ : Unit => f a)) ≫ projectiveLineAffineInclusion R
  rw [← Category.assoc, ← ringTestMap_comp]
  congr 1
  apply congrArg (ringTestMap R)
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  simp

/-- Over a local topological coefficient ring, the standard affine coordinate
is an open embedding into the independent projective point topology. -/
theorem isOpenEmbedding_projectiveLineAffinePoint (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLocalRing A] [IsOpenUnits A] :
    @IsOpenEmbedding A (RingPoint R (projectivePointScheme R 1) A) inferInstance
      (schemePointTopology R (projectivePointScheme R 1) A)
      (projectiveLineAffinePoint R A) := by
  have he : @IsHomeomorph (RingPoint R (ringTest R (MvPolynomial Unit R)) A) A
      (schemePointTopology R (ringTest R (MvPolynomial Unit R)) A)
      inferInstance (affineLinePointEquiv R A) := by
    rw [schemePointTopology_eq_affine]
    exact (affineLinePointHomeomorph R A).isHomeomorph
  let := schemePointTopology R (ringTest R (MvPolynomial Unit R)) A
  let := schemePointTopology R (projectivePointScheme R 1) A
  let h : RingPoint R (ringTest R (MvPolynomial Unit R)) A ≃ₜ A :=
    { toEquiv := affineLinePointEquiv R A
      continuous_toFun := he.continuous
      continuous_invFun := (affineLinePointEquiv R A).continuous_symm_iff.2 he.isOpenMap }
  exact (isOpenEmbedding_schemePointMap R A (projectiveLineAffineInclusion R)).comp
    h.symm.isOpenEmbedding

end Langlands.Global

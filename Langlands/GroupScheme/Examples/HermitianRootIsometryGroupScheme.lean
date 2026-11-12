import Langlands.GroupScheme.Examples.HermitianRootIsometryTransport
import Langlands.GroupScheme.Examples.HermitianRootModelIdentification

/-! # Gram-isometry transport of the actual Hermitian group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]

/-- Including the quadratic field in actual tensor coefficients respects conjugation. -/
theorem tensorInclusion_bar (T : Over (Spec (CommRingCat.of k))) (a : L) :
    algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)
        ((fieldInvolution k L).bar a) =
      (SU3Root.SchemeModel.coefficientInvolution k L T).bar
        (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T) a) := by
  change conjugation k L a ⊗ₜ[k] (1 : SpecialLinear.WeilRoot.sectionAlgebra k T) =
    QuasiSplitUnitary.scalarConjugation _ (conjugation k L) (a ⊗ₜ[k] 1)
  rw [QuasiSplitUnitary.scalarConjugation_tmul]

/-- Extend an actual change-of-basis matrix to each test scheme's tensor coefficients. -/
def tensorIsometryMatrix (P : Matrix.GeneralLinearGroup (Index Middle) L)
    (T : Over (Spec (CommRingCat.of k))) :
    Matrix.GeneralLinearGroup (Index Middle)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T) :=
  Matrix.GeneralLinearGroup.map
    (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)) P

omit [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- The extended change-of-basis matrix is natural under every test restriction. -/
theorem tensorIsometryMatrix_map (P : Matrix.GeneralLinearGroup (Index Middle) L)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    Matrix.GeneralLinearGroup.map (SpecialLinear.WeilRoot.tensorMap k L a)
        (tensorIsometryMatrix k L P T) = tensorIsometryMatrix k L P T' := by
  apply Units.ext
  ext i j
  change QuasiSplitUnitary.tensorCoefficientMap
    ((algΓ (CommRingCat.of k)).map a).unop.hom
    ((P : Matrix (Index Middle) (Index Middle) L) i j ⊗ₜ[k] 1) =
      (P : Matrix (Index Middle) (Index Middle) L) i j ⊗ₜ[k] 1
  rw [QuasiSplitUnitary.tensorCoefficientMap_tmul, map_one]

variable (H J : DiagonalForm (fieldInvolution k L) Middle)
  (P : Matrix.GeneralLinearGroup (Index Middle) L)
  (hP : conjugateTranspose (fieldInvolution k L)
      (P : Matrix (Index Middle) (Index Middle) L) * gram J *
        (P : Matrix (Index Middle) (Index Middle) L) = gram H)

include hP in
/-- A field-valued Gram congruence extends to the actual tensor forms. -/
theorem tensorGramCongruence (T : Over (Spec (CommRingCat.of k))) :
    conjugateTranspose (SU3Root.SchemeModel.coefficientInvolution k L T)
        (tensorIsometryMatrix k L P T :
          Matrix (Index Middle) (Index Middle)
            (SpecialLinear.WeilRoot.tensorAlgebra k L T)) *
      gram (tensorForm k L J T) *
        (tensorIsometryMatrix k L P T :
          Matrix (Index Middle) (Index Middle)
            (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
      gram (tensorForm k L H T) :=
  gramCongruence_map
    (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T))
    (tensorInclusion_bar k L T) (fun _ => rfl) (fun _ => rfl) P hP

/-- Actual determinant-one isometries of the two tensor forms are equivalent. -/
def tensorIsometryEquiv (T : Over (Spec (CommRingCat.of k))) :
    specialUnitarySubgroup (tensorForm k L H T) ≃*
      specialUnitarySubgroup (tensorForm k L J T) :=
  specialUnitaryIsometryEquiv (tensorIsometryMatrix k L P T)
    (tensorGramCongruence k L H J P hP T)

/-- The tensor isometry equivalences commute with all actual test restrictions. -/
theorem tensorIsometryEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (g : specialUnitarySubgroup (tensorForm k L H T)) :
    specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a)
        (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_weight k L J a)
        (tensorIsometryEquiv k L H J P hP T g) =
      tensorIsometryEquiv k L H J P hP T'
        (specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a)
          (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_weight k L H a) g) := by
  simpa only [tensorIsometryEquiv, tensorIsometryMatrix_map] using
    specialUnitaryIsometryEquiv_map (SpecialLinear.WeilRoot.tensorMap k L a)
      (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_weight k L H a)
      (tensorMap_weight k L J a) (tensorIsometryMatrix k L P T)
      (tensorGramCongruence k L H J P hP T) g

variable (wH : Middle → Lˣ) (hwH : ∀ i, (wH i : L) = H.weight i)

/-- Points of the source model have the transported actual target matrices. -/
def isometryPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L H wH hwH).X) ≃*
      specialUnitarySubgroup (tensorForm k L J T) :=
  (pointsEquiv k L H wH hwH T).trans (tensorIsometryEquiv k L H J P hP T)

/-- Applying the transported point comparison is the indicated matrix equivalence. -/
theorem isometryPointsEquiv_apply (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme k L H wH hwH).X) :
    isometryPointsEquiv k L H J P hP wH hwH T x =
      tensorIsometryEquiv k L H J P hP T (pointsEquiv k L H wH hwH T x) := rfl

/-- Transported model points satisfy the actual target matrix naturality. -/
theorem isometryPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme k L H wH hwH).X) :
    ((isometryPointsEquiv k L H J P hP wH hwH T' (a ≫ x)).1 :
      Matrix (Index Middle) (Index Middle)
        (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      ((isometryPointsEquiv k L H J P hP wH hwH T x).1 :
        Matrix (Index Middle) (Index Middle)
          (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
            (SpecialLinear.WeilRoot.tensorMap k L a) := by
  have hn := tensorIsometryEquiv_naturality k L H J P hP a
    (pointsEquiv k L H wH hwH T x)
  rw [← pointsEquiv_map k L H wH hwH a x] at hn
  exact congrArg
    (fun g : specialUnitarySubgroup (tensorForm k L J T') =>
      (g.1 : Matrix (Index Middle) (Index Middle)
        (SpecialLinear.WeilRoot.tensorAlgebra k L T'))) hn.symm

variable (wJ : Middle → Lˣ) (hwJ : ∀ i, (wJ i : L) = J.weight i)

/-- A supplied actual Gram isometry induces an isomorphism of the Hermitian models. -/
def isometryIso : groupScheme k L H wH hwH ≅ groupScheme k L J wJ hwJ :=
  isoOfMatrixPoints k L J wJ hwJ
    (isometryPointsEquiv k L H J P hP wH hwH)
    (isometryPointsEquiv_naturality k L H J P hP wH hwH)

end Langlands.GroupScheme.HermitianRoot.SchemeModel

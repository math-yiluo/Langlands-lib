import Langlands.Automorphic.OperatorDeterminantSliceHaar
import Langlands.Global.AdelicGroupPolish

/-!
# Instances for the matrix Haar measure

The matrix Haar measure `matrixHaarMeasure F n` on `AdelicGL F n` is right invariant (the
actual adelic general linear group is unimodular, `haar_isMulRightInvariant`), and
`AdelicGL F n` is second countable, both transported from the group-scheme points through the
adelic homeomorphism.
-/

noncomputable section

universe uF

open MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance haarInstIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance haarInstSmooth : _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

theorem secondCountableTopology_adelicGL : SecondCountableTopology (AdelicGL F n) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).toHomeomorph.symm.secondCountableTopology

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

theorem matrixHaarMeasure_isMulRightInvariant :
    (matrixHaarMeasure F n).IsMulRightInvariant := by
  have := haar_isMulRightInvariant F n
  constructor
  intro g
  set e := GeneralLinearGroupPoints.adelicHomeomorph F n
  have he : Measurable (fun y => e y) := e.continuous.measurable
  have hfun : (fun x : AdelicGL F n => x * g) ∘ (fun y => e y) =
      (fun y => e y) ∘ (fun y => y * e.symm g) := by
    funext y
    simp [map_mul]
  rw [matrixHaarMeasure, Measure.map_map (measurable_mul_const g) he, hfun,
    ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

omit [BorelSpace (AdelicGL F n)] in
theorem sFinite_matrixHaarMeasure : SFinite (matrixHaarMeasure F n) := by
  unfold matrixHaarMeasure
  infer_instance

end Langlands.Automorphic.OperatorDeterminantSlice

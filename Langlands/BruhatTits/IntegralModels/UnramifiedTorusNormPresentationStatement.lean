import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.AbelianScheme.Kernel

/-! # A torus norm presentation for the connected integral-point bound -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- The norm-sequence input to KP Corollary B.8.7, over the maximal
unramified extension. There is a surjection from an affine torus with torus
full kernel whose maximal bounded subgroup maps into the prescribed
norm-defined Iwahori subgroup. The intended witness is `Res_{L/K}(T_L)`
with its norm, but the conclusion retains only the properties needed by the
connected integral-point argument. -/
def UnramifiedTorusNormPresentationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left]
    (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
    [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L],
    IsSplitTorus (baseChanged (inertiaFixedField F) L T.toGrp) →
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
      (_ : IsAffine S.X.left),
      IsTorus S.toGrp ∧
        ∃ q : S.toGrp ⟶ T.toGrp,
          Surjective q.hom.hom.left ∧ IsTorus (kernel q) ∧
            (characterValuationKernel (fixedFieldValuation F) S.toGrp).map
                (rationalPoints.map q) ≤
              torusNormIwahori (inertiaFixedField F) L
                (intermediateValuation F L) T

end Langlands.BruhatTits.IntegralModels

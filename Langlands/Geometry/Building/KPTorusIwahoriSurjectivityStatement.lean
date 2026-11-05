import Langlands.Geometry.Building.KPZeroSubgroups

/-! # A derived formulation of KP Lemma 2.5.20(1) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Derived formulation of KP Lemma 2.5.20(1): a morphism of `K`-tori, split over `L`, that is surjective on
cocharacters over `L` maps `T₂(K)^0` onto `T₃(K)^0`. -/
def TorusIwahoriSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T₂ T₃ : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    [IsAffine T₂.X.left] [IsAffine T₃.X.left] (f : T₂ ⟶ T₃)
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L],
    IsSplitTorus (GaloisPointComparison.baseChanged (UnramifiedClosure F) L T₂.toGrp) →
    IsSplitTorus (GaloisPointComparison.baseChanged (UnramifiedClosure F) L T₃.toGrp) →
    Function.Surjective
      (fun ν : cocharacterLattice ((CommGroupScheme.baseChange
          (GaloisPointComparison.baseMap (UnramifiedClosure F) L)).obj T₂) =>
        ν ≫ (CommGroupScheme.baseChange
          (GaloisPointComparison.baseMap (UnramifiedClosure F) L)).map f) →
    (torusNormIwahori (UnramifiedClosure F) L (intermediateValuation F L) T₂).map
        (rationalPoints.map (CommGroupScheme.groupHom f)) =
      torusNormIwahori (UnramifiedClosure F) L (intermediateValuation F L) T₃

end Langlands.Geometry.Building

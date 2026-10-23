import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.PullbackTensorStatement

/-! # Tensor products of locally free rank-one module sheaves -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- A local trivialization on `V` gives a trivialization of the pullback to any smaller open. -/
def pullbackTrivializationOfLE {U V : X.Opens} (h : U ≤ V) (M : X.Modules)
    (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE h) V.ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE h)).mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ e) ≪≫
          pullbackUnitIso (X.homOfLE h)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

include preservation in
/-- Local rank one is closed under the actual sheaf tensor, assuming its canonical
pullback comparison is invertible. -/
lemma IsLocallyFreeRankOne.tensor {M N : X.Modules}
    (hM : IsLocallyFreeRankOne M) (hN : IsLocallyFreeRankOne N) :
    IsLocallyFreeRankOne (tensorObj M N) := by
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN x
  let W := U ⊓ V
  let := preservation W.ι
  refine ⟨W, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorIsoPullback W.ι).app (tensorObj M N) ≪≫
    (asIso (pullbackTensorComparison W.ι)).app (M, N) ≪≫
      (tensorFunctor W.toScheme).mapIso
        ((pullbackTrivializationOfLE inf_le_left M eM).prod
          (pullbackTrivializationOfLE inf_le_right N eN)) ≪≫
            tensorLeftUnitor (structureSheaf W.toScheme)

namespace LineBundle

/-- Tensor product of actual locally free rank-one module sheaves. -/
def tensor (L M : LineBundle X) : LineBundle X :=
  ⟨tensorObj L.obj M.obj, L.property.tensor preservation M.property⟩

/-- The tensor bifunctor on line bundles. -/
def tensorFunctor (X : Scheme.{u}) : LineBundle X × LineBundle X ⥤ LineBundle X :=
  ObjectProperty.lift IsLocallyFreeRankOne
    ((forget X).prod (forget X) ⋙ Langlands.Scheme.Modules.tensorFunctor X)
    (fun LM => LM.1.property.tensor preservation LM.2.property)

/-- The lifted tensor bifunctor has the stated underlying tensor object. -/
lemma tensorFunctor_obj (L M : LineBundle X) :
    (tensorFunctor preservation X).obj (L, M) = tensor preservation L M := rfl

/-- Forgetting the rank-one property recovers exactly the sheaf tensor bifunctor. -/
def tensorForgetIso (X : Scheme.{u}) :
    tensorFunctor preservation X ⋙ forget X ≅
      (forget X).prod (forget X) ⋙ Langlands.Scheme.Modules.tensorFunctor X :=
  Iso.refl _

end LineBundle

end Langlands.AlgebraicGeometry.Picard

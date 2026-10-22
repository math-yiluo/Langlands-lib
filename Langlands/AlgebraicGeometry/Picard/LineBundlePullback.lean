import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

/-! # Pullback of locally free rank-one sheaves -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {X Y Z : Scheme.{u}}

/-- Restricting a pulled-back sheaf agrees with pulling back its restriction. -/
def restrictPullbackIso (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
        ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
          (Scheme.Modules.pullback (f ∣_ U)).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

/-- Pullback preserves the local rank-one condition. -/
lemma IsLocallyFreeRankOne.pullback {M : Y.Modules}
    (hM : IsLocallyFreeRankOne M) (f : X ⟶ Y) :
    IsLocallyFreeRankOne ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM (f x)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨?_⟩⟩
  exact restrictPullbackIso f U M ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
      Langlands.Scheme.Modules.pullbackUnitIso (f ∣_ U)

namespace LineBundle

/-- Pullback on actual locally free rank-one sheaves and their morphisms. -/
def pullback (f : X ⟶ Y) : LineBundle Y ⥤ LineBundle X :=
  ObjectProperty.lift IsLocallyFreeRankOne
    (forget Y ⋙ Scheme.Modules.pullback f) (fun L ↦ L.property.pullback f)

/-- The underlying module of the line-bundle pullback is the usual pullback. -/
def pullbackForgetIso (f : X ⟶ Y) :
    pullback f ⋙ forget X ≅ forget Y ⋙ Scheme.Modules.pullback f :=
  Iso.refl _

/-- Pulling back by the identity is naturally isomorphic to the identity. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (LineBundle X) :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _ ((Scheme.Modules.pullbackId X).app L.obj))
    (fun h ↦ by
      apply ObjectProperty.hom_ext
      exact (Scheme.Modules.pullbackId X).hom.naturality h.hom)

/-- Successive pullbacks agree with pullback by the composite. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _ ((Scheme.Modules.pullbackComp f g).app L.obj))
    (fun h ↦ by
      apply ObjectProperty.hom_ext
      exact (Scheme.Modules.pullbackComp f g).hom.naturality h.hom)

/-- Pullback carries the trivial line bundle to the trivial line bundle. -/
def pullbackTrivialIso (f : X ⟶ Y) : (pullback f).obj (trivial Y) ≅ trivial X :=
  ObjectProperty.isoMk _ (Langlands.Scheme.Modules.pullbackUnitIso f)

end LineBundle

end Langlands.AlgebraicGeometry.Picard

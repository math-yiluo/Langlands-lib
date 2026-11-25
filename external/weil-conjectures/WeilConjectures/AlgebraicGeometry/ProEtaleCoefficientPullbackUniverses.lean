/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage

/-! # Constant-coefficient pullback in an independent coefficient universe

Source: Stacks Project, Tags 09A5, 00VC and 03D2
(auxiliary; not a blueprint node).

The small model enlarges only Hom sizes. The module pullback is Mathlib's sheafified
module Kan extension along the constant-section ring map, hence the tensor-formula
inverse image along its adjoint coefficient map.
-/

@[expose] public section

set_option autoImplicit false

universe t r

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The same small pro-etale site in a universe containing the coefficient ring.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
abbrev coefficientProEtaleSiteModel (X : Scheme.{t}) := AsSmall.{max r (t + 1)} X.ProEt

/-- The topology transported to the coefficient-sized model.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientProEtaleModelTopology (X : Scheme.{t}) :=
  (AsSmall.down : coefficientProEtaleSiteModel.{t, r} X ⥤ X.ProEt).inducedTopology
    (ProEt.topology X)

/-- Base change transported to these models.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientProEtaleModelBaseChange {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientProEtaleSiteModel.{t, r} Y ⥤ coefficientProEtaleSiteModel.{t, r} X :=
  AsSmall.down ⋙ proEtaleBaseChange f ⋙ AsSmall.up

/-- The equivalence to the coefficient-sized model preserves covering sieves.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
instance coefficientProEtaleModelUp_isContinuous (X : Scheme.{t}) :
    (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{t, r} X).IsContinuous
      (ProEt.topology X) (coefficientProEtaleModelTopology.{t, r} X) :=
  inferInstanceAs ((AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)).functor.IsContinuous
    (ProEt.topology X)
      ((AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X)))

/-- Continuity of transported base change.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
instance coefficientProEtaleModelBaseChange_isContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (coefficientProEtaleModelBaseChange.{t, r} f).IsContinuous
      (coefficientProEtaleModelTopology.{t, r} Y)
      (coefficientProEtaleModelTopology.{t, r} X) :=
  haveI := Functor.isContinuous_comp (proEtaleBaseChange f) AsSmall.up
    (ProEt.topology Y) (ProEt.topology X) (coefficientProEtaleModelTopology.{t, r} X)
  Functor.isContinuous_comp AsSmall.down (proEtaleBaseChange f ⋙ AsSmall.up)
    (coefficientProEtaleModelTopology.{t, r} Y) (ProEt.topology Y)
    (coefficientProEtaleModelTopology.{t, r} X)

/-- The constant-section map A_Y → f_* A_X. It is the extension by sheafification
of the map sending a coefficient to its constant section.
Source: Stacks Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable def coefficientProEtaleDirectRingMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max r (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A) :=
  ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv _ _).symm
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))

/-- The ring morphism on the coefficient-sized models, obtained by precomposition
from the canonical constant-section map.
Source: Stacks Tags 0H7J and 03D2 (auxiliary; not a blueprint node). -/
noncomputable def coefficientProEtaleModelRingMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    ((AsSmall.down : coefficientProEtaleSiteModel.{t, r} Y ⥤ Y.ProEt).sheafPushforwardContinuous
       RingCat.{max r (t + 1)} (coefficientProEtaleModelTopology Y)
        (ProEt.topology Y)).obj
          ((sheafCompose _ (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A)) ⟶
    ((coefficientProEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{max r (t + 1)}
      (coefficientProEtaleModelTopology Y) (coefficientProEtaleModelTopology X)).obj
        (((AsSmall.down :
          coefficientProEtaleSiteModel.{t, r} X ⥤ X.ProEt).sheafPushforwardContinuous
            RingCat.{max r (t + 1)} (coefficientProEtaleModelTopology X)
            (ProEt.topology X)).obj
              ((sheafCompose _ (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
                ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A))) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (Functor.whiskerRight (coefficientProEtaleDirectRingMap f A).hom
      (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)}))⟩

/-- Constant-coefficient module direct image through the constant-section map.
Source: Stacks Tag 03D1 (auxiliary; not a blueprint node). -/
noncomputable def coefficientProEtaleModuleDirectImage {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :=
  SheafOfModules.pushforward.{max r (t + 1)} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := (sheafCompose _
      (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A))
    (R := (sheafCompose _
      (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A))
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap f A).hom
      (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The module Kan extension and sheafification supply the left adjoint in the
independent coefficient universe.
Source: Stacks Tags 00VC and 03D2 (auxiliary; not a blueprint node).
Proof: transport modules to the coefficient-sized models. There the ring map is
coefficientProEtaleModelRingMap. Presheaf module pullback exists by the free-Yoneda
presentation, and module sheafification gives its sheaf pullback adjunction. Transport
that adjunction back along the two equivalences of module sheaf categories. Its right
adjoint is the displayed sectionwise pushforward with action through ρ_A^f. -/
@[instance]
theorem coefficientProEtaleModuleDirectImage_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    (coefficientProEtaleModuleDirectImage f A).IsRightAdjoint := by
  let rings (Z : Scheme.{t}) : Sheaf (ProEt.topology Z) RingCat.{max r (t + 1)} :=
    (sheafCompose _ (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
      ((constantSheaf (ProEt.topology Z) CommRingCat.{max r (t + 1)}).obj A)
  have upContinuous (Z : Scheme.{t}) :
      (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := Z.ProEt)).functor.IsContinuous
        (ProEt.topology Z) (coefficientProEtaleModelTopology.{t, r} Z) :=
    coefficientProEtaleModelUp_isContinuous Z
  have downContinuous (Z : Scheme.{t}) :
      (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := Z.ProEt)).inverse.IsContinuous
        (coefficientProEtaleModelTopology.{t, r} Z) (ProEt.topology Z) := by
    change (AsSmall.down : coefficientProEtaleSiteModel.{t, r} Z ⥤ Z.ProEt).IsContinuous
      (coefficientProEtaleModelTopology.{t, r} Z) (ProEt.topology Z)
    infer_instance
  let e (Z : Scheme.{t}) :=
    SheafOfModules.pushforwardPushforwardEquivalence.{max r (t + 1)}
      (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := Z.ProEt))
      (S := rings Z) (R := ((AsSmall.down :
        coefficientProEtaleSiteModel.{t, r} Z ⥤ Z.ProEt).sheafPushforwardContinuous
          RingCat.{max r (t + 1)} (coefficientProEtaleModelTopology Z)
            (ProEt.topology Z)).obj (rings Z)) (𝟙 _) (𝟙 _)
      (by ext : 2; exact (rings Z).obj.map_id _)
      (by ext : 2; exact (rings Z).obj.map_id _)
  let smallPush := SheafOfModules.pushforward.{max r (t + 1)}
    (coefficientProEtaleModelRingMap f A)
  have : smallPush.IsRightAdjoint := by
    dsimp [smallPush]
    infer_instance
  have hx : (e X).inverse.IsRightAdjoint := (e X).isRightAdjoint_inverse
  have hy : (e Y).functor.IsRightAdjoint := (e Y).isRightAdjoint_functor
  apply Functor.isRightAdjoint_of_iso
    (F := (e X).inverse ⋙ smallPush ⋙ (e Y).functor)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) ?_)) ?_
  · intro U V g
    ext x
    rfl
  · intro M N g
    ext U x
    rfl

/-- The canonical module inverse image, defined by the usual pullback adjunction.
Its Kan-extension construction is f⁻¹(-) ⊗_(f⁻¹ A_Y) A_X. The adjunction unit
fixes its canonical generator map, so no arbitrary map is supplied.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def coefficientProEtaleModulePullback {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :=
  (coefficientProEtaleModuleDirectImage f A).leftAdjoint

/-- The defining pullback/direct-image adjunction and its normalized unit.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def coefficientProEtaleModuleAdjunction {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    coefficientProEtaleModulePullback f A ⊣ coefficientProEtaleModuleDirectImage f A :=
  Adjunction.ofIsRightAdjoint _

end AlgebraicGeometry.Scheme

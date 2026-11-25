/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes

/-!
# Sections of the integral localization sequence

The constant section one restricts to one, and its image in the closed term of the
integral localization sequence vanishes on the open complement, as soon as the open term
represents sections over the open with the inclusion corresponding to one.

## References

* Stacks Project, Tags 03AJ and 0A45
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The constant section one is compatible with restriction. -/
lemma torsorExtensionOne_map (T : Scheme.{u}) {U V : T.Etaleᵒᵖ} (f : U ⟶ V) :
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.map f (torsorExtensionOne T U.unop) =
      torsorExtensionOne T V.unop :=
  (ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality f)
      ⟨1⟩).symm

/-- If the open term of the localization sequence represents sections over the open, with
the inclusion corresponding to one, then the image of one in the closed term vanishes on
the open. -/
lemma principalTorsorLocalization_g_one {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (e : ∀ G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1},
      ((principalTorsorLocalization i W h).X₁ ⟶ G) ≃+ G.obj.obj (op (Scheme.Etale.mk W.ι)))
    (he : ∀ (A B : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : A ⟶ B)
      (v : (principalTorsorLocalization i W h).X₁ ⟶ A),
      e B (v ≫ f) = f.hom.app (op (Scheme.Etale.mk W.ι)) (e A v))
    (hone : e _ (principalTorsorLocalization i W h).f =
      torsorExtensionOne T (Scheme.Etale.mk W.ι)) :
    (principalTorsorLocalization i W h).g.hom.app (op (Scheme.Etale.mk W.ι))
      (torsorExtensionOne T (Scheme.Etale.mk W.ι)) = 0 := by
  rw [← hone, ← he, (principalTorsorLocalization i W h).zero, map_zero]

/-- Under the hypotheses of `principalTorsorLocalization_g_one`, the image of one under any
map out of the closed term restricts to zero on the open. -/
lemma principalTorsorLocalization_g_comp_restrict {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (hg : (principalTorsorLocalization i W h).g.hom.app (op (Scheme.Etale.mk W.ι))
      (torsorExtensionOne T (Scheme.Etale.mk W.ι)) = 0)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (b : (principalTorsorLocalization i W h).X₃ ⟶ F) :
    F.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op
      (((principalTorsorLocalization i W h).g ≫ b).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))) = 0 := by
  have hn := ConcreteCategory.congr_hom
    (((principalTorsorLocalization i W h).g ≫ b).hom.naturality
    ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op)
    (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))
  simp only [ConcreteCategory.comp_apply] at hn
  rw [← hn]
  erw [torsorExtensionOne_map T]
  simp [hg]

/-- The integral localization sequence is short exact. -/
lemma principalTorsorLocalization_shortExact {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    (principalTorsorLocalization i W h).ShortExact :=
  shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) h

/-- Maps out of the integral constant sheaf are global sections. -/
noncomputable def integralSectionEquiv (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ F) ≃+
        F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

lemma integralSectionEquiv_apply (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ F) :
    integralSectionEquiv T F a = a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) := by
  dsimp only [integralSectionEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [constantSheafAdj_homEquiv_apply]
  rfl

/-- A map out of the integral constant sheaf sends one to the restriction of its value on
the global section one. -/
lemma integral_hom_app_one (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ F) (V : T.Etale) :
    φ.hom.app (op V) (torsorExtensionOne T V) =
      F.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from V).op
        (φ.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))) := by
  have hn := ConcreteCategory.congr_hom
    (φ.hom.naturality ((MorphismProperty.Over.mkIdTerminal @Etale T).from V).op)
    (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))
  simp only [ConcreteCategory.comp_apply] at hn
  rw [← hn]
  erw [torsorExtensionOne_map T]

end AlgebraicGeometry.Etale

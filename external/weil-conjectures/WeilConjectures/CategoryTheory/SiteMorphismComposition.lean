/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of morphisms of sites

Source: Stacks Project, Lemma 03CB and Definition 03CC
(blueprint: lem-weil-pbc-site-morphism-composition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The unit equation determines the comparison isomorphism componentwise. -/
private theorem leftAdjointUniq_existsUnique
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R) :
    ∃! e : L ≅ L', ∀ X, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X := by
  refine ⟨a.leftAdjointUniq b, fun X ↦ a.unit_leftAdjointUniq_hom_app b X, ?_⟩
  intro e he
  apply Iso.ext
  ext X
  apply (a.homEquiv X (L'.obj X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (he X).trans (a.unit_leftAdjointUniq_hom_app b X).symm

-- The original existential continuity binder is used only through instance synthesis.
set_option linter.unusedVariables false in
/-- Source: Stacks Project, Lemma 03CB and Definition 03CC
(blueprint: lem-weil-pbc-site-morphism-composition).

The precoverages encode the sites of 00VH, and the covering and pullback hypotheses
are the two conditions of 00WV. The `IsContinuous` instances are their consequences
by `siteContinuous_pushforward_isSheaf`; they only make the sheaf functors typeable.
`sheafPullback` here is the left-Kan-extension followed by sheafification construction,
not the arbitrarily chosen left adjoint. Both coefficients use the same construction.

Proof:
1. Apply each covering condition successively. Compose the two pullback comparison
   isomorphisms. This proves Stacks continuity of the composite. Precomposition
   agrees objectwise and on restriction maps, hence agrees as a functor, for sets
   and abelian groups (lem-weil-pbc-site-continuous-pushforward-sheaf and
   situation-conventions).
2. Compose the adjunctions of
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction using
   def-weil-pbc-composite-adjunction. The composite right adjoint is the functor in
   step 1. Uniqueness of left adjoints gives the unique isomorphism compatible with
   units (situation-conventions). Its component equation below
   is exactly the composite unit: eta_v followed by v^s applied to eta_u at v_s F.
3. Finite limits and colimits are preserved by successive application of the two
   preservation hypotheses. Transport along the isomorphism of step 2. This is
   exactness of the composite left adjoint. Together with step 1 it defines the
   composite morphism of sites; its direct and inverse images are the functors in
   steps 1 and 2, as in 03CC. -/
theorem siteMorphism_composition
    {C₁ C₂ C₃ : Type u} [SmallCategory C₁] [SmallCategory C₂] [SmallCategory C₃]
    (J₁ : Precoverage C₁) (J₂ : Precoverage C₂) (J₃ : Precoverage C₃)
    [J₁.HasIsos] [J₁.IsStableUnderComposition] [J₁.IsStableUnderBaseChange] [J₁.HasPullbacks]
    [J₂.HasIsos] [J₂.IsStableUnderComposition] [J₂.IsStableUnderBaseChange] [J₂.HasPullbacks]
    [J₃.HasIsos] [J₃.IsStableUnderComposition] [J₃.IsStableUnderBaseChange] [J₃.HasPullbacks]
    (U : C₂ ⥤ C₁) (V : C₃ ⥤ C₂)
    (hUcover : ∀ (X : C₂) (R : Presieve X), R ∈ J₂ X → R.map U ∈ J₁ (U.obj X))
    (hUpullback : ∀ (X Y Z : C₂) (R : Presieve X), R ∈ J₂ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (hVcover : ∀ (X : C₃) (R : Presieve X), R ∈ J₃ X → R.map V ∈ J₂ (V.obj X))
    (hVpullback : ∀ (X Y Z : C₃) (R : Presieve X), R ∈ J₃ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) V)
    [U.IsContinuous J₂.toGrothendieck J₁.toGrothendieck]
    [V.IsContinuous J₃.toGrothendieck J₂.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback U (Type u)
      J₂.toGrothendieck J₁.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback U (Type u)
      J₂.toGrothendieck J₁.toGrothendieck)]
    [PreservesFiniteLimits (sheafPullback V (Type u)
      J₃.toGrothendieck J₂.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback V (Type u)
      J₃.toGrothendieck J₂.toGrothendieck)] :
    (∀ (X : C₃) (R : Presieve X), R ∈ J₃ X →
      R.map (V ⋙ U) ∈ J₁ ((V ⋙ U).obj X)) ∧
    (∀ (X Y Z : C₃) (R : Presieve X), R ∈ J₃ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) (V ⋙ U)) ∧
    ∃ (hVU : (V ⋙ U).IsContinuous J₃.toGrothendieck J₁.toGrothendieck),
      ((V ⋙ U).sheafPushforwardContinuous (Type u) J₃.toGrothendieck J₁.toGrothendieck =
        U.sheafPushforwardContinuous (Type u) J₂.toGrothendieck J₁.toGrothendieck ⋙
          V.sheafPushforwardContinuous (Type u) J₃.toGrothendieck J₂.toGrothendieck) ∧
      (∃! e : sheafPullback (V ⋙ U) (Type u) J₃.toGrothendieck J₁.toGrothendieck ≅
          sheafPullback V (Type u) J₃.toGrothendieck J₂.toGrothendieck ⋙
            sheafPullback U (Type u) J₂.toGrothendieck J₁.toGrothendieck,
        ∀ F : Sheaf J₃.toGrothendieck (Type u),
          (sheafAdjunctionContinuous (V ⋙ U) (Type u)
            J₃.toGrothendieck J₁.toGrothendieck).unit.app F ≫
            ((V ⋙ U).sheafPushforwardContinuous (Type u)
              J₃.toGrothendieck J₁.toGrothendieck).map (e.hom.app F) =
          (sheafAdjunctionContinuous V (Type u)
            J₃.toGrothendieck J₂.toGrothendieck).unit.app F ≫
            (V.sheafPushforwardContinuous (Type u) J₃.toGrothendieck J₂.toGrothendieck).map
              ((sheafAdjunctionContinuous U (Type u)
                J₂.toGrothendieck J₁.toGrothendieck).unit.app
                ((sheafPullback V (Type u) J₃.toGrothendieck J₂.toGrothendieck).obj F))) ∧
      ((V ⋙ U).sheafPushforwardContinuous AddCommGrpCat.{u} J₃.toGrothendieck J₁.toGrothendieck =
        U.sheafPushforwardContinuous AddCommGrpCat.{u} J₂.toGrothendieck J₁.toGrothendieck ⋙
          V.sheafPushforwardContinuous AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck) ∧
      (∃! e : sheafPullback (V ⋙ U) AddCommGrpCat.{u} J₃.toGrothendieck J₁.toGrothendieck ≅
          sheafPullback V AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck ⋙
            sheafPullback U AddCommGrpCat.{u} J₂.toGrothendieck J₁.toGrothendieck,
        ∀ F : Sheaf J₃.toGrothendieck AddCommGrpCat.{u},
          (sheafAdjunctionContinuous (V ⋙ U) AddCommGrpCat.{u}
            J₃.toGrothendieck J₁.toGrothendieck).unit.app F ≫
            ((V ⋙ U).sheafPushforwardContinuous AddCommGrpCat.{u}
              J₃.toGrothendieck J₁.toGrothendieck).map (e.hom.app F) =
          (sheafAdjunctionContinuous V AddCommGrpCat.{u}
            J₃.toGrothendieck J₂.toGrothendieck).unit.app F ≫
            (V.sheafPushforwardContinuous AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck).map
              ((sheafAdjunctionContinuous U AddCommGrpCat.{u}
                J₂.toGrothendieck J₁.toGrothendieck).unit.app
                ((sheafPullback V AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck).obj F))) ∧
      Nonempty (PreservesFiniteLimits (sheafPullback (V ⋙ U) (Type u)
        J₃.toGrothendieck J₁.toGrothendieck)) ∧
      Nonempty (PreservesFiniteColimits (sheafPullback (V ⋙ U) (Type u)
        J₃.toGrothendieck J₁.toGrothendieck)) := by
  have hcover : ∀ (X : C₃) (R : Presieve X), R ∈ J₃ X →
      R.map (V ⋙ U) ∈ J₁ ((V ⋙ U).obj X) := by
    intro X R hR
    have heq : R.map (V ⋙ U) = (R.map V).map U := by
      funext Y f
      apply propext
      constructor
      · rintro ⟨hg⟩
        exact Presieve.map_map (F := U) (Presieve.map_map (F := V) hg)
      · rintro ⟨⟨hh⟩⟩
        exact Presieve.map_map (F := V ⋙ U) hh
    rw [heq]
    exact hUcover _ _ (hVcover X R hR)
  have hpullback : ∀ (X Y Z : C₃) (R : Presieve X), R ∈ J₃ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) (V ⋙ U) := by
    intro X Y Z R hR f g hf
    have := hVpullback X Y Z R hR f g hf
    have := hUpullback _ _ _ (R.map V) (hVcover X R hR)
      (V.map f) (V.map g) (Presieve.map_map (F := V) hf)
    have := preservesLimit_of_iso_diagram U (cospanCompIso V f g).symm
    infer_instance
  have hVU := Functor.isContinuous_comp V U
    J₃.toGrothendieck J₂.toGrothendieck J₁.toGrothendieck
  have hset := leftAdjointUniq_existsUnique
    (sheafAdjunctionContinuous (V ⋙ U) (Type u) J₃.toGrothendieck J₁.toGrothendieck)
    ((sheafAdjunctionContinuous V (Type u) J₃.toGrothendieck J₂.toGrothendieck).comp
      (sheafAdjunctionContinuous U (Type u) J₂.toGrothendieck J₁.toGrothendieck))
  have hab := leftAdjointUniq_existsUnique
    (sheafAdjunctionContinuous (V ⋙ U) AddCommGrpCat.{u}
      J₃.toGrothendieck J₁.toGrothendieck)
    ((sheafAdjunctionContinuous V AddCommGrpCat.{u}
        J₃.toGrothendieck J₂.toGrothendieck).comp
      (sheafAdjunctionContinuous U AddCommGrpCat.{u}
        J₂.toGrothendieck J₁.toGrothendieck))
  obtain ⟨e, _⟩ := hset.exists
  have : PreservesFiniteLimits
      (sheafPullback V (Type u) J₃.toGrothendieck J₂.toGrothendieck ⋙
        sheafPullback U (Type u) J₂.toGrothendieck J₁.toGrothendieck) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (sheafPullback V (Type u) J₃.toGrothendieck J₂.toGrothendieck ⋙
        sheafPullback U (Type u) J₂.toGrothendieck J₁.toGrothendieck) :=
    comp_preservesFiniteColimits _ _
  have hlim := preservesFiniteLimits_of_natIso e.symm
  have hcolim := preservesFiniteColimits_of_natIso e.symm
  refine ⟨hcover, hpullback, hVU, rfl, ?_, rfl, ?_, ⟨hlim⟩, ⟨hcolim⟩⟩
  · simpa only [Adjunction.comp_unit_app] using hset
  · simpa only [Adjunction.comp_unit_app] using hab

end CategoryTheory

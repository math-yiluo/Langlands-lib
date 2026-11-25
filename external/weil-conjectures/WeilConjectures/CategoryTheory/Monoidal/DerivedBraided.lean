/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# The derived monoidal category of a braided category is braided

Let `L : C ⥤ D` be a localization functor for `W` such that the tensor product of the monoidal
category `C` induces a derived monoidal structure on `DerivedMonoidal L W`
(`CategoryTheory.Functor.HasDerivedMonoidalCategory`). If `C` is braided, the braiding of `C`
induces a natural isomorphism `X ⊗ᴸ Y ≅ Y ⊗ᴸ X`
(`CategoryTheory.DerivedMonoidal.braiding'`): by the universal property of the left derived
functor `- ⊗ᴸ -`, it is the unique natural transformation whose composite with the comparison
`L'X ⊗ᴸ L'Y ⟶ L'(X ⊗ Y)` is `L'(β_ X Y)` (`CategoryTheory.DerivedMonoidal.braiding_hom_μ`).

When K-flat objects form a left derivability structure, the hexagon identities hold
(`CategoryTheory.DerivedMonoidal.braidedCategory'`): for K-flat objects the comparison maps
are isomorphisms, which reduces the hexagons to those of `C`
(`CategoryTheory.DerivedMonoidal.hexagon_forward_of_kFlat`), and every object of
`DerivedMonoidal L W` is isomorphic to the image of a K-flat object.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory _root_.CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]

namespace DerivedMonoidal

local notation "L'" => toDerivedMonoidal L W

variable [L.HasDerivedMonoidalCategory W]

/-- (Implementation) The map `L'Y ⊗ᴸ L'X ⟶ L'(Y ⊗ X) ⟶ L'(X ⊗ Y)` whose second map is
`L'((β_ Y X).hom)`. -/
noncomputable def braidingCounit :
    (((whiskeringLeft₂ D).obj L').obj L').obj (bifunctor L W).flip ⟶
      curriedTensor C ⋙ (whiskeringRight _ _ _).obj L' :=
  (flipFunctor _ _ _).map (counit L W) ≫
    whiskerRight ((flipFunctor _ _ _).map (BraidedCategory.curriedBraidingNatIso C).hom)
      ((whiskeringRight C C _).obj L')

/-- (Implementation) The map `L'Y ⊗ᴸ L'X ⟶ L'(Y ⊗ X) ⟶ L'(X ⊗ Y)` whose second map is
`L'((β_ X Y).inv)`. -/
noncomputable def braidingInvCounit :
    (((whiskeringLeft₂ D).obj L').obj L').obj (bifunctor L W).flip ⟶
      curriedTensor C ⋙ (whiskeringRight _ _ _).obj L' :=
  (flipFunctor _ _ _).map (counit L W) ≫
    whiskerRight (BraidedCategory.curriedBraidingNatIso C).inv ((whiskeringRight C C _).obj L')

/-- (Implementation) The natural transformation `(X, Y) ↦ (Y ⊗ᴸ X ⟶ X ⊗ᴸ Y)` lifted from
`braidingCounit`. -/
noncomputable def braidingNatTrans : (bifunctor L W).flip ⟶ bifunctor L W :=
  (bifunctor L W).leftDerived₂Lift (counit L W) W W _ (braidingCounit L W)

/-- (Implementation) The natural transformation `(X, Y) ↦ (Y ⊗ᴸ X ⟶ X ⊗ᴸ Y)` lifted from
`braidingInvCounit`. -/
noncomputable def braidingInvNatTrans : (bifunctor L W).flip ⟶ bifunctor L W :=
  (bifunctor L W).leftDerived₂Lift (counit L W) W W _ (braidingInvCounit L W)

/-- The square
```
L'X ⊗ᴸ L'Y --β--> L'Y ⊗ᴸ L'X
    |                  |
 L'(X ⊗ Y) --L'β--> L'(Y ⊗ X)
```
commutes, where the vertical maps are the counit. -/
@[reassoc]
lemma braidingNatTrans_fac (X Y : C) :
    ((braidingNatTrans L W).app ((L').obj Y)).app ((L').obj X) ≫ ((counit L W).app Y).app X =
      ((counit L W).app X).app Y ≫ (L').map (β_ X Y).hom :=
  (bifunctor L W).leftDerived₂_fac_app_app (counit L W) W W _ (braidingCounit L W) Y X

/-- The square
```
L'X ⊗ᴸ L'Y --β⁻¹--> L'Y ⊗ᴸ L'X
    |                    |
 L'(X ⊗ Y) --L'β⁻¹--> L'(Y ⊗ X)
```
commutes, where the vertical maps are the counit. -/
@[reassoc]
lemma braidingInvNatTrans_fac (X Y : C) :
    ((braidingInvNatTrans L W).app ((L').obj Y)).app ((L').obj X) ≫ ((counit L W).app Y).app X =
      ((counit L W).app X).app Y ≫ (L').map (β_ Y X).inv :=
  (bifunctor L W).leftDerived₂_fac_app_app (counit L W) W W _ (braidingInvCounit L W) Y X

lemma braidingNatTrans_comp_braidingInvNatTrans :
    (flipFunctor _ _ _).map (braidingNatTrans L W) ≫ braidingInvNatTrans L W =
      𝟙 (bifunctor L W) := by
  apply (bifunctor L W).leftDerived₂_ext (counit L W) W W
  ext X Y
  have h : ((braidingNatTrans L W).app ((L').obj Y)).app ((L').obj X) ≫
      ((braidingInvNatTrans L W).app ((L').obj X)).app ((L').obj Y) ≫
        ((counit L W).app X).app Y = 𝟙 _ ≫ ((counit L W).app X).app Y := by
    dsimp
    rw [braidingInvNatTrans_fac]
    erw [← Category.assoc, braidingNatTrans_fac]
    erw [Category.assoc, ← (L').map_comp, Iso.hom_inv_id, (L').map_id, Category.comp_id,
      Category.id_comp]
  exact (Category.assoc _ _ _).trans h

lemma braidingInvNatTrans_comp_braidingNatTrans :
    (flipFunctor _ _ _).map (braidingInvNatTrans L W) ≫ braidingNatTrans L W =
      𝟙 (bifunctor L W) := by
  apply (bifunctor L W).leftDerived₂_ext (counit L W) W W
  ext X Y
  have h : ((braidingInvNatTrans L W).app ((L').obj Y)).app ((L').obj X) ≫
      ((braidingNatTrans L W).app ((L').obj X)).app ((L').obj Y) ≫
        ((counit L W).app X).app Y = 𝟙 _ ≫ ((counit L W).app X).app Y := by
    dsimp
    rw [braidingNatTrans_fac]
    erw [← Category.assoc, braidingInvNatTrans_fac]
    erw [Category.assoc, ← (L').map_comp, Iso.inv_hom_id, (L').map_id, Category.comp_id,
      Category.id_comp]
  exact (Category.assoc _ _ _).trans h

/-- The braiding of the derived monoidal category. -/
noncomputable def braiding' (X Y : DerivedMonoidal L W) : X ⊗ Y ≅ Y ⊗ X where
  hom := ((braidingNatTrans L W).app Y).app X
  inv := ((braidingInvNatTrans L W).app X).app Y
  hom_inv_id := congr_app (congr_app (braidingNatTrans_comp_braidingInvNatTrans L W) X) Y
  inv_hom_id := congr_app (congr_app (braidingInvNatTrans_comp_braidingNatTrans L W) Y) X

/-- The braiding is characterised by the commutativity of the square
```
L'X ⊗ᴸ L'Y --β--> L'Y ⊗ᴸ L'X
    |                  |
 L'(X ⊗ Y) --L'β--> L'(Y ⊗ X)
```
where the vertical maps are the counit. -/
@[reassoc]
lemma braiding_hom_counit (X Y : C) :
    (braiding' L W ((L').obj X) ((L').obj Y)).hom ≫ ((counit L W).app Y).app X =
      ((counit L W).app X).app Y ≫ (L').map (β_ X Y).hom :=
  braidingNatTrans_fac L W X Y

@[reassoc]
lemma braiding_naturality_left {X Y : DerivedMonoidal L W} (f : X ⟶ Y) (Z : DerivedMonoidal L W) :
    f ▷ Z ≫ (braiding' L W Y Z).hom = (braiding' L W X Z).hom ≫ Z ◁ f :=
  ((braidingNatTrans L W).app Z).naturality f

@[reassoc]
lemma braiding_naturality_right (X : DerivedMonoidal L W) {Y Z : DerivedMonoidal L W}
    (g : Y ⟶ Z) :
    X ◁ g ≫ (braiding' L W X Z).hom = (braiding' L W X Y).hom ≫ g ▷ X :=
  congr_app ((braidingNatTrans L W).naturality g) X

open Functor.LaxMonoidal in
/-- The square
```
L'X ⊗ᴸ L'Y --β--> L'Y ⊗ᴸ L'X
    |                  |
 L'(X ⊗ Y) --L'β--> L'(Y ⊗ X)
```
commutes, where the vertical maps are the lax monoidal structure `μ` of `L'`. -/
@[reassoc]
lemma braiding_hom_μ (X Y : C) :
    (braiding' L W ((L').obj X) ((L').obj Y)).hom ≫ μ (L') Y X =
      μ (L') X Y ≫ (L').map (β_ X Y).hom :=
  braiding_hom_counit L W X Y

section Transfer

variable {L W}

variable (L W) in
/-- (Implementation) The forward hexagon identity at `X`, `Y`, `Z`. -/
abbrev HexagonForward (X Y Z : DerivedMonoidal L W) : Prop :=
  (α_ X Y Z).hom ≫ (braiding' L W X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (braiding' L W X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding' L W X Z).hom

variable (L W) in
/-- (Implementation) The reverse hexagon identity at `X`, `Y`, `Z`. -/
abbrev HexagonReverse (X Y Z : DerivedMonoidal L W) : Prop :=
  (α_ X Y Z).inv ≫ (braiding' L W (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (braiding' L W Y Z).hom ≫ (α_ X Z Y).inv ≫ (braiding' L W X Z).hom ▷ Y

lemma hexagon_forward_transfer₁ {X' X : DerivedMonoidal L W} (e : X' ≅ X)
    (Y Z : DerivedMonoidal L W) (h : HexagonForward L W X' Y Z) : HexagonForward L W X Y Z := by
  unfold HexagonForward at h ⊢
  rw [← cancel_epi ((e.hom ▷ Y) ▷ Z)]
  rw [associator_naturality_left_assoc, braiding_naturality_left_assoc,
    associator_naturality_right, reassoc_of% h]
  conv_rhs => rw [← comp_whiskerRight_assoc, braiding_naturality_left, comp_whiskerRight_assoc,
    associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp,
    braiding_naturality_left, MonoidalCategory.whiskerLeft_comp]

lemma hexagon_forward_transfer₂ {Y' Y : DerivedMonoidal L W} (e : Y' ≅ Y)
    (X Z : DerivedMonoidal L W) (h : HexagonForward L W X Y' Z) : HexagonForward L W X Y Z := by
  unfold HexagonForward at h ⊢
  rw [← cancel_epi ((X ◁ e.hom) ▷ Z)]
  rw [associator_naturality_middle_assoc, braiding_naturality_right_assoc,
    associator_naturality_left, reassoc_of% h]
  rw [← comp_whiskerRight_assoc, braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left_assoc, ← whisker_exchange]

lemma hexagon_forward_transfer₃ {Z' Z : DerivedMonoidal L W} (e : Z' ≅ Z)
    (X Y : DerivedMonoidal L W) (h : HexagonForward L W X Y Z') : HexagonForward L W X Y Z := by
  unfold HexagonForward at h ⊢
  rw [← cancel_epi ((X ⊗ Y) ◁ e.hom)]
  rw [associator_naturality_right_assoc, braiding_naturality_right_assoc,
    associator_naturality_middle, reassoc_of% h]
  conv_rhs => rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, braiding_naturality_right,
    MonoidalCategory.whiskerLeft_comp]

lemma hexagon_reverse_transfer₁ {X' X : DerivedMonoidal L W} (e : X' ≅ X)
    (Y Z : DerivedMonoidal L W) (h : HexagonReverse L W X' Y Z) : HexagonReverse L W X Y Z := by
  unfold HexagonReverse at h ⊢
  rw [← cancel_epi (e.hom ▷ (Y ⊗ Z))]
  rw [associator_inv_naturality_left_assoc, braiding_naturality_left_assoc,
    associator_inv_naturality_middle, reassoc_of% h]
  conv_rhs => rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight, braiding_naturality_left, comp_whiskerRight]

lemma hexagon_reverse_transfer₂ {Y' Y : DerivedMonoidal L W} (e : Y' ≅ Y)
    (X Z : DerivedMonoidal L W) (h : HexagonReverse L W X Y' Z) : HexagonReverse L W X Y Z := by
  unfold HexagonReverse at h ⊢
  rw [← cancel_epi (X ◁ (e.hom ▷ Z))]
  rw [associator_inv_naturality_middle_assoc, braiding_naturality_left_assoc,
    associator_inv_naturality_right, reassoc_of% h]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc, braiding_naturality_left,
    MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
    whisker_exchange]

lemma hexagon_reverse_transfer₃ {Z' Z : DerivedMonoidal L W} (e : Z' ≅ Z)
    (X Y : DerivedMonoidal L W) (h : HexagonReverse L W X Y Z') : HexagonReverse L W X Y Z := by
  unfold HexagonReverse at h ⊢
  rw [← cancel_epi (X ◁ (Y ◁ e.hom))]
  rw [associator_inv_naturality_right_assoc, braiding_naturality_right_assoc,
    associator_inv_naturality_left, reassoc_of% h]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc, braiding_naturality_right,
    MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, braiding_naturality_right, comp_whiskerRight]

end Transfer

section KFlat

variable [W.RespectsIso] [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
  [W.HasTwoOutOfThreeProperty]

open Functor.LaxMonoidal

/-- The forward hexagon identity for objects of the form `L'X`, `L'Y`, `L'Z` with `Y` and `Z`
K-flat. -/
lemma hexagon_forward_of_kFlat (X Y Z : C) (hY : W.kFlat Y) (hZ : W.kFlat Z) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom ≫
      (braiding' L W ((L').obj X) ((L').obj Y ⊗ (L').obj Z)).hom ≫
        (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom =
    (braiding' L W ((L').obj X) ((L').obj Y)).hom ▷ (L').obj Z ≫
      (α_ ((L').obj Y) ((L').obj X) ((L').obj Z)).hom ≫
        (L').obj Y ◁ (braiding' L W ((L').obj X) ((L').obj Z)).hom := by
  have : IsIso (μ (L') Z X) := isIso_counit_app_app_of_kFlat_left L W Z X hZ
  have : IsIso (μ (L') Y (Z ⊗ X)) := isIso_counit_app_app_of_kFlat_left L W Y _ hY
  rw [← cancel_mono ((L').obj Y ◁ μ (L') Z X ≫ μ (L') Y (Z ⊗ X))]
  simp only [Category.assoc]
  rw [← associativity, ← braiding_naturality_right_assoc, braiding_hom_μ_assoc,
    ← associativity_assoc, ← (L').map_comp, ← (L').map_comp]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, braiding_hom_μ,
    MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right, ← associativity_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, braiding_hom_μ,
    MonoidalCategory.comp_whiskerRight_assoc,
    μ_natural_left_assoc, ← (L').map_comp, ← (L').map_comp, BraidedCategory.hexagon_forward]

/-- The reverse hexagon identity for objects of the form `L'X`, `L'Y`, `L'Z` with `Y` and `Z`
K-flat. -/
lemma hexagon_reverse_of_kFlat (X Y Z : C) (hY : W.kFlat Y) (hZ : W.kFlat Z) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv ≫
      (braiding' L W ((L').obj X ⊗ (L').obj Y) ((L').obj Z)).hom ≫
        (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv =
    (L').obj X ◁ (braiding' L W ((L').obj Y) ((L').obj Z)).hom ≫
      (α_ ((L').obj X) ((L').obj Z) ((L').obj Y)).inv ≫
        (braiding' L W ((L').obj X) ((L').obj Z)).hom ▷ (L').obj Y := by
  have : IsIso (μ (L') Z X) := isIso_counit_app_app_of_kFlat_left L W Z X hZ
  have : IsIso (μ (L') (Z ⊗ X) Y) := isIso_counit_app_app_of_kFlat_right L W _ Y hY
  rw [← cancel_mono (μ (L') Z X ▷ (L').obj Y ≫ μ (L') (Z ⊗ X) Y)]
  simp only [Category.assoc]
  rw [← associativity_inv, ← braiding_naturality_left_assoc, braiding_hom_μ_assoc,
    ← associativity_inv_assoc, ← (L').map_comp, ← (L').map_comp]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, braiding_hom_μ,
    MonoidalCategory.comp_whiskerRight_assoc, μ_natural_left, ← associativity_inv_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, braiding_hom_μ,
    MonoidalCategory.whiskerLeft_comp_assoc,
    μ_natural_right_assoc, ← (L').map_comp, ← (L').map_comp, BraidedCategory.hexagon_reverse]

omit [BraidedCategory C] [W.ContainsIdentities] [L.HasDerivedMonoidalCategory W] [W.RespectsIso]
  [W.HasTwoOutOfThreeProperty] in
/-- Every object of the derived monoidal category is isomorphic to the image of a K-flat
object. -/
lemma exists_kFlat_iso (X : DerivedMonoidal L W) :
    ∃ (P : C), W.kFlat P ∧ Nonempty ((L').obj P ≅ X) := by
  have : (L').EssSurj := Localization.essSurj _ W
  have R : W.localizerMorphismKFlat.LeftResolution ((L').objPreimage X) := Classical.arbitrary _
  have hR : IsIso ((L').map R.w) := Localization.inverts (L') W _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property,
    ⟨@asIso _ _ _ _ ((L').map R.w) hR ≪≫ (L').objObjPreimageIso X⟩⟩

/-- The braided structure on the derived monoidal category, induced by a braiding of `C`. -/
noncomputable instance braidedCategory' : BraidedCategory (DerivedMonoidal L W) where
  braiding := braiding' L W
  braiding_naturality_left f Z := braiding_naturality_left L W f Z
  braiding_naturality_right X _ _ g := braiding_naturality_right L W X g
  hexagon_forward X Y Z := by
    obtain ⟨X', -, ⟨e₁⟩⟩ := exists_kFlat_iso L W X
    obtain ⟨Y', hY, ⟨e₂⟩⟩ := exists_kFlat_iso L W Y
    obtain ⟨Z', hZ, ⟨e₃⟩⟩ := exists_kFlat_iso L W Z
    exact hexagon_forward_transfer₁ e₁ _ _ (hexagon_forward_transfer₂ e₂ _ _
      (hexagon_forward_transfer₃ e₃ _ _ (hexagon_forward_of_kFlat L W X' Y' Z' hY hZ)))
  hexagon_reverse X Y Z := by
    obtain ⟨X', -, ⟨e₁⟩⟩ := exists_kFlat_iso L W X
    obtain ⟨Y', hY, ⟨e₂⟩⟩ := exists_kFlat_iso L W Y
    obtain ⟨Z', hZ, ⟨e₃⟩⟩ := exists_kFlat_iso L W Z
    exact hexagon_reverse_transfer₁ e₁ _ _ (hexagon_reverse_transfer₂ e₂ _ _
      (hexagon_reverse_transfer₃ e₃ _ _ (hexagon_reverse_of_kFlat L W X' Y' Z' hY hZ)))

end KFlat

end DerivedMonoidal

end CategoryTheory

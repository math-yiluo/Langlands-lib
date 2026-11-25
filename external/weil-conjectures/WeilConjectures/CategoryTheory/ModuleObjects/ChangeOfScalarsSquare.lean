/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula

/-!

# Change of scalars along a commutative square of algebra objects

Let `F : C ⥤ D` be a lax monoidal functor (the pushforward `f_*` on sheaves) and consider a
commutative square of morphisms of algebra objects
```
      R_Y ---φ_Y---> S_Y
       |              |
      η_R            η_S
       ↓              ↓
    F R_X --F φ_X--> F S_X
```
with `R_X, S_X : C` and `R_Y, S_Y : D`. The "`mapMod` followed by restriction of scalars"
pushforwards `F.mapMod ⋙ comap η : Mod C R_X ⥤ Mod D R_Y` built from `η_R` and `η_S` are then
compatible with the restrictions of scalars along `φ_X` and `φ_Y`
(`Mod.comapMapModComapIso`): restricting scalars along `φ_Y` after pushing forward is pushing
forward after restricting scalars along `φ_X`, both sides being the restriction of scalars along
the two equal composites of the square. This is the formal input from which all the
compatibilities of the six functors with a change of coefficients are deduced by taking mates
and conjugates (`Adjunction.pullIsoOfComapIso`, `Adjunction.pushHomOfComapIso`):

* a *square of adjunctions*, `E₁ ⊣ Res₁`, `E₂ ⊣ Res₂` (extension and restriction of scalars
  on the source and on the target) and `U₁ ⊣ L₁`, `U₂ ⊣ L₂` (pullback and pushforward over the
  two coefficient rings), together with an isomorphism `L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁` between the
  composites of right adjoints, yields the *conjugate* isomorphism `U₁ ⋙ E₁ ≅ E₂ ⋙ U₂` between
  the composites of left adjoints: extension of scalars commutes with pullback;
* and the *mate* `L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂`, the canonical comparison between extension of scalars
  after pushforward and pushforward after extension of scalars. It is not an isomorphism in
  general.

The file also records two further formal compatibilities of restriction of scalars:

* with the linearization `mapModLeft` of a functor satisfying a projection formula, which is
  the shape of the extension by zero along an open immersion
  (`Functor.ProjectionFormula.mapModLeftComapIso`);
* with the extension of scalars along *isomorphisms* of algebra objects, which is the shape of
  the pullback along an open immersion (`Mod.extendScalarsComapIsoOfIsIso`).

Finally, for a monoidal adjunction `G ⊣ F` (the adjunction `f^* ⊣ f_*` on sheaves), the mates
`α = G η ≫ counit : G R_Y ⟶ R_X` of the morphisms `η` also form a commutative square with
`φ_X` and `G φ_Y` (`Adjunction.pullbackHom_square`).

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-! ### Restriction of scalars and the `mapMod`-then-`comap` pushforward -/

namespace Mod

section Comap

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]
  {R_X S_X : C} [MonObj R_X] [MonObj S_X] {R_Y S_Y : D} [MonObj R_Y] [MonObj S_Y]
  (φ_X : R_X ⟶ S_X) [IsMonHom φ_X] (φ_Y : R_Y ⟶ S_Y) [IsMonHom φ_Y]
  (η_R : R_Y ⟶ F.obj R_X) [IsMonHom η_R] (η_S : S_Y ⟶ F.obj S_X) [IsMonHom η_S]
  (sq : φ_Y ≫ η_S = η_R ≫ F.map φ_X)

/-- Given a commutative square `φ_Y ≫ η_S = η_R ≫ F φ_X` of morphisms of algebra objects, the
restriction of scalars along `φ_Y` after the pushforward `F.mapMod ⋙ comap η_S` is the
pushforward `F.mapMod ⋙ comap η_R` after the restriction of scalars along `φ_X`: both are
`F.mapMod` followed by the restriction of scalars along the common composite of the square. -/
noncomputable def comapMapModComapIso :
    (F.mapMod S_X ⋙ comap η_S) ⋙ comap φ_Y ≅ comap φ_X ⋙ (F.mapMod R_X ⋙ comap η_R) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapMod _)
      ((comapComp φ_Y η_S).symm ≪≫ comapCongr sq ≪≫ comapComp η_R (F.map φ_X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapModComapIso φ_X).symm (comap η_R) ≪≫
    Functor.associator _ _ _

/-- The underlying morphism of the components of `Mod.comapMapModComapIso` is the identity. -/
lemma comapMapModComapIso_hom_app_hom (M : Mod C S_X) :
    ((comapMapModComapIso F φ_X φ_Y η_R η_S sq).hom.app M).hom = 𝟙 (F.obj M.X) := by
  change (𝟙 (F.obj M.X) ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ : F.obj M.X ⟶ F.obj M.X) = 𝟙 _
  simp

end Comap

/-! ### Restriction of scalars and extension of scalars along isomorphisms -/

section ExtendScalarsOfIsIso

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]
  {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S'] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
  (a : R ⟶ R') [IsMonHom a] [IsIso a] (b : S ⟶ S') [IsMonHom b] [IsIso b]
  (sq : a ≫ ψ = φ ≫ b)

/-- Given a commutative square `a ≫ ψ = φ ≫ b` of morphisms of algebra objects whose horizontal
sides `a` and `b` are isomorphisms, the extension of scalars along `b` followed by the
restriction of scalars along `ψ` is the restriction of scalars along `φ` followed by the
extension of scalars along `a`: along an isomorphism, extension of scalars is restriction of
scalars along the inverse, and the square `ψ ≫ b⁻¹ = a⁻¹ ≫ φ` commutes. -/
noncomputable def extendScalarsComapIsoOfIsIso :
    extendScalars b ⋙ comap ψ ≅ comap φ ⋙ extendScalars a :=
  Functor.isoWhiskerRight (extendScalarsIsoComapInv b) (comap ψ) ≪≫
    (comapComp ψ (asIso b).inv).symm ≪≫
    comapCongr (by
      rw [← cancel_mono (asIso b).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, asIso_hom, ← sq, ← cancel_epi (asIso a).hom, Iso.hom_inv_id_assoc,
        asIso_hom]) ≪≫
    comapComp (asIso a).inv φ ≪≫
    Functor.isoWhiskerLeft (comap φ) (extendScalarsIsoComapInv a).symm

end ExtendScalarsOfIsIso

/-! ### Extension of scalars along equal morphisms -/

section ExtendScalarsOfEq

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] {φ ψ : R ⟶ S} [IsMonHom φ] [IsMonHom ψ]

/-- Extension of scalars along two equal morphisms of algebra objects, by uniqueness of left
adjoints of the (equal) restrictions of scalars. -/
noncomputable def extendScalarsIsoOfEq (h : φ = ψ) : extendScalars φ ≅ extendScalars ψ :=
  (extendRestrictAdjunction φ).leftAdjointUniq
    ((extendRestrictAdjunction ψ).ofNatIsoRight (comapCongr h).symm)

end ExtendScalarsOfEq

/-! ### Right exactness of extension of scalars -/

section RightExact

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- Extension of scalars is right exact, being a left adjoint. -/
instance preservesFiniteColimits_extendScalars : PreservesFiniteColimits (extendScalars φ) :=
  have := preservesSmallestColimits_of_preservesColimits (extendScalars φ)
  PreservesColimitsOfSize.preservesFiniteColimits _

end RightExact

end Mod

/-! ### Restriction of scalars and the linearization of a projection formula -/

namespace Functor.ProjectionFormula

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {S : D ⥤ C} [S.Monoidal] {P : C ⥤ D} (pf : S.ProjectionFormula P)
  {B B' : D} [MonObj B] [MonObj B'] (φ : B ⟶ B') [IsMonHom φ]

open scoped Obj

/-- The linearization `P_{B'} : Mod C (S B') ⥤ Mod D B'` of a functor `P` satisfying a
projection formula with respect to the strong monoidal `S` is compatible with restriction of
scalars: restricting the `B'`-action of `P M` along `φ : B ⟶ B'` is the linearization `P_B`
applied to `M` with its `S B'`-action restricted along `S φ`. Both actions are
`B ⊗ P M ≅ P (S B ⊗ M) ⟶ P (S B' ⊗ M) ⟶ P M`, by the naturality of the projection formula. -/
noncomputable def mapModLeftComapIso :
    pf.mapModLeft B' ⋙ Mod.comap φ ≅ Mod.comap (S.map φ) ⋙ pf.mapModLeft B :=
  NatIso.ofComponents (fun M ↦ Mod.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    change φ ▷ P.obj M.X ≫ (pf.iso B' M.X).inv ≫ P.map γ[S.obj B',M.X] =
      (pf.iso B M.X).inv ≫ P.map (S.map φ ▷ M.X ≫ γ[S.obj B',M.X])
    rw [whiskerRight_iso_inv_assoc, P.map_comp]))
    (fun f ↦ by ext; simp; rfl)

end Functor.ProjectionFormula

/-! ### Mates and conjugates in a square of adjunctions -/

namespace Adjunction

universe v₃ v₄ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
  {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
  (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)

/-- In a square of adjunctions
```
        E₁ ⊣ Res₁
      A <------> B
 U₁ ⊣ L₁ |      | U₂ ⊣ L₂
      A' <-----> B'
        E₂ ⊣ Res₂
```
(extension and restriction of scalars horizontally, pullback and pushforward vertically), an
isomorphism `L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁` between the two composites of right adjoints (restriction
of scalars commutes with pushforward) has a *conjugate* isomorphism `U₁ ⋙ E₁ ≅ E₂ ⋙ U₂` between
the two composites of left adjoints: extension of scalars commutes with pullback. -/
noncomputable def pullIsoOfComapIso : U₁ ⋙ E₁ ≅ E₂ ⋙ U₂ :=
  (conjugateIsoEquiv (adj₂.comp adjS) (adjR.comp adj₁)).symm e

/-- In the square of adjunctions of `Adjunction.pullIsoOfComapIso`, the *mate*
`L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` of the inverse of the isomorphism `L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁`: the canonical
comparison between extension of scalars after pushforward and pushforward after extension of
scalars. It is the composite
`L₁ ⟶ L₁ ⋙ Res₁ ⋙ E₁ ≅ L₂ ⋙ Res₂ ⋙ E₁ ⟶ ...` transposed along `E₂ ⊣ Res₂`, and it is not an
isomorphism in general. -/
noncomputable def pushHomOfComapIso : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂ :=
  ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk Res₁ L₂ L₁ Res₂ e.inv))

end Adjunction

/-! ### The square of the mates `α` -/

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {D : Type u₂} [Category.{v₂} D]
  {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F) {R_X S_X : C} [MonObj R_X] [MonObj S_X] {R_Y S_Y : D}
  (φ_X : R_X ⟶ S_X) (φ_Y : R_Y ⟶ S_Y) (η_R : R_Y ⟶ F.obj R_X) (η_S : S_Y ⟶ F.obj S_X)

open scoped Obj

/-- If the morphisms `η_R : R_Y ⟶ F R_X`, `η_S : S_Y ⟶ F S_X` form a commutative square with
`φ_X` and `φ_Y`, then so do their mates `α_R = G η_R ≫ counit : G R_Y ⟶ R_X` and
`α_S : G S_Y ⟶ S_X` with `φ_X` and `G φ_Y`: `G φ_Y ≫ α_S = α_R ≫ φ_X`. -/
lemma pullbackHom_square (sq : φ_Y ≫ η_S = η_R ≫ F.map φ_X) :
    G.map φ_Y ≫ (G.map η_S ≫ adj.counitAlgHom S_X) =
      (G.map η_R ≫ adj.counitAlgHom R_X) ≫ φ_X := by
  rw [← Category.assoc, ← G.map_comp, sq, G.map_comp, Category.assoc, Category.assoc,
    Adjunction.counitAlgHom, Adjunction.counitAlgHom, adj.counit_naturality]


end Adjunction

end CategoryTheory

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Grothendieck abelian categories are locally presentable

Let `C` be a Grothendieck abelian category and `G` a separator of `C`. We show that `G` is
`κ`-presentable for any regular cardinal `κ` which is bigger than the cardinalities of
`Subobject G` and of `G ⟶ G`. As `{G}` is a strong generator of `C`, it follows that `C` is
locally `κ`-presentable, so that `C` is locally presentable and every object of `C` is
presentable.

The docstring of `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda` states the
expectation that every object of a Grothendieck abelian category is `κ`-presentable for some
regular cardinal `κ`, and only proves that `colim (Hom(G, Y j)) ⟶ Hom(G, colim Y)` is
injective for `κ`-filtered diagrams, and bijective for `κ`-filtered diagrams of monomorphisms.
The results of this file settle that expectation and are intended for Mathlib.

## Proof of surjectivity

Let `R := (End G)ᵐᵒᵖ`, `U := preadditiveCoyonedaObj G : C ⥤ ModuleCat R` and let `T` be its
left adjoint `tensorObj G`. By the Gabriel-Popescu theorem, `U` is fully faithful and `T` is
exact. Let `Y : J ⥤ C` be a `κ`-filtered diagram with colimit `L` and let `f : G ⟶ L`.

* The comparison map `φ : colim (Y ⋙ U) ⟶ U L` is injective
  (`IsPresentable.mono_colimitDesc_preadditiveCoyonedaObj`), and `T.map φ` is an isomorphism
  (`Adjunction.isIso_map_colimitDesc_mapCocone`).
* Let `g : R ⟶ U L` be the linear map `r ↦ r • f` and consider the pullback square
  ```
  pullback φ g ──fst──▶ colim (Y ⋙ U)
       │                     │
      snd                    │ φ
       ▼                     ▼
       R ───────── g ──────▶ U L
  ```
  Then `snd` is injective, so `pullback φ g` has cardinality `< κ` and is `κ`-presentable in
  `ModuleCat R` (`ModuleCat.isCardinalPresentable_of_hasCardinalLT`); and `T.map snd` is an
  isomorphism, as `T` preserves pullbacks.
* By presentability, `fst = ψ₁ ≫ colimit.ι _ j` for some `j` and `ψ₁ : pullback φ g ⟶ U (Y j)`.
  Since `T.map snd` is an isomorphism, the adjunction extends `ψ₁` to `ψ : R ⟶ U (Y j)` with
  `snd ≫ ψ = ψ₁`, and shows that `g = ψ ≫ U.map (c.ι.app j)`. Evaluating at `1` gives
  `f = ψ 1 ≫ c.ι.app j`.

## Main results

- `IsGrothendieckAbelian.isCardinalPresentable_of_isSeparator`: a separator `G` is
  `κ`-presentable if `Subobject G` and `G ⟶ G` have cardinality `< κ`.
- `IsGrothendieckAbelian.isCardinalLocallyPresentable_of_isSeparator`: under the same
  assumptions, `C` is locally `κ`-presentable.
- `IsGrothendieckAbelian.isLocallyPresentable`: a Grothendieck abelian category is locally
  presentable; in particular every object is presentable.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

namespace IsPresentable

/-- If `κ` is a regular cardinal bigger than the cardinality of `Subobject G`, then for a
`κ`-filtered diagram `Y` with colimit cocone `c`, the comparison map
`colim (Y ⋙ preadditiveCoyonedaObj G) ⟶ (preadditiveCoyonedaObj G).obj c.pt` is injective. -/
lemma mono_colimitDesc_preadditiveCoyonedaObj {G : C} {κ : Cardinal.{v}} [Fact κ.IsRegular]
    (hSub : HasCardinalLT (Subobject G) κ) {J : Type v} [SmallCategory J]
    [IsCardinalFiltered J κ] {Y : J ⥤ C} {c : Cocone Y} (hc : IsColimit c) :
    Mono (colimit.desc (Y ⋙ preadditiveCoyonedaObj G)
      ((preadditiveCoyonedaObj G).mapCocone c)) := by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep (Y ⋙ preadditiveCoyonedaObj G) x
  have hy : colimit.desc _ ((preadditiveCoyonedaObj G).mapCocone c)
      (colimit.ι (Y ⋙ preadditiveCoyonedaObj G) j y) = y ≫ c.ι.app j :=
    ConcreteCategory.congr_hom (colimit.ι_desc ((preadditiveCoyonedaObj G).mapCocone c) j) y
  obtain ⟨k, a, ha⟩ := injectivity₀ hc hSub y (hy.symm.trans hx)
  rw [← ConcreteCategory.congr_hom (colimit.w (Y ⋙ preadditiveCoyonedaObj G) a) y]
  exact (congr_arg (colimit.ι (Y ⋙ preadditiveCoyonedaObj G) k) ha).trans (map_zero _)

/-- If `G` is a separator of a Grothendieck abelian category and `κ` a regular cardinal
bigger than the cardinalities of `Subobject G` and `G ⟶ G`, then any morphism `f` from `G`
to the colimit of a `κ`-filtered diagram `Y` factors through one of the objects of the diagram:
```
        f
   G ───────▶ c.pt
    ╲          ▲
   y ╲         │ c.ι.app j
      ▶        │
       Y.obj j ┘
```
-/
lemma surjectivity_of_isSeparator {G : C} (hG : IsSeparator G) {κ : Cardinal.{v}}
    [Fact κ.IsRegular] (hSub : HasCardinalLT (Subobject G) κ) (hEnd : HasCardinalLT (G ⟶ G) κ)
    {J : Type v} [SmallCategory J] [IsCardinalFiltered J κ] {Y : J ⥤ C} {c : Cocone Y}
    (hc : IsColimit c) (f : G ⟶ c.pt) :
    ∃ (j : J) (y : G ⟶ Y.obj j), f = y ≫ c.ι.app j := by
  let U := preadditiveCoyonedaObj G
  let adj : tensorObj G ⊣ U := tensorObjPreadditiveCoyonedaObjAdjunction G
  have : U.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  have : U.Full := GabrielPopescu.full G hG
  have := GabrielPopescu.preservesFiniteLimits G hG
  have hR : HasCardinalLT (End G)ᵐᵒᵖ κ := hEnd.of_injective (fun x : (End G)ᵐᵒᵖ ↦ x.unop.asHom)
    (fun _ _ h ↦ MulOpposite.unop_injective (End.ext h))
  -- the comparison map `colim (Y ⋙ U) ⟶ U c.pt`
  let φ : colimit (Y ⋙ U) ⟶ U.obj c.pt := colimit.desc _ (U.mapCocone c)
  have : Mono φ := mono_colimitDesc_preadditiveCoyonedaObj hSub hc
  have : IsIso ((tensorObj G).map φ) := adj.isIso_map_colimitDesc_mapCocone hc
  -- the linear map `r ↦ r • f` and the pullback of `φ` along it
  let g : ModuleCat.of (End G)ᵐᵒᵖ (End G)ᵐᵒᵖ ⟶ U.obj c.pt :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ f)
  have hP := IsPullback.of_hasPullback φ g
  have : IsIso ((tensorObj G).map (pullback.snd φ g)) := (hP.map _).isIso_snd_of_isIso
  have : IsCardinalPresentable (pullback φ g) κ :=
    ModuleCat.isCardinalPresentable_of_hasCardinalLT hR
      (hR.of_injective _ ((ModuleCat.mono_iff_injective (pullback.snd φ g)).1 inferInstance))
  -- `pullback.fst φ g = ψ₁ ≫ colimit.ι _ j`
  obtain ⟨j, ψ₁, hψ₁⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (colimit.isColimit (Y ⋙ U)) (pullback.fst φ g)
  -- extend `ψ₁` along `pullback.snd φ g`, using the adjunction
  let ψ : ModuleCat.of (End G)ᵐᵒᵖ (End G)ᵐᵒᵖ ⟶ U.obj (Y.obj j) :=
    adj.homEquiv _ _ (inv ((tensorObj G).map (pullback.snd φ g)) ≫ (adj.homEquiv _ _).symm ψ₁)
  have hψ : pullback.snd φ g ≫ ψ = ψ₁ := by
    rw [← adj.homEquiv_naturality_left, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  have key : g = ψ ≫ U.map (c.ι.app j) := by
    apply (adj.homEquiv _ _).symm.injective
    rw [← cancel_epi ((tensorObj G).map (pullback.snd φ g)),
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm,
      reassoc_of% hψ, ← hP.w, ← hψ₁]
    dsimp only [φ, colimit.cocone_ι]
    rw [Category.assoc, colimit.ι_desc]
    rfl
  exact ⟨j, ψ 1, (one_smul _ f).symm.trans (ConcreteCategory.congr_hom key 1)⟩

end IsPresentable

open IsPresentable in
/-- A separator `G` of a Grothendieck abelian category is `κ`-presentable for any regular
cardinal `κ` which is bigger than the cardinalities of `Subobject G` and of `G ⟶ G`.

This gives an explicit bound on `κ`; for the mere existence of such a `κ`, use the instance
`IsGrothendieckAbelian.isLocallyPresentable`, which makes every object presentable. -/
theorem isCardinalPresentable_of_isSeparator {G : C} (hG : IsSeparator G)
    {κ : Cardinal.{v}} [Fact κ.IsRegular] (hSub : HasCardinalLT (Subobject G) κ)
    (hEnd : HasCardinalLT (G ⟶ G) κ) : IsCardinalPresentable G κ where
  preservesColimitOfShape J _ _ := ⟨fun {_} ↦ ⟨fun {_} hc ↦ ⟨
    have := isFiltered_of_isCardinalFiltered J κ
    Types.FilteredColimit.isColimitOf' _ _
      (surjectivity_of_isSeparator hG hSub hEnd hc) (injectivity hc hSub)⟩⟩⟩

/-- If `G` is a separator of a Grothendieck abelian category `C` and `κ` is a regular cardinal
bigger than the cardinalities of `Subobject G` and of `G ⟶ G`, then `C` is locally
`κ`-presentable. -/
theorem isCardinalLocallyPresentable_of_isSeparator {G : C} (hG : IsSeparator G)
    {κ : Cardinal.{v}} [Fact κ.IsRegular] (hSub : HasCardinalLT (Subobject G) κ)
    (hEnd : HasCardinalLT (G ⟶ G) κ) : IsCardinalLocallyPresentable C κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  exact ⟨.singleton G, inferInstance, hG.isStrongGenerator, by
    simpa [ObjectProperty.singleton_le_iff, isCardinalPresentable_iff] using
      isCardinalPresentable_of_isSeparator hG hSub hEnd⟩

/-- A Grothendieck abelian category is locally presentable. In particular, every object is
presentable. -/
instance isLocallyPresentable : IsLocallyPresentable.{v} C where
  exists_cardinal := by
    obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal.{v}
      (Subobject (separator C) ⊕ (separator C ⟶ separator C))
    have : Fact κ.IsRegular := ⟨hκ⟩
    exact ⟨κ, this, isCardinalLocallyPresentable_of_isSeparator (isSeparator_separator C)
      (h.of_injective _ Sum.inl_injective) (h.of_injective _ Sum.inr_injective)⟩

end CategoryTheory.IsGrothendieckAbelian

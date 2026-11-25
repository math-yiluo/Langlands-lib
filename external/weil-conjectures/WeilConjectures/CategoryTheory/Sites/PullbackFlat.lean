/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Vanishing

/-!
# Pullback of sheaves along a flat functor preserves flatness

Let `G : C ⥤ D` be a representably flat, cover-preserving functor between sites and let `R` be
a Noetherian commutative ring. The pullback `G^* F = (Lan_{G} F)^#` of a flat sheaf `F` of
`R`-modules is flat (`CategoryTheory.flat_sheafPullback_obj`).

By the relation criterion for flatness
(`CategoryTheory.Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations`) it suffices
that linear relations between sections of `Lan_G F` are locally trivial. The left Kan extension
is a filtered colimit `(Lan_G F)(U) = colim_{U ⟶ G V} F(V)`, so finitely many relations between
finitely many sections over `U` come from one stage `F(V)` where they already hold
(`ModuleCat.exists_lift_of_isColimit`). Since `F` is flat they are trivial locally on `V`
(`CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat`), and pulling the covering back to
`U` along `G` makes them trivial locally on `U`.

This is the argument of blueprint `corollary-finite-tor-amplitude-under-comparison` (the relation
criterion for flatness transported by an exact inverse image), at the level of an arbitrary flat
cover-preserving functor.

## Main results

- `CategoryTheory.Sheaf.hasLocallyTrivialRelations_lan`: `Lan_G F` has locally trivial
  relations.
- `CategoryTheory.flat_sheafPullback_obj`: the pullback of a flat sheaf of modules along a
  representably flat cover-preserving functor is flat.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace CategoryTheory

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [EssentiallySmall.{u + 1} C]
  [EssentiallySmall.{u + 1} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  {G : C ⥤ D} [RepresentablyFlat G]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R, G.op.HasPointwiseLeftKanExtension P]

omit [EssentiallySmall.{u + 1} D] in
/-- **The left Kan extension of a flat sheaf has locally trivial relations.** Let `F` be a flat
sheaf of modules over a Noetherian ring on `C`. Linear relations between sections of
`Lan_G F` over `U` come from a stage `F(V)`, `U ⟶ G V`, of the filtered colimit computing
`(Lan_G F)(U)`; they are trivial locally on `V` as `F` is flat, hence trivial on the pullback to
`U` of the image under `G` of a covering of `V`. -/
theorem Sheaf.hasLocallyTrivialRelations_lan (hG : CoverPreserving J K G)
    {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F) :
    Presheaf.HasLocallyTrivialRelations K (G.op.lan.obj F.obj) := by
  intro U s q y e hey
  let P := G.op.lan.obj F.obj
  -- the elements `yⱼ` and their relations come from one stage `F(V)` of the colimit
  have : IsFiltered (CostructuredArrow G.op (op U)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G U)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let hcol := G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op U)
  obtain ⟨T₀, y', hy', hey'⟩ := ModuleCat.exists_lift_of_isColimit hcol y e hey
  -- the relations are trivial locally on `V`, as `F` is flat
  obtain ⟨S, hS, hfac⟩ :=
    Sheaf.hasLocallyTrivialRelations_of_flat hF (V := T₀.left.unop) y' e hey'
  refine ⟨_, K.pullback_stable T₀.hom.unop (hG.cover_preserve hS), ?_⟩
  rintro U' h ⟨W, f, h', hf, hcomp⟩
  obtain ⟨t', b, z, heb, hyz⟩ := hfac f hf
  -- restricted to `U'`, each `yⱼ` is `∑ₘ bⱼₘ wₘ`
  refine ⟨t', b, fun m ↦ P.map h'.op ((G.op.leftKanExtensionUnit F.obj).app (op W) (z m)),
    heb, fun j ↦ ?_⟩
  rw [← hy' j]
  change P.map h.op (P.map T₀.hom ((G.op.leftKanExtensionUnit F.obj).app T₀.left (y' j))) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have hτ : T₀.hom ≫ h.op = G.op.map f.op ≫ h'.op :=
    Quiver.Hom.unop_inj (by simpa using hcomp)
  rw [hτ, Functor.map_comp, ConcreteCategory.comp_apply]
  have hnat := NatTrans.naturality_apply (G.op.leftKanExtensionUnit F.obj) f.op (y' j)
  change _ = P.map (G.op.map f.op) _ at hnat
  rw [← hnat, hyz j]
  change (P.map h'.op).hom
      (((G.op.leftKanExtensionUnit F.obj).app (op W)).hom (∑ m, b j m • z m)) =
    ∑ m, b j m • (P.map h'.op).hom
      (((G.op.leftKanExtensionUnit F.obj).app (op W)).hom (z m))
  simp only [map_sum, map_smul]

variable [K.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [K.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

/-- Blueprint `corollary-finite-tor-amplitude-under-comparison`, for an arbitrary site morphism:
**pullback along a flat functor preserves flat sheaves of modules.** Let `G : C ⥤ D` be a
representably flat, cover-preserving functor and `R` a Noetherian commutative ring. The pullback
`G^* F = (Lan_G F)^#` of a flat sheaf `F` of `R`-modules on `C` is flat.

The presheaf `Lan_G F` has locally trivial relations
(`CategoryTheory.Sheaf.hasLocallyTrivialRelations_lan`), so its sheafification is flat by the
relation criterion `CategoryTheory.Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations`.
-/
theorem flat_sheafPullback_obj (hG : CoverPreserving J K G) {F : Sheaf J (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat
      ((Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} R) J K).obj F) :=
  Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations
    (Sheaf.hasLocallyTrivialRelations_lan hG hF)

end CategoryTheory

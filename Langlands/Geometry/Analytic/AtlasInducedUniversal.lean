import Langlands.Geometry.Analytic.AtlasInducedUnit

/-! # Normalized arbitrary-atlas induction into arbitrary action targets -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory
open PresentedAffinoidAlgebra.InducedAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)
  {X X' : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H}
  {Y Z : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) G}

/-- Complete target actions compose in geometric order. -/
theorem targetAction_comp
    (Y : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) G) (g k : G) :
    Y.ρ k ≫ Y.ρ g = Y.ρ (g * k) :=
  (Y.ρ.map_mul g k).symm

/-- Descend the prescribed full target-action arrow from every original coset copy. -/
def extendMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    copies H X ⟶ Y.V :=
  AtlasDisjointUnion.desc (component H X) (component_hasNonemptyCharts H X)
    (fun c => f.hom ≫ Y.ρ c.out)

/-- Restriction recovers the complete prescribed bounded arrow on each copy. -/
@[simp]
theorem copy_extendMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (c : G ⧸ H) :
    copy H X c ≫ extendMap H f = f.hom ≫ Y.ρ c.out :=
  AtlasDisjointUnion.inclusion_desc _ _ _ c

/-- Correction equivariance holds for all chosen charts and bounded pullbacks. -/
theorem extendMap_equivariant (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (g : G) :
    copiesActionMap H X g ≫ extendMap H f = extendMap H f ≫ Y.ρ g := by
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  let f₀ : X.V.nonemptyPresentation ⟶ Y.V := f.hom
  have hc (d : G ⧸ H) : copy H X d ≫ extendMap H f = f₀ ≫ Y.ρ d.out :=
    copy_extendMap H f d
  have hf : localAction H X (correction H g c) ≫ f₀ =
      f₀ ≫ Y.ρ (correction H g c : G) := f.comm (correction H g c)
  change copy H X c ≫ (copiesActionMap H X g ≫ extendMap H f) =
    copy H X c ≫ (extendMap H f ≫ Y.ρ g)
  calc
    _ = localAction H X (correction H g c) ≫
        (copy H X (g • c) ≫ extendMap H f) := by
      rw [← Category.assoc, copy_action, Category.assoc]
    _ = localAction H X (correction H g c) ≫
        (f₀ ≫ Y.ρ (g • c).out) := by rw [hc]
    _ = (f₀ ≫ Y.ρ (correction H g c : G)) ≫ Y.ρ (g • c).out := by
      rw [← Category.assoc, hf]
    _ = f₀ ≫ Y.ρ (g * c.out) := by
      rw [Category.assoc, targetAction_comp, ← correction_spec]
    _ = _ := by
      rw [← Category.assoc, hc, Category.assoc, targetAction_comp]

/-- The constructed full-group-equivariant extension into an arbitrary target. -/
def extendToAction (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    copiesAction H X ⟶ Y where
  hom := extendMap H f
  comm := extendMap_equivariant H f

/-- The inverse representative cancels in the complete unit-extension triangle. -/
theorem unitMap_extendMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    unitMap H X ≫ extendMap H f = f.hom := by
  let f₀ : X.V.nonemptyPresentation ⟶ Y.V := f.hom
  have hf : localAction H X (identityRepresentative H)⁻¹ ≫ f₀ =
      f₀ ≫ Y.ρ ((identityRepresentative H)⁻¹ : H) :=
    f.comm (identityRepresentative H)⁻¹
  have hc : copy H X (identityCoset H) ≫ extendMap H f =
      f₀ ≫ Y.ρ (identityRepresentative H : G) :=
    copy_extendMap H f (identityCoset H)
  change unitMap H X ≫ extendMap H f = f₀
  rw [unitMap, Category.assoc, hc, ← Category.assoc, hf,
    Category.assoc, targetAction_comp]
  simp

/-- Restrict a full equivariant arrow along the constructed normalized unit. -/
def restrictFromAction (p : copiesAction H X ⟶ Y) :
    normalizedAction H X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y :=
  unitEquivariantMap H X ≫
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map p

@[simp]
theorem restrictFromAction_extendToAction (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    restrictFromAction H (extendToAction H f) = f :=
  Action.Hom.ext (unitMap_extendMap H f)

/-- Every full equivariant arrow is recovered on each actual copy. -/
@[simp]
theorem extendToAction_restrictFromAction (p : copiesAction H X ⟶ Y) :
    extendToAction H (restrictFromAction H p) = p := by
  apply Action.Hom.ext
  let p₀ : copies H X ⟶ Y.V := p.hom
  change extendMap H (restrictFromAction H p) = p₀
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  change copy H X c ≫ extendMap H (restrictFromAction H p) = copy H X c ≫ p₀
  rw [copy_extendMap]
  change (unitMap H X ≫ p₀) ≫ Y.ρ c.out = copy H X c ≫ p₀
  have hp : copiesActionMap H X c.out ≫ p₀ = p₀ ≫ Y.ρ c.out := p.comm c.out
  rw [Category.assoc, ← hp, ← Category.assoc, unitMap_action]

/-- Relative Hom correspondence with normalized source and arbitrary atlas-action target. -/
def actionExtensionEquiv :
    (copiesAction H X ⟶ Y) ≃
      (normalizedAction H X ⟶
        (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) where
  toFun := restrictFromAction H
  invFun := extendToAction H
  left_inv := extendToAction_restrictFromAction H
  right_inv := restrictFromAction_extendToAction H

/-- Agreement after the unit determines the full equivariant extension. -/
theorem extendToAction_unique (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (p : copiesAction H X ⟶ Y) (hp : unitMap H X ≫ p.hom = f.hom) :
    p = extendToAction H f := by
  apply (actionExtensionEquiv H).injective
  change restrictFromAction H p = restrictFromAction H (extendToAction H f)
  rw [restrictFromAction_extendToAction]
  exact Action.Hom.ext hp

/-- Naturality retains the entire chosen source arrow under normalization. -/
theorem actionExtensionEquiv_naturality_left
    (a : X' ⟶ X) (p : copiesAction H X ⟶ Y) :
    actionExtensionEquiv H (copiesEquivariantMap H a ≫ p) =
      (AffinoidAtlasPresentation.nonemptyActionFunctor H).map a ≫
        actionExtensionEquiv H p := by
  apply Action.Hom.ext
  let p₀ : copies H X ⟶ Y.V := p.hom
  change unitMap H X' ≫ (copiesMap H a ≫ p₀) =
    localMap H a ≫ (unitMap H X ≫ p₀)
  rw [← Category.assoc, ← unitMap_naturality, Category.assoc]

/-- The correspondence is natural for every full equivariant target arrow. -/
theorem actionExtensionEquiv_naturality_right
    (p : copiesAction H X ⟶ Y) (q : Y ⟶ Z) :
    actionExtensionEquiv H (p ≫ q) =
      actionExtensionEquiv H p ≫
        (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q := by
  apply Action.Hom.ext
  exact (Category.assoc (unitMap H X) p.hom q.hom).symm

/-- The constructed extension commutes with normalized source composition. -/
theorem extendToAction_naturality_left (a : X' ⟶ X)
    (f : normalizedAction H X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    extendToAction H ((AffinoidAtlasPresentation.nonemptyActionFunctor H).map a ≫ f) =
      copiesEquivariantMap H a ≫ extendToAction H f := by
  apply (actionExtensionEquiv H).injective
  rw [actionExtensionEquiv_naturality_left]
  change restrictFromAction H (extendToAction H _) =
    (AffinoidAtlasPresentation.nonemptyActionFunctor H).map a ≫
      restrictFromAction H (extendToAction H f)
  rw [restrictFromAction_extendToAction, restrictFromAction_extendToAction]

/-- Extension commutes with every full equivariant target arrow. -/
theorem extendToAction_naturality_right (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (q : Y ⟶ Z) :
    extendToAction H
        (f ≫ (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q) =
      extendToAction H f ≫ q := by
  apply (actionExtensionEquiv H).injective
  rw [actionExtensionEquiv_naturality_right]
  change restrictFromAction H (extendToAction H _) =
    restrictFromAction H (extendToAction H f) ≫
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q
  rw [restrictFromAction_extendToAction, restrictFromAction_extendToAction]

/-- The extension applies the representative's original target point action. -/
@[simp]
theorem extendMap_baseMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (c : G ⧸ H) (x : X.V.space) :
    (extendMap H f).baseMap ⟨c, x⟩ = (Y.ρ c.out).baseMap (f.hom.baseMap x) := rfl

/-- The chosen chart is exactly the input target chart followed by the target action. -/
@[simp]
theorem extendMap_indexMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (c : G ⧸ H) (i : X.V.nonemptyPresentation.atlas.Index) :
    (extendMap H f).indexMap ⟨c, i⟩ =
      (Y.ρ c.out).indexMap (f.hom.indexMap i) := rfl

/-- The bounded pullback is the actual contravariant composite of the supplied maps. -/
@[simp]
theorem extendMap_pullback (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (c : G ⧸ H) (i : X.V.nonemptyPresentation.atlas.Index) :
    (extendMap H f).pullback ⟨c, i⟩ =
      (f.hom.pullback i).comp ((Y.ρ c.out).pullback (f.hom.indexMap i)) := rfl

end Langlands.Analytic.AtlasInducedAction

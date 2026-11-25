/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.CategoryTheory.SiteCechComplex

/-! # Compatible affine étale Čech presentation data

Source: Stacks Project, Tag 099U, finite Čech limit reductions.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Compatible affine étale approximations of a specified finite Čech nerve.
The cone identities include every index map, not only the alternating faces.
Source: Stacks Project, Tag 099U (auxiliary; not a blueprint node). -/
structure CoefficientAffineCechPresentation (X : Scheme.{u})
    {U : Scheme.coefficientProEtaleSiteModel.{u, v} X} {m : ℕ}
    {V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X} {f : ∀ a, V a ⟶ U}
    (S : SiteCechComplex V f) (J : Type (u + 1)) [SmallCategory J] where
  base : J → Scheme.smallModelComparisonEtaleSite.{u, v} X
  family : J → Fin m → Scheme.smallModelComparisonEtaleSite.{u, v} X
  arrow : ∀ j a, family j a ⟶ base j
  covering : ∀ j, Presieve.ofArrows (family j) (arrow j) ∈
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X).toPrecoverage (base j)
  stage : ∀ j, SiteCechComplex (family j) (arrow j)
  trans : ∀ {i j : J}, (i ⟶ j) → ∀ p t, (stage i).W p t ⟶ (stage j).W p t
  trans_id : ∀ i p t, trans (𝟙 i) p t = 𝟙 _
  trans_comp : ∀ {i j k : J} (a : i ⟶ j) (b : j ⟶ k) p t,
    trans (a ≫ b) p t = trans a p t ≫ trans b p t
  trans_index : ∀ {i j : J} (a : i ⟶ j) {p q : ℕ}
    (t : Fin (p + 1) → Fin m) (α : Fin (q + 1) → Fin (p + 1)),
    trans a p t ≫ (stage j).indexMap t α =
      (stage i).indexMap t α ≫ trans a q (t ∘ α)
  projection : ∀ p t j, S.W p t ⟶
    (Scheme.smallModelComparisonInclusion.{u, v} X).obj ((stage j).W p t)
  projection_trans : ∀ {i j : J} (a : i ⟶ j) p t,
    projection p t i ≫ (Scheme.smallModelComparisonInclusion.{u, v} X).map (trans a p t) =
      projection p t j
  projection_index : ∀ j {p q : ℕ} (t : Fin (p + 1) → Fin m)
    (α : Fin (q + 1) → Fin (p + 1)),
    S.indexMap t α ≫ projection q (t ∘ α) j =
      projection p t j ≫
        (Scheme.smallModelComparisonInclusion.{u, v} X).map ((stage j).indexMap t α)
  affine_stage : ∀ j p t, IsAffine (AsSmall.down.obj ((stage j).W p t)).left
  affine_vertex : ∀ p t, IsAffine (AsSmall.down.obj (S.W p t)).left

namespace CoefficientAffineCechPresentation
variable {X : Scheme.{u}} {U : Scheme.coefficientProEtaleSiteModel.{u, v} X} {m : ℕ}
  {V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X} {f : ∀ a, V a ⟶ U}
  {S : SiteCechComplex V f} {J : Type (u + 1)} [SmallCategory J]
  (P : CoefficientAffineCechPresentation X S J)

/-- The stage diagram for one tuple of the nerve. -/
def nerve (p : ℕ) (t : Fin (p + 1) → Fin m) :
    J ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X where
  obj j := (P.stage j).W p t
  map a := P.trans a p t
  map_id j := P.trans_id j p t
  map_comp a b := P.trans_comp a b p t

/-- The prescribed intersection and its restriction projections. -/
def cone (p : ℕ) (t : Fin (p + 1) → Fin m) :
    Cone (P.nerve p t ⋙ Scheme.smallModelComparisonInclusion.{u, v} X) where
  pt := S.W p t
  π.app j := P.projection p t j
  π.naturality i j a := by
    change 𝟙 _ ≫ P.projection p t j = _
    exact (Category.id_comp _).trans (P.projection_trans a p t).symm
end CoefficientAffineCechPresentation

end AlgebraicGeometry.ProEtale

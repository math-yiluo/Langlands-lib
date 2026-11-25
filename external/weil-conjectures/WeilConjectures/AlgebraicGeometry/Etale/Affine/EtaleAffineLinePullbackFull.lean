/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Fullness of ordinary etale affine-line pullback -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem a1_geometricallyConnected (S : Scheme.{u}) :
    GeometricallyConnected (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) := by
  constructor
  intro K hK y Z fst snd h
  have : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Affine-line inverse image on ordinary etale module sheaves is full.
Source: Stacks Project, Tag 0A3H: section invariance for flat quasi-compact morphisms
with connected geometric fibres.
(blueprint: new-lem-pur-etale-a1-pullback-full).
Proof: the projection is smooth, affine and geometrically irreducible. On each etale
object V the adjunction unit is the section map for the base-changed projection, which
is an isomorphism by the cited section-invariance theorem. The forgetful functor from
sheaves reflects isomorphisms, so the unit is invertible and its left adjoint is full. -/
theorem etale_a1_pullback_full (S : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).Full := by
  let p := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  let : GeometricallyConnected p := a1_geometricallyConnected S
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  have hi (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso (adj.unit.app G) := by
    have : IsIso ((sheafToPresheaf _ _).map (adj.unit.app G)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      let : Smooth p := SmoothOfRelativeDimension.smooth
        (Nat.card (ULift.{u} (Fin 1))) p
      let : Flat p := inferInstance
      let : QuasiCompact p := by dsimp [p]; infer_instance
      let q := pullback.fst V.unop.hom p
      let φ := 𝟙 ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V.unop)
      have hq : φ.left ≫ q = q := Category.id_comp _
      let : Flat (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      let : QuasiCompact (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      let : GeometricallyConnected (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      have h := Etale.isIso_upperStarSectionsMap Λ p G φ
      change IsIso ((adj.unit.app G).hom.app V)
      change IsIso ((adj.unit.app G).hom.app V ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj G).obj.map (𝟙 _)) at h
      rw [CategoryTheory.Functor.map_id] at h
      exact (isIso_comp_right_iff ((adj.unit.app G).hom.app V) (𝟙 _)).mp h
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  let : ∀ G, IsIso (adj.unit.app G) := hi
  exact adj.full_L_of_isSplitEpi_unit_app

end AlgebraicGeometry

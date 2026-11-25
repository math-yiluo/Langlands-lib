/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AffineOpenPushforwardExchange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The ordinary exchange is invertible for the Cech resolution data.
Source: Stacks Project, Tags 02KG and 02KH; the affine intersection exchange
paragraph of `lem-pc-affine-alternating-cech-pinned-mate`.
(blueprint: lem-pc-s3-affine-alternating-cech-resolution-exchange).
Proof: Choose the representative C and its degreewise finite-product
identifications from hterms. For each affine W, separatedness makes W.ι affine,
and W.ι ≫ f is affine because its source and target are affine. The restriction
G|W is quasi-coherent. Apply affinePushforward_baseChange to the cartesian
squares for W.ι and for W.ι ≫ f. The vertical pasting identity for moduleBaseChangeMap,
obtained by transposing under the pullback adjunctions,
with the invertible exchange for W.ι, shows that ordinary exchange for f on
W.ι_*(G|W) is invertible. Both functors in the exchange are additive, so they
preserve finite biproducts, which are the finite products of these module
categories. Naturality transports the factor isomorphisms across each specified
product isomorphism for C.X k. Hence termwise exchange on C is an isomorphism
of complexes; its homotopy image and localization are isomorphisms. Finally
naturality across D ≅ quotient C transports the localized conclusion to D.
The empty finite product is a zero object and gives the same conclusion.
This makes no assertion for arbitrary complexes without hterms. -/
theorem affineAlternatingCech_resolution_exchange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (D : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
    (hterms : ∃ C : CochainComplex
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        Nonempty (D ≅ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ∧
        ∀ k : ℤ, ∃ (n : ℕ) (W : Fin n → X.Opens),
          (∀ j, IsAffineOpen (W j)) ∧
          Nonempty (C.X k ≅ ∏ᶜ fun j : Fin n ↦
            (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι))) :
    IsIso ((DerivedCategory.Qh (C := SheafOfModules.{u}
      (moduleRings (Spec B).toRingedSpace))).map
      ((moduleHomotopyBaseChange f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).app D)) := by
  classical
  obtain ⟨C, ⟨e⟩, hC⟩ := hterms
  let F := Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g
  let H := Scheme.Modules.tensorPullback (pullback.fst f g) ⋙
    Scheme.Modules.pushforward (pullback.snd f g)
  let α : F ⟶ H :=
    { app := Scheme.Modules.moduleBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition
      naturality := fun _ _ a ↦ Scheme.Modules.moduleBaseChangeMap_naturality
        f (pullback.snd f g) g (pullback.fst f g) pullback.condition a }
  have hα (k : ℤ) : IsIso (α.app (C.X k)) := by
    obtain ⟨n, W, hW, ⟨eW⟩⟩ := hC k
    let T : Fin n → X.Modules := fun j ↦
      (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι)
    have (j : Fin n) : IsIso (α.app (T j)) :=
      affineOpen_pushforward_exchange f g G (W j) (hW j)
    have eq : α.app (∏ᶜ T) ≫ piComparison H T =
        piComparison F T ≫ Limits.Pi.map (fun j ↦ α.app (T j)) := by
      apply Pi.hom_ext
      intro j
      simp only [Category.assoc, piComparison_comp_π, Pi.map_π]
      rw [← Category.assoc, piComparison_comp_π]
      exact (α.naturality (Pi.π T j)).symm
    have : IsIso (α.app (∏ᶜ T) ≫ piComparison H T) := by
      rw [eq]
      infer_instance
    have : IsIso (α.app (∏ᶜ T)) :=
      (isIso_comp_right_iff _ (piComparison H T)).mp inferInstance
    exact (NatTrans.isIso_app_iff_of_iso α eW).mpr inferInstance
  have (k : ℤ) : IsIso (((NatTrans.mapHomologicalComplex α
      (ComplexShape.up ℤ)).app C).f k) := hα k
  have : IsIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app C) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hq : IsIso ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) := by
    change IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app C))
    infer_instance
  have : IsIso ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app D) :=
    (NatTrans.isIso_app_iff_of_iso _ e).mpr hq
  have : IsIso ((moduleHomotopyBaseChange f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition).app D) := by
    dsimp only [moduleHomotopyBaseChange, NatTrans.comp_app]
    change IsIso (_ ≫ (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app D ≫ _)
    infer_instance
  infer_instance
end AlgebraicGeometry

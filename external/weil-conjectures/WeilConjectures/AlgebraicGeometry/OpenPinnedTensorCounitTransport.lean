/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle
import WeilConjectures.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem transport_counit_comparison
    {I C D : Type*} [Category C] [Category D]
    (A : I → D) (B : I → C) (Q : C ⥤ D) (ε : ∀ i, A i ⟶ Q.obj (B i))
    {i j : I} (h : i = j) {E F : C}
    (a : B j ⟶ E) (b : E ⟶ F) (c : B i ⟶ F)
    (hc : a ≫ b = eqToHom (congrArg B h).symm ≫ c) :
    eqToHom (congrArg A h) ≫ ε j ≫ Q.map a ≫ Q.map b = ε i ≫ Q.map c := by
  cases h
  simp only [eqToHom_refl, Category.id_comp] at hc ⊢
  rw [← Q.map_comp, hc]

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Transport and termwise tensor composition in a commuting open square.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-tensor-counit-transport).
Proof: the source and target homotopy comparison isomorphisms are the two
termwise paths from tensor pullback along the composite to restriction
followed by tensor pullback. Expand openPinnedTensorRestrictionIso into its
four factors. The target comparison cancels its inverse composition and
inverse open tensor comparison, leaving the source comparison, with transport
along hj. The functor from additive functors to homotopy functors preserves
these compositions and inverses, as does Qh. The counit family respects
transport along equality of scheme morphisms by equality induction. Combine
that transport identity with the termwise comparison identity. No derived
composition comparison, derived open-pullback comparison, or flatness of P
is used. Empty opens and zero complexes obey the same functor identities. -/
theorem open_pinned_tensor_counit_transport
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (pinnedPullbackCounit.{u, w} (j ≫ U.ι)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopySourceCompositionIso U j).hom.app P) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact transport_counit_comparison
    (fun f : U'.toScheme ⟶ X ↦ (derivedPullback.{u, w} f).obj (DerivedCategory.Qh.obj P))
    (fun f ↦ ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P)
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace)))
    (fun f ↦ (pinnedPullbackCounit.{u, w} f).app P) hj _ _ _
    (open_pinned_tensor_comparison_coherence k U U' j hj P)

end AlgebraicGeometry

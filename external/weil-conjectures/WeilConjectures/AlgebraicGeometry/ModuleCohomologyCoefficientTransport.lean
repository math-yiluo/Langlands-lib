/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientFactor
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtCoefficientFactor

/-! # Transport of coefficient naturality through the edge comparison

Source: Stacks Project, Tags 01FB and 01F7.
(blueprint: new-module-cohomology-coefficient-transport)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Naturality and compatibility for the identity edge coefficient imply compatibility
for an arbitrary coefficient morphism, on each cohomology class.

Source: Stacks Project, Tags 01FB and 01F7, functoriality in coefficients.
(blueprint: new-module-cohomology-coefficient-transport)

Proof: Factor the module h-map as the module cohomology map of the coefficient
morphism followed by the edge map. Apply edge compatibility to this class, then
coefficient naturality of E. The Ext coefficient factorization identifies the
result with exact inverse image followed by the adjoint coefficient map. Equality
transitivity combines these four steps. The maps E and E' need not be equivalences;
only the displayed naturality and edge equalities are used. -/
theorem moduleCohomology_transport_coefficient
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (F : X.Modules)
    (φ : N ⟶ (pushforward f).obj F) (p : ℕ)
    (E : ∀ M : Y.Modules,
      (RingedSpace.moduleCohomology Y.toRingedSpace p).obj M → H (X := Y) M p)
    (E' : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F → H (X := X) F p)
    (hnat : ∀ x, E ((pushforward f).obj F)
      (((RingedSpace.moduleCohomology Y.toRingedSpace p).map φ).hom x) =
        H.map (X := Y) φ p (E N x))
    (hedge : ∀ x, E' (moduleCohomologyEdgeMap f F p x) =
      Sheaf.H.map (coeff (X := X) (Y := Y) (M := (pushforward f).obj F) (N := F)
        f (𝟙 ((pushforward f).obj F))) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p
          (E ((pushforward f).obj F) x)))
    (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj N) :
    E' (moduleCohomologyFMap (X := X) (Y := Y) (G := N) (F := F) f φ p x) =
      Sheaf.H.map (coeff (X := X) (Y := Y) (M := N) (N := F) f φ) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) p (E N x)) := by
  have hm := moduleCohomology_coefficient_factor
    (X := X) (Y := Y) (N := N) (F := F) f φ p x
  have hc := moduleCohomology_ext_coefficient_factor
    (X := X) (Y := Y) (N := N) (F := F) f φ p (E N x)
  have hn := hnat x
  dsimp only [H.map] at hn
  exact (congrArg E' hm).trans ((hedge _).trans
    ((congrArg (fun y : H (X := Y) ((pushforward f).obj F) p ↦
      Sheaf.H.map (coeff (X := X) (Y := Y)
        (M := (pushforward f).obj F) (N := F) f (𝟙 ((pushforward f).obj F))) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p y))
      hn).trans hc))


end AlgebraicGeometry.Scheme.Modules

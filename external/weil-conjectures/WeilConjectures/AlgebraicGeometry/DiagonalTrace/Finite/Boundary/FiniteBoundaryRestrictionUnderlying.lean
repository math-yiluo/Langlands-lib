/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison

/-! The concrete comparison between restricted and finite evaluation presentations. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local implicit_reducible] AlgebraicGeometry.ProEtale.spCoefficientCommRings
  AlgebraicGeometry.ProEtale.SpTowerShriek.tau
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
attribute [local irreducible] CategoryTheory.constantSheaf Padic
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
attribute [local irreducible] WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- The restricted evaluation of a diagonal system agrees with its finite
evaluation: componentwise the identity transport along `r.underlying`, natural by
`r.restrictions` and `r.morphisms` through
`SpTowerClasses.finiteBoundary_transport_addHom`.
(blueprint: def-diagonal-local-finite-boundary-restriction-underlying) -/
noncomputable def finiteBoundaryRestrictionUnderlying (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ) :
    r.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙
        diagonalForget l T ≅
      SpTowerShriek.ev l (ULift.{u} (Padic l)) T n ⋙
        finiteForget l (ULift.{u} (Padic l)) T n := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ eqToIso (r.underlying M n U)) ?_)) ?_
  · intro U V a
    apply finiteBoundary_transport_addHom (r.underlying M n U) (r.underlying M n V)
    exact r.restrictions M n a
  · intro M N a
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply finiteBoundary_transport_addHom (r.underlying M n U) (r.underlying N n U)
    exact r.morphisms a n U

end AlgebraicGeometry.ProEtale.DiagonalTrace

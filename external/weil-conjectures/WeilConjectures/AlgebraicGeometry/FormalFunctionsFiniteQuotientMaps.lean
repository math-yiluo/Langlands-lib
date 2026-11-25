/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoicesExist
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization

/-! # Finite pullback of the local germ formula

Source: Stacks Project, Tags 02OD, 01F7, 01FB and 01E4.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-maps)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
noncomputable section

-- Compare cohomology h-maps by their interfaces, without unfolding chosen resolutions.
attribute [local irreducible] Scheme.Modules.moduleCohomologyFMap

-- The coherence hypothesis belongs to the existing interface; this compatibility is formal.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composing the local germ formula with canonical finite-level pullback gives theta.
Source: Stacks Project, Tag 02OD, factorization c_n through c; Tags 01F7, 01FB, 01E4.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-maps)

Proof: Fix the prescribed finite choices D and choose an injective resolution K of F'.
The local spectrum map and its base change are flat, so the open-choice existence
theorem gives local choices E₀. Set E to E₀ with its source field replaced by D.source.
The psi, target and unit_square fields do not depend on source, so E is valid and the
germ in the local comparison formula is definitionally the germ required by Theta.
Apply the finite-open factorization theorem to E and D, obtaining an additive map t
with its restriction and restricted-pullback equations. Apply t to ha on this germ.
Its restriction equation identifies the left side with restriction after canonical
finite pullback; its restricted-pullback equation identifies the right side with the
finite restricted h-map applied to xi. Substitute hr at a(germ) and evaluate linear-map
composition. This is the defining Theta equality for every I, J, V, hy, D and xi. No
surjectivity of r or equivalence property of a is needed. For zero coefficients or
empty fibre all maps are zero; in degree zero this is composition of section pullbacks.
There is no quotient-system isomorphism or completed module in this argument. -/
theorem formalFunctions_finite_quotient_maps {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p n : ℕ)
    (r : formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n)
    (hr : ∀ z, r z = formalFunctionsFinitePullback f y F p n z)
    (a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
      formalFunctionsLocalCohomology f y F p)
    (ha : IsFormalFunctionsLocalComparison f y F p a) :
    IsFormalFunctionsTheta f y F p n (r.comp a) := by
  classical
  have : Flat (Y.fromSpecStalk y) :=
    (Scheme.fromSpecStalk_local_properties Y y).2.2.2.2.2
  have : Flat (pullback.snd (Y.fromSpecStalk y) f) := inferInstance
  have : EnoughInjectives (pullback (Y.fromSpecStalk y) f).Modules :=
    Scheme.Modules.enoughInjectives (X := _)
  intro I J V hy D xi
  let K := injectiveResolution
    ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
  let E₀ := Classical.choice (Scheme.Modules.flatBaseChangeMap_sections_choices
    f (Y.fromSpecStalk y) F I K V)
  let E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V :=
    { E₀ with source := D.source }
  have hfac := formalFunctions_finite_open_factorization f y F p n I K J V E D
  let t := hfac.choose
  have ht := hfac.choose_spec.1
  have htx := hfac.choose_spec.2
  have hl := ha I K V hy E xi
  let rho := Scheme.Modules.moduleCohomologyRestriction
    ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) p
  refine (congrArg rho (hr _)).trans ?_
  exact (ht _).symm.trans ((congrArg t hl).trans (htx xi))


end
end AlgebraicGeometry

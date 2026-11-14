/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions

/-!
# The class-formation cohomology bridge: data

Modified by Worker 5454: extract five data definitions from the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`:
M114.002 `LocalClassFieldTheory.additiveFixedUnitsEquivInvariants` (lines 60–73),
the private M114.004 `additiveHomToMultiplicativeHom` (lines 85–90), M114.005
`multiplicativeQuotientGroup` (lines 92–99) and M114.006
`kernelOfAdditiveQuotientHom` (lines 101–107), and M114.019
`LocalClassFieldTheory.unitsRhoSubToNormKerLinearMap` (lines 290–307).
Prefix the public names with `Langlands.NYLL`; the three private source
definitions become the public `Langlands.NYLL.PortInternal.M114.d004`, `.d005`
and `.d006` (the call of `multiplicativeQuotientGroup` inside M114.006 becomes
`d005`) and are placed in their own namespace block, outside the section
variables of source line 33, which they do not use. The source's Mathlib import
is kept; its NYLL imports are replaced by the M095 data module of this port
(`unitsNormLinearMap`, `unitsInvariantSubmodule`) and the published M113 data
module (`fixedSubgroup`). The constructions, proof fields, attributes, binder
kinds and universes are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.PortInternal.M114

/-- Multiplicative form of an additive homomorphism, kept polymorphic for the
same elaboration reason as `additiveEquivToQuotientHom`. -/
def d004
    {G B : Type} [Group G] [AddCommGroup B]
    (f : Additive G →+ B) : G →* Multiplicative B :=
  AddMonoidHom.toMultiplicativeRight f

/-- The multiplicative group structure on an additive submodule quotient.
This is passed explicitly at concrete call sites to avoid rediscovering it by
unfolding the coefficient representation. -/
@[implicit_reducible]
def d005
    {M : Type} [AddCommGroup M] (N : Submodule ℤ M) :
    Group (Multiplicative (M ⧸ N)) :=
  Multiplicative.group

/-- Kernel of a homomorphism into a multiplicative additive quotient, with the
codomain structure supplied directly. -/
def d006
    {G M : Type} [Group G] [AddCommGroup M]
    (N : Submodule ℤ M) (f : G →* Multiplicative (M ⧸ N)) : Subgroup G :=
  @MonoidHom.ker G inferInstance (Multiplicative (M ⧸ N))
    (d005 N).toMulOneClass f

end Langlands.NYLL.PortInternal.M114

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Multiplicative fixed units and the invariant submodule of the actual unit
representation are the same additive group. -/
def additiveFixedUnitsEquivInvariants :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) ≃+
      unitsInvariantSubmodule K L where
  toFun x := ⟨Additive.ofMul ((Additive.toMul x : fixedSubgroup (Gal(L / K)) Lˣ) : Lˣ), by
    intro σ
    exact congrArg Additive.ofMul ((Additive.toMul x).property σ)⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    intro σ
    exact Additive.ofMul.injective (x.property σ)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- The actual additive differential `ρ(g)-1`, with codomain restricted to
the kernel of the norm. -/
def unitsRhoSubToNormKerLinearMap [Fintype (Gal(L/K))]
    (g : Gal(L/K)) :
    Additive Lˣ →ₗ[ℤ] LinearMap.ker (unitsNormLinearMap K L) :=
  ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id).codRestrict
    (LinearMap.ker (unitsNormLinearMap K L)) (by
      intro x
      change unitsNormLinearMap K L
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      change (Rep.ofAlgebraAutOnUnits K L).norm.hom
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      change Representation.norm (Rep.ofAlgebraAutOnUnits K L).ρ
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x) =
          Representation.norm (Rep.ofAlgebraAutOnUnits K L).ρ x
      exact Representation.norm_self_apply (Rep.ofAlgebraAutOnUnits K L).ρ g x)

end

end Langlands.NYLL.LocalClassFieldTheory

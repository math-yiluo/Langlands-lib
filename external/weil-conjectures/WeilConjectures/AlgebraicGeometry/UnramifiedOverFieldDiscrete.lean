/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Discreteness of a scheme unramified over a field

Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field),
part (1), topological part of the only-if direction
(blueprint: lem-weil-pbc-unramified-over-field-discrete).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme unramified over a field has discrete underlying topological space.
Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field), part (1)
(blueprint: lem-weil-pbc-unramified-over-field-discrete).

Proof: On every pair of affine opens mapped into one another, local finite type gives
`Algebra.FiniteType` on the section rings. The open diagonal gives formal unramifiedness
of the morphism and hence `Algebra.FormallyUnramified` on those rings. Mathlib's instance
in `RingTheory.Unramified.LocalStructure` gives `Algebra.QuasiFinite`, establishing
Mathlib's `LocallyQuasiFinite g` directly. Since a field is Artinian, its spectrum is
locally Artinian. Apply `IsLocallyArtinian.of_locallyQuasiFinite g` to obtain that `Y`
is locally Artinian, then the instance `IsLocallyArtinian.discreteTopology`. This is
an implementation of the locally quasi-finite route in Stacks 02G7 using Mathlib's
Artinian-scheme results; no comparison with the project's quasi-finiteness predicate
or transport through the scheme-theoretic fibre is needed. -/
theorem discreteTopology_of_unramified_over_field {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType g] [IsOpenImmersion (pullback.diagonal g)] :
    DiscreteTopology Y := by
  have : LocallyQuasiFinite g := by
    constructor
    intro U hU V hV e
    let := (g.appLE U V e).hom.toAlgebra
    have : Algebra.FiniteType Γ(Spec (CommRingCat.of k), U) Γ(Y, V) :=
      g.finiteType_appLE hU hV e
    have : Algebra.FormallyUnramified Γ(Spec (CommRingCat.of k), U) Γ(Y, V) :=
      g.formallyUnramified_appLE hU hV e
    exact (inferInstance : Algebra.QuasiFinite Γ(Spec (CommRingCat.of k), U) Γ(Y, V))
  have : IsLocallyArtinian Y := .of_locallyQuasiFinite g
  infer_instance

end AlgebraicGeometry

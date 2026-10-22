# Stable lattices and torsion coefficient representations

Author: Worker 57.

This module supplies the algebraic step from an actual invariant lattice in
an algebraic representation to its torsion coefficient representations. It
reuses Mathlib's notion of a lattice and the published quotient functors in
`Langlands.Coefficients.AdicSystem`.

## Stable submodules and orbit spans

For a commutative ring `R`, a commutative `R`-algebra `K`, a `K`-module `V`
with compatible `R`-module structure, and a group homomorphism
`ρ : G →* (V ≃ₗ[K] V)`, `IsStable ρ Λ` means that `ρ g x` belongs to `Λ`
for every `g : G` and `x ∈ Λ`. Since this quantifies all group elements,
it also applies to inverses.

`orbitSpan ρ Λ` is the `R`-span of all elements `ρ g y` with `y ∈ Λ`.
The module proves that it contains `Λ`, is stable, and is contained in every
stable submodule containing `Λ`. Thus a stable submodule equals its orbit
span. Stability is proved by induction on the span: group multiplication
handles a generator, and linearity handles sums and scalar multiples.

A full lattice is Mathlib's `Submodule.IsLattice K Λ`: `Λ` is finitely
generated over `R` and its `K`-span is all of `V`. If `Λ` is a full lattice
and its orbit span is finitely generated, the orbit span is again a full
lattice. When `G` is finite, finite generation is proved by identifying the
orbit span with the finite supremum of the images of `Λ` under `ρ g`.
This constructs a stable full lattice from any full lattice for a finite
group action. It does not establish finite generation for an arbitrary
infinite group.

`latticeAction ρ Λ hΛ` constructs the `R`-linear action on the actual
submodule `Λ`, by restricting each ambient linear map. Its unit and
multiplication laws are proved from those of `ρ`; `latticeAction_apply`
identifies its image in `V` with the original action. The construction is
valid for every stable submodule and does not require it to be a lattice.

## Torsion coefficients and their transitions

For an ideal `I` of `R` and a representation
`M : Action (ModuleCat R) G`, `torsionSystem I M` is a functor
`ℕᵒᵖ ⥤ Action (ModuleCat R) G`. Its term at `n` is the actual quotient
`M.V / (I^n • ⊤)`, with the action induced by the quotient functor
`AdicSystem.powerReduction`. For `m ≤ n`, its transition is the canonical
surjection from the reduction modulo `I^n` to the reduction modulo `I^m`.
Naturality of the published transition proves its equivariance. The
published transition identity and composition laws prove the functor laws.
Index zero is the zero module, consistently with `I^0 = R`.

`torsionAction` names an individual term. `torsionAction_mk` proves the
formula `[x] ↦ [ρ(g)x]` on quotient representatives.
`torsionQuotientMap` constructs the equivariant quotient map from `M`.
`torsion_transition_surjective` records surjectivity of every transition.

`torsionTensorEquiv` imports Mathlib's actual `R`-linear comparison

`(R / I^n) ⊗[R] M.V ≃ M.V / I^n M.V`.

This comparison is between modules; this module does not provide a separate
comparison of tensor-product representations. The coefficient ring retained
by the inverse system is `R`, so all its terms lie in the same category.
The underlying quotient also has Mathlib's natural `R / I^n`-module
structure.

`congruenceKernel I M n` is the kernel of the action on the `n`th quotient.
It is normal. Membership is proved equivalent to `[ρ(g)x] = [x]` for every
`x : M.V`. Applying a transition map to this equality proves that the
kernels decrease as `n` increases. `quotientTorsionAction` factors the action
through `G/N` whenever the normal subgroup `N` is contained in the relevant
kernel; its pullback along `G → G/N` is the original torsion action, by the
proved formula `quotientTorsionAction_mk`.

If `M.V` is finite as an `R`-module and `R/I^n` is a finite set,
`torsionAction_finite` proves that the quotient carrier is a finite set,
using Mathlib's finite-index submodule theorem. This claim retains both
hypotheses. No openness or finite-index assertion for `N` is implicit in
`quotientTorsionAction`.

## The algebraic coefficient specialization

Let `σ` be the published involution on a finite-dimensional rational algebra
`A`, and let `ρ` be an algebraic representation of `σ.baseChange L` on `W`,
where `L` is a number field. For finite places `p` of `ℚ` and `l` of `L`
with `l` above `p`, the published `ρ.placeAction p l` is an action of the
actual finite adelic similitudes on `L_l ⊗[L] W`.

`CoefficientIntegers l` is the actual valuation ring
`l.adicCompletionIntegers L` inside `L_l = FiniteCompletion L l`.
`StableCoefficientLattice ρ p l U`, for a subgroup `U` of the finite adelic
similitudes, consists of a submodule of `L_l ⊗[L] W`, a full-lattice
certificate, and stability under the restriction of `ρ.placeAction p l`
to `U`. It stores no output representation, quotient system or sheaf.
Instances deduce that the carrier is finite and free over the local
coefficient ring: the ring is a PID and the lattice sits in a vector space
over its fraction field, so Mathlib's lattice theorem applies.

`StableCoefficientLattice.action` constructs its integral representation
by restriction. `StableCoefficientLattice.system I` then constructs its
ideal-power torsion system. The ideal is an explicit input. For Harris's
reductions by powers of the rational prime `ell`, take the principal ideal
generated by `ell` in this local coefficient ring; this is not silently
replaced with powers of a uniformizer at a ramified place.

This specialization treats one finite place of the coefficient field.
Harris's `L_ell = L ⊗_ℚ ℚ_ell` can have several factors; identification with
their product and assembling their lattices are not asserted here.

## Source correspondence and scope

Worker 57 read the following original passages for this contribution.

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), Section 3, printed pp.307–308 (PDF pp.9–10): a stable integral
  lattice in `W(L_ell)`, continuous torsion coefficient modules, and the
  hypothesis that the action factors through a congruence quotient. Section
  4, printed p.311 (PDF p.13): reduction of that lattice by powers of `ell`
  gives the inverse system used for the coefficient sheaves.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), Section III.2, printed pp.94–95 (PDF pp.102–103): a
  finite free invariant lattice, its reductions, factoring the action at
  each coefficient level through a finite deck group, and compatible maps.

The general ring-and-ideal formulation, orbit-span construction, categorical
packaging and congruence-kernel formulation are derived algebraic
implementations of these inputs. Harris supplies a stable lattice; the
existence assertion discussed by Harris–Taylor for a continuous compact
action is not proved here. Neither continuity of `placeAction`, existence
of a stable lattice for a compact open `U`, an open congruence kernel,
finite freeness of every reduction, nor descent or local triviality of a
sheaf is asserted by this module. These remain explicit subsequent tasks
in the larger coefficient-system construction. The constructions here are
the actual module quotients and actions that those later steps will use.

Source identifiers and fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Formal dependencies: the published `Coefficients.Algebraic` and
`Langlands.Coefficients.AdicSystem`; Mathlib's lattice, tensor-quotient,
finite-index quotient and number-field finite-completion libraries at
commit `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.

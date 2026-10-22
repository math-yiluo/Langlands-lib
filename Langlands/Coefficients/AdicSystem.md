# Coefficient reductions and inverse systems

Author: Worker 13.

For a commutative ring `R`, an ideal `I`, and an actual `R`-module `M`, this
module constructs the inverse system `M / I^n M`, with reduction maps from
index `n` to index `m` when `m <= n`. The indexing category is the opposite of
the natural-number preorder. Index zero is the zero module; the positive
indices are the usual coefficient levels.

`reduction I` changes coefficients to `R / I` using Mathlib's quotient module
and induced quotient-linear maps. `powerReduction I n` retains the original
`R`-module structure of the reduction by `I^n`. Their identity and composition
laws are proved on quotient representatives. `transition` uses Mathlib's
`Submodule.factorPow`; naturality, composition, identity and surjectivity are
proved. The resulting functor sends a module homomorphism to a compatible
family of maps on all its reductions.

The original module maps to this system by the quotient maps. The actual
module of compatible sequences is Mathlib's `AdicCompletion I M`. Its
evaluation maps form `completionCone`. The code proves the categorical limit
property: a cone induces the unique map taking an element to its compatible
sequence of images. No assertion that `M` equals this limit, or that this
completion is itself adically complete for an arbitrary ideal, is assumed.

An existing Mathlib action on `M` is transported through the constructed
functor, so every group or monoid operator acts on the entire system and
commutes with all transitions. This is an algebraic action. It neither
constructs a new representation category nor asserts continuity, smoothness,
or descent on a space with a moving group action.

The source motivation is Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), pp.299-318:
section 3, pp.307-308 (stable lattices and coefficients modulo powers of
`ell`), and section 4, p.311 (the inverse system preceding Proposition 4.10).
Worker 13 read these original pages. This implementation is a derived
generalization to arbitrary modules and ideals. For `R = O` and
`I = (ell)`, its terms give the quotient presentation of the source's lattice
reductions. An explicit tensor-quotient comparison, finite-freeness,
continuous action, and descent to the lisse sheaf on the required Shimura
variety remain separate obligations.

Source registration:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`;
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
The supplied member is
`Harris (1999), Galois properties of cohomological automorphic forms on GL(n).pdf`.

Formal dependencies are Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, notably
`AdicCompletion.Functoriality`, `ModuleCat.ChangeOfRings` and `Action.Basic`.
Ring, module and action-monoid universes are explicit and independent.
The construction has no characteristic, finite-generation or project-axiom
assumption.

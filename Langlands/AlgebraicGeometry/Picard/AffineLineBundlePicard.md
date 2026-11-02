# Actual affine line-bundle trivializations from module Picard vanishing

This internal construction supplies a dictionary from the actual module
Picard group of a commutative ring to actual line bundles on its spectrum.
It uses existing Library line bundles and their tensor inverses, not an
abstract replacement for the given bundle.

For an actual line bundle on any affine scheme, the module of global
sections is invertible over the actual global function ring. The proof
uses the published ported theorem
`Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2`:
for two locally trivial rank-one sheaves, tensoring sections on an affine
open gives the sections of their ported tensor. The restriction/pullback
comparison shows that a Library line bundle satisfies the theorem's
local-triviality predicate. `portedTensorExplicitIso` identifies that
ported tensor with the Library's explicit sheaf tensor: each is the
sheafification of the same sectionwise tensor. Taking the actual chosen
inverse line bundle and its evaluation isomorphism therefore gives a
linear equivalence from the tensor of their section modules to the ring.
Mathlib's `Module.Invertible.left` proves invertibility of the original
section module.

For a line bundle on `Spec R`, triviality of the module Picard group of
`R` transports along the canonical equivalence between `R` and the actual
global function ring. Mathlib's characterization of free invertible
modules yields a basis of rank one over that function ring. Restricting
scalars to `R` and composing with the inverse canonical coefficient
equivalence gives an actual `R`-linear equivalence from the
`moduleSpecΓFunctor` module of the original bundle to `R`. The affine
associated-sheaf equivalence for quasi-coherent sheaves, applied to the
given locally free rank-one sheaf, carries this to an actual sheaf
isomorphism with the structure sheaf.
`affineLineBundleTrivialization` chooses that isomorphism.

The construction is derived internally from the imported Library and
Mathlib theorems. It adds no Noetherian, domain, valuation, dimension, or
connectedness assumptions. It does not prove that a generic-fibre line
bundle extends to a total scheme.

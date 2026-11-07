# Conditional assembly of the actual norm-kernel small progenerator

`RationalNormKernelSmallProgeneratorReductionStatement` states that the existing
`IsRationalNormKernelSmallProgenerator G π` follows from three explicit structural
inputs. `rationalNormKernelSmallProgeneratorReduction` proves this conditional
statement. The field universe `uF` and original representation-carrier universe
`uV` are independent.

The setting is a nonarchimedean local field, an affine group scheme locally of
finite type, its canonical rational-point topology, local compactness and a
nonarchimedean rational-point group. The quantified group is connected reductive
and `π` is irreducible. The three additional inputs are:

- Compact smooth-dual coefficients of the entire restriction of `π` to
  `rationalCommonNormKernel G`.
- `RationalNormKernelFiniteRestrictionStatement.{uF, uV}`.
- `RationalNormKernelTwistEquivalenceStatement` with both representation-carrier
  universes equal to `max uF uV`.

These inputs are not proved in this module. In particular, the conditional
statement is separate from the existing unconditional
`RationalUniversalSmallProgeneratorStatement`. That target, its structural
binders and its Lean/Markdown pair are unchanged. The conditional conclusion
does not need a separate cuspidality premise once the three displayed inputs
are supplied; this does not assert compact restriction for every irreducible
representation.

The conclusion uses the actual compact induction of the full restriction,
with its original function carrier and action. Its block is exactly
`RationalInertiaBlock G (rationalInertiaBaseLift G π)`. The Hom functor is the
existing integer-module-valued `preadditiveCoyonedaInt` of that object. All
coproduct indices have type `Type (max uF uV)`.

The proof first applies `rationalNormKernelCompactInduction_mem_of_restriction`
to obtain membership in that block. This published helper uses the finite
restriction family and compact-coefficient projectors to control every actual
irreducible subquotient of the induction, transports its nonzero restricted
map to the actual lifted base, and applies the supplied twist-equivalence
criterion. The assembly uses precisely the resulting membership witness.

For an epimorphism in the block and a map from the induced object, the published
`rationalNormKernelBlockProjectiveLift` supplies a lift and
`rationalNormKernelBlockProjectiveLift_comp` supplies the required composition
identity. `rationalNormKernelHom_faithful` gives faithfulness of the specified
integer Hom functor, using the same membership witness and compact restriction
input. `rationalInertiaBlock_hasColimitsOfShape` provides the actual block
coproducts for each required index type.

Finally, the proof extracts finite composition length of the full restriction
from the second conjunct of the finite-restriction input.
`rationalNormKernelHom_preservesCoproducts_of_finiteLength` then gives
preservation of every required coproduct by the same integer Hom functor. The
five results are inserted directly into `IsRationalNormKernelSmallProgenerator`.
No abelian block instance is assumed.

This is an internal composition of the published membership, projectivity,
generation, inertia-coproduct and finite-generation smallness APIs, based on
Worker 1740's private integration example and prepared jointly with Worker 1594.
The underlying source motivation is the full-restriction alternative object in
Renard VI.4.1, already represented by the existing unconditional target. This
module establishes only the stated reduction; proving the three structural
inputs in the original cuspidal scope remains necessary for that target.

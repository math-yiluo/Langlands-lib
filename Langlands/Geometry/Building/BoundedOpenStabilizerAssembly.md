# Assembling bounded open stabilizers on the actual quotient

This internal conditional assembly proves the exact existing
`HasBoundedOpenStabilizers` predicate from the stated sharp-fixer, centralizer
and parahoric-openness inputs. It works over every nonarchimedean local field at
every universe `u`, on the original `ReducedBuilding` and rational-point action.
The topology is precisely `rationalPointTopology F G.X` and boundedness is the
existing KP algebraic boundedness predicate.

At an original apartment point, the original quotient's exact stabilizer formula
writes every fixer element as `p * n`, with `p` in the singleton sharp fixer and
`n` in the actual normalizer fixing the apartment point. V7 puts the sharp fixer
in the actual rational character norm kernel. Intersecting the product with
that kernel therefore gives exactly the sharp fixer times the norm-one
normalizer stabilizer. The latter is bounded by the published finite-relative-
Weyl-coset argument whenever the image of the centralizer norm kernel is
bounded. The product of these two bounded sets is bounded.

An open actual point parahoric lies in the norm-one point stabilizer by the
published fixer comparison. Thus the stabilizer is open. The wrapper obtains
point-parahoric openness from the existing open-root-generation theorem target,
V7 and openness of the actual centralizer-zero subgroup. It retains the
open-root-generation and centralizer-zero-openness proofs as explicit inputs;
it does not assert them unconditionally.

For every other quotient point the existing representative theorem writes it
as `g` times an apartment point. Normality of the actual character norm kernel
and the original group-action laws identify its stabilizer with the conjugate
of the apartment stabilizer. Left/right multiplication are homeomorphisms in
the canonical point-group topology, so openness transports. Conjugation is
also a left and right translate of a bounded set, so boundedness transports.
No injectivity of the apartment map or choice of a new quotient carrier is
needed.

`boundedOpenStabilizerData` bundles each original norm-one fixer as an actual
open subgroup with algebraic boundedness and equality of its underlying
subgroup to the existing stabilizer. Its inputs are supplied parahoric-building
data, the full existing apartment predicate, singleton sharp-fixer boundedness,
boundedness of the image of the actual centralizer norm kernel, the actual
open-root/centralizer generation statement and canonical openness of the
centralizer-zero subgroup. All remain explicit. This unit fills the assembly
step for KP 4.1.2; it neither constructs general building data nor discharges
these structural inputs or the unrestricted parent construction theorem.

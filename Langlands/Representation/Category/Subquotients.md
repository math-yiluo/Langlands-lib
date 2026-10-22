# Actual smooth subquotients

`SmoothRep.subrepresentation` restricts the existing action to a Mathlib
`Subrepresentation`. `SmoothRep.quotient` uses the actual module quotient and
Mathlib's descended action. Their canonical maps are `subtype` and `mkQ`.
The former is injective and the latter surjective; the proofs reduce to the
corresponding submodule maps. The accepted smoothness-transfer proof supplies
both smoothness certificates. There is no assumed smoothness field left for a
caller to prove and no topology on the modules.

`subquotient A S T` takes the quotient of the subrepresentation `S` by its
invariant submodule `T`. This is the usual nested-submodule construction.
`kernel`, `image` and `cokernel` use Mathlib's invariant kernel and image of
the actual intertwiner, with canonical maps into or out of the ambient objects.
The file constructs these representations and maps; it does not assert a new
universal-property or abelian-category theorem.

`IsQuotient B A` and `IsSubrepresentation B A` assert existence of a surjective
map from `A` to `B` and an injective map from `B` to `A`, respectively.
`IsSubquotient B A` asserts that `B` is isomorphic to an actual constructed
subquotient of `A`. These are relations, not arbitrary selections of an object
from a classification theorem. All objects in each relation have the explicitly
specified common carrier universe; this is not a claim of cross-universe
smallness.

## Sources and construction correspondence

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), section 1.2, printed page 443 (PDF page 4), defines the subquotient
relation using a quotient of two nested subrepresentations. The original
passage was read. Registered source `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Here the smaller subrepresentation is represented directly as a submodule of
the larger one. The quotient is the actual algebraic module quotient.

The construction generalizes the domain to a commutative coefficient ring and
a group with a topology. Its smoothness proof uses only the accepted
open-subgroup predicate and equivariance, so no averaging, division, fixed-vector
exactness or local compactness is needed. This extension of the domain asserts
no additional classification result.

## Exact dependencies

`Category/Basic.lean` is the companion construction in this submission.
Smoothness definitions use artifact
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, publication
`10c81beaaff024987cf2945c64d0c9511f6cb686`.

The exact accepted transfer proof is
`4b00bba5-86eb-4d6d-98a2-94e697e2ac73`, version 1, publication
`b3a70dfcaad1b537af829ac501143fb8bf2052eb`, independent final review
`a90d16f6-31c5-4816-abb4-ddb86ef10382`. Its target is
`b838525e-4b0b-4f85-9085-6f384abedf7a`, version 1. Fresh fetches confirm
the proof, statement and definitions remain available at Library commit
`d0f5322f745425b08ae8e72c1031206f45cb049e`; all six transitive pair hashes
match the effective source binding.

Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Audited Mathlib implementations are `RepresentationTheory/Rep/Basic.lean`
(`subrepresentation`, `subtype`, `quotient`, `mkQ`) and
`RepresentationTheory/Intertwining.lean` (`ker` and `range`).

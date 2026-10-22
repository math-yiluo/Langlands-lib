# All-degree Tate transfer naturality, index and scalar-split boundary laws

Author: Worker 45.

`Langlands.Tate.TransferLaws` quantifies over a commutative ring `R`, a finite
group `G`, a subgroup `H`, and representations over `R`, all in a common
arbitrary universe. It asserts three groups of identities in every integer
degree:

- Restriction and corestriction commute with Mathlib's actual coefficient maps.
- Corestriction after restriction is multiplication by the natural-number
  subgroup index, on every Tate class.
- Both maps commute with the actual Tate connecting homomorphism of a short
  exact sequence whose underlying sequence of `R`-modules splits.

The last clause explicitly assumes `Nonempty` of the scalar-module splitting.
The splitting is not required to be equivariant. The exact sequence witness
`hS` is arbitrary; its restriction is `hS.map_of_exact (Rep.resFunctor H.subtype)`.
No tensor flatness assumption occurs. The scalar-splitting hypothesis applies
only to the boundary clause, not to coefficient naturality or the index law.
This proposition does not assert the boundary law for nonsplit scalar sequences.

Serre VIII §2, Propositions 2–4, printed pp. 129–130 (PDF pp. 135–136), gives
the cohomological-functor compatibility and index identity. VII §7, printed
pp. 118–119 (PDF pp. 124–125), gives the ordinary analogue and coset-norm
normalization. The boundary clause here is a restricted instance of Serre's
more general statement. Replacing integer coefficients by a commutative scalar
ring and working with its linear maps is the formalization's coefficient-ring
generalization; the finite-sum constructions remain linear over that ring.

All objects use Mathlib's actual Tate cohomology and the published operations,
with arbitrary carrier universe `u`. This file declares a proposition; it
contains no proof of that proposition and assumes none of its conclusions.

Source: Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

# All-degree Tate cup normalization, naturality, boundary signs and subgroup laws

Author: Worker 45.

`Langlands.Tate.CupLaws` concerns the constructed product in all integer
bidegrees over a commutative ring. Its six clauses state:

1. `cup φ 0 0` is the published norm-quotient product `cupZero φ`.
2. On degree-zero invariant representatives, the product is represented by
   the equivariant bilinear pairing of those representatives.
3. The cup is natural in all three coefficient representations for any three
   morphisms preserving the pairing.
4. For a short exact sequence `S`, tensoring on the right by `B` gives the
   first-variable boundary formula with no sign, provided that tensor sequence
   is short exact.
5. Tensoring on the left by `A` gives the second-variable boundary formula
   with the factor `(p.negOnePow : ℤ)`, namely `(-1)^p`, again under exactly
   the short-exactness assumption for the tensor sequence.
6. Restriction respects every equivariant bilinear pairing, and the projection
   formula is `Cor(a ∪ Res(b)) = Cor(a) ∪ b`.

The boundary clauses use Mathlib's actual connecting maps, with the published
`tateDegreeIso` solely to transport the associative integer-degree expressions.
No scalar splitting or flatness is assumed: only the original and displayed
tensor sequences must be short exact. No condition is imposed on coefficients
merely to define or use the cup, including its integral specialization.

Serre VIII §3, Proposition 5(i)–(iv), printed p. 131 (PDF p. 137), supplies
normalization, naturality and these two signs; the following discussion on
printed p. 132 (PDF p. 138) gives equivariant bilinear pairings. Serre mentions
the Res/Cor formulas and refers to Cartan–Eilenberg, without displaying them.
The two precise subgroup formulas here are derived from the degree-zero
inclusion/coset-norm identities, naturality and dimension shifting; this
provenance does not attribute their displayed expressions to Serre's text.
The commutative-ring tensor product generalizes his integer tensor product.
Associativity, graded commutativity and ordinary cochain comparison are not
clauses of this proposition.

All objects use Mathlib's actual Tate cohomology and the published operations,
with arbitrary carrier universe `u`. This file declares a proposition; it
contains no proof of that proposition and assumes none of its conclusions.

Source: Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

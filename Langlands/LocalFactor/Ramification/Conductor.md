# Finite ramification conductor expressions

For the actual congruence filtration `lowerGroup R G` from the paired
`Filtration` module and a finite-dimensional representation `rho` over a
field `k`, `conductorTerm R G rho i` is

`(|G_i| / |G_0|) * (dim V - dim V^(G_i))`,

as a rational number. The fixed subspace is the accepted
`Langlands.fixedVectors`, not an independently supplied dimension.
`artinConductor` sums the terms for `i >= 0`; `swanConductor` sums the
positive-index tail. Both use the inertia denominator `|G_0|`.

The definitions require a finite group acting faithfully by ring
automorphisms on a Noetherian local commutative ring. The preceding module
proves that its actual maximal-ideal congruence filtration terminates.
Once `G_i` is trivial, all vectors are fixed, so the codimension and the
summand vanish. This proves finite support for both sequences. The two
constructors sum over those proved finite supports. They do not use a
default value for an infinite sum or an arbitrary truncation parameter.
The finite-sum comparison lemmas show that any proved termination bound
gives exactly the same expressions.
The identity `artinConductor_eq_tame_add_swan` splits off the zeroth
summand. A finite group is nonempty, so its inertia cardinality is
positive and that summand is exactly the inertia-fixed codimension.

The formulas are invariant under representation equivalence: the accepted
`fixedVectorsEquiv` restricts the given equivalence to every fixed subspace,
so both the ambient dimension and the fixed dimension are preserved.
The coefficient field and two representation spaces occupy independent
universes.

These are rational expressions at this generality. No characteristic-zero
integrality theorem, finite-quotient independence, induction formula, or
comparison with a Weil representation is asserted here. The paired
`Galois` module constructs the specialization to the actual integer ring
and Galois action of a p-adic field extension, and also to its actual
inertia subgroup.

## Original sources and scope

Jean-Pierre Serre, *Local Fields* (1979), Chapter IV, Section 1, Lemma 1 and
Proposition 1, printed pages 61–62 (PDF pages 68–69), defines the lower
groups by their action on the integer-ring quotients. Chapter VI,
Section 2, Proposition 2 and Corollary 1', printed pages 99–101
(PDF pages 106–108), gives the weighted fixed-space codimension formula
for the Artin conductor. The present generic rational expression extends
the domain on which that formula can be formed; it does not extend
Serre's integrality theorem to arbitrary coefficient fields or ring
actions.

- Literature ID: `serre-1979-local-fields`.
- Retained file: `C:/Central-Library/Serre--Local Fields--1979.pdf`.
- SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions
L* (1973), Section 4.5, internal/PDF pages 37–38, separates the Swan
part from the inertia codimension in the Artin conductor. The positive
tail here is the corresponding weighted expression. Its identification
with the Swan character and independence of a finite inertia quotient
are separate obligations.

- Literature ID: `deligne-1973-local-constants`.
- Retained file:
  `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
- SHA256: `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

## Exact dependencies and status

The project fixed-vector dependencies are accepted, published version 1
artifacts `665022df-625b-44ae-9dbd-425f6e266bab` and
`7ad85b8b-caae-4345-ac1b-2c2d551dbb94`. Their current availability and
unchanged Lean/Markdown hashes were verified at Library commit
`9007729971e6e6ecea63b5567b6d1621769ccfb0`. The latter has review receipt
`7f5084d1-9e75-445b-b031-b754e38c4830`.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1;
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 40 authored this construction. It is submitted with `Filtration`
and `Galois` as one coherent contribution; independent review and
publication are separate from development compilation.

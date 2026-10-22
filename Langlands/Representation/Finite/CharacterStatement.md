# Finite complex character theory for Henniart

Worker 30 authored this proposition family. It states the finite-dimensional
complex character theory used before Henniart's integral virtual-lattice
argument. The closing proposition is
`Langlands.FiniteCharacterTheoryStatement`; this file does not prove it.
Its six reusable component proposition definitions are listed below.

## Objects and scope

`G` is an actual finite group, with a `Fintype G` enumeration. The two
carrier spaces `V` and `W` are finite-dimensional complex vector spaces.
The group and both carriers have three independent universes. The coefficient
field is specifically `ℂ`, the characteristic-zero field used in Henniart's
argument; this file does not claim a result over modular or nonsplitting
coefficient fields.

The Lean representations are Mathlib's `Representation ℂ G V`. For a group,
each action map is invertible because its inverse is the action of the
inverse group element. `Subrepresentation` is a genuine invariant linear
subspace, `Representation.directSum` is the actual direct-sum action,
and `Representation.Equiv` is a bundled intertwining linear equivalence.
No arbitrary predicate stands in for these objects, and equality of
characters is equality of the actual trace functions.

All representations are universally quantified inside the proposition
definitions. Irreducibility is an internal hypothesis only in the
orthogonality component; it is a conclusion in the decomposition and
norm-one components. Semisimplicity, character faithfulness, and
orthogonality are not structure fields or assumed instances.

## The proposition family

| Declaration after `Langlands.` | Content | Original location |
| --- | --- | --- |
| `FiniteCharacterNormalizationStatement` | Character at the identity is dimension; evaluation at an inverse is complex conjugation; conjugation in the group leaves the character unchanged; the dual character is evaluation at the inverse. | Serre §2.1, Proposition 1, pp.10–11; Exercise 2.3, p.12. |
| `FiniteCompleteReducibilityStatement` | Every invariant subspace has an invariant complement, and there is a finite direct sum of irreducible subrepresentations isomorphic to the original representation. | Serre §1.3, Theorem 1, pp.5–6; §1.4, Theorem 2 and its proof, p.7. |
| `FiniteCharacterHomDimensionStatement` | The normalized inverse-character pairing is the dimension of the space of intertwiners. | Derived from Serre §2.2, Proposition 4 and Corollary 1, pp.13–14; §2.3, Theorems 3–4, pp.15–16. See the derivation below. |
| `FiniteCharacterOrthogonalityStatement` | The pairing of two irreducibles is one when they are isomorphic and zero otherwise. | Serre §2.3, Theorem 3, p.15. |
| `FiniteCharacterIsomorphismStatement` | Two representations have equal trace characters if and only if they are isomorphic. | Serre §1.1, p.4, and §2.3, Corollary 2 to Theorem 4, p.16. |
| `FiniteCharacterNormOneStatement` | A genuine representation has normalized squared character norm one if and only if it is irreducible. | Serre §2.3, Theorem 5 and preceding sum-of-squares calculation, pp.16–17. |

`FiniteCharacterTheoryStatement` conjoins these components, applying the
one-carrier components to both `V` and `W`. This groups one coherent
finite-character theorem family into a single reviewable target.

The pairing used in Lean is

\[
 |G|^{-1}\sum_{g\in G}\chi_\rho(g^{-1})\chi_\sigma(g).
\]

The inverse of `Fintype.card G`, after casting to `ℂ`, is meaningful because
a group contains its identity and hence its finite cardinal is positive.
The normalization component identifies this with
`|G|⁻¹ Σ conj(χρ(g)) χσ(g)`. In Serre's convention, which is linear in
the first argument, this is `(χσ | χρ)`. This order agrees with the
dimension of `Hom_G(ρ, σ)`. The bilinear inverse-character pairing is
symmetric after replacing the summation variable by its inverse, so the
order does not change the orthogonality conclusions.

For the Hom-dimension assertion, decompose both representations into
irreducibles using Theorem 2. Schur's lemma gives a one-dimensional Hom
space between isomorphic irreducibles and a zero-dimensional Hom space
between nonisomorphic ones. Additivity of the Hom dimension and of the
character pairing gives the stated formula. This is a derived formulation
of the cited results, rather than a claim that Serre prints this exact
Lean-shaped statement.

The decomposition is expressed by a natural number `n`, subrepresentations
indexed by `Fin n`, their irreducibility, and an intertwining equivalence
from their direct sum to the original representation. It asserts existence,
not uniqueness of the chosen subspaces. `n = 0` permits the empty
decomposition of the zero representation, as in Serre's proof on p.7.
The norm-one statement also allows the zero representation, whose norm is
zero. It therefore uses the precise equivalence from Theorem 5 without
asserting that the norm of every representation is strictly positive.

## Exact source and environment

The cited original is Jean-Pierre Serre, *Linear Representations of Finite
Groups*, translated by Leonard L. Scott, Graduate Texts in Mathematics 42,
Springer, 1977.

- Literature ID: `serre-1977-linear-representations`.
- Retained file:
  `C:/Central-Library/Serre--Linear Representations of Finite Groups--1977.pdf`.
- SHA-256:
  `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
- The printed page is the PDF page minus nine in these passages.
- The definitions, statements, and arguments at the cited locations were
  read from the retained original. In particular, printed pp.7, 15, and 16
  were also inspected as page images to verify the empty-family case,
  pairing orientation, orthogonality, and character-isomorphism conclusion.

The only formal dependency is the prepared environment artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1: Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
The direct imports are `Mathlib.Analysis.Complex.Basic`,
`Mathlib.RepresentationTheory.Character`, and
`Mathlib.RepresentationTheory.Semisimple`. There are no imported project
statements, unaccepted construction modules, or project axioms.

Pinned Mathlib already proves several ingredients. In particular,
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank` and
`Representation.char_orthonormal` provide the Hom-dimension and
orthogonality formulas under their stated general field hypotheses;
`Representation.char_one`, `char_conj`, `char_dual`, and `char_iso`
provide the indicated character identities. Its separate
`RepresentationTheory.Maschke` module proves the complement property.
These are existing Mathlib results, not proofs supplied by this statement
contribution. A subsequent proof of the closing project target must
actually discharge every conjunct.

## Boundary with the remaining Henniart construction

This pair covers the finite-character foundations. It does not yet state
Brauer's integral induction theorem on the concrete representation
Grothendieck group, identify that group with a lattice on irreducible
classes, or construct an automorphic virtual map. The finite-group
construction owner supplies the representation classes and induction;
the virtual-lattice owner supplies the integral lattice and its actual
local instantiations. The later target lattice is free on supercuspidal
classes across positive ranks.

The norm-one assertion here concerns a genuine finite-group
representation. Henniart's separate assertion for an **integral virtual
vector** first yields a signed basis vector; a positive-degree hypothesis
is then needed to select the positive sign. That later assertion remains
a separate obligation, as do the finite-witness and numerical
surjectivity theorems. None is assumed by this proposition family.

For this boundary, the original is Henniart, *Une preuve simple des
conjectures de Langlands pour GL(n) sur un corps p-adique* (2000),
§§2.5–2.8, pp.445–448, and §3.7, p.451, read in the retained file
`C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
Its literature ID is `henniart-2000-simple-proof` and its SHA-256 is
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

Development compilation succeeded without diagnostics. All seven
elaborated proposition definitions were printed and inspected: each
retains the explicit `Fintype G` and finite-dimensional coefficient-module
hypotheses, and the two-carrier statements retain three independent
universes. This confirms the stated formal scope; it is not a proof of
the propositions or independent semantic acceptance.

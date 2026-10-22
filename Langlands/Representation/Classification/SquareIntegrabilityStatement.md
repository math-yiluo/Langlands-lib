# Square-integrability prerequisites for general linear groups

Worker 19 states `Langlands.GLSquareIntegrabilityPrerequisitesStatement`.
This is a proposition definition. It uses the published analytic definition
`IsSquareIntegrableModCenter`; it does not assert a Lean proof or use the
Jacquet exponent criterion as the definition of square-integrability.

## Objects and quantifiers

The statement quantifies every prime `p`, every `PadicField p` in an independent
field universe, and every positive natural rank `n`. The group is the actual
`Matrix.GeneralLinearGroup (Fin n) F.Carrier`, with the canonical module
topology of the finite extension of the usual p-adic field. Its topological-ring
instance is constructed by Mathlib's
`IsModuleTopology.isTopologicalRing`; it is not an added hypothesis.
The matrix and units topologies induce the usual topology on this general
linear group. The representation carrier occupies a separate arbitrary
universe and has no topology or finite-dimensionality assumption.

`Q` is the actual quotient by the full group center. Its measurable structure
is required to be Borel for its quotient topology. Both `mu` and any comparison
measure `nu` must satisfy Mathlib's `Measure.IsHaarMeasure`: left invariance,
finiteness on compact sets, and positivity on nonempty open sets. In particular
a zero measure is excluded. There is no choice of an additive character and no
normalization of a compact subgroup's volume in this statement.

The representation `rho` is admissible, hence smooth. No irreducibility or scalar
central action is assumed for the first three clauses. Each occurrence of
`IsSquareIntegrableModCenter` itself requires a smooth unitary scalar central
character and square-integrability of the descended absolute value of every
coefficient of a smooth-dual functional and a vector. It includes the
almost-everywhere strong measurability condition through `MemLp`.

## The four clauses

1. Replacing one Borel Haar measure on `Q` by any other leaves
   square-integrability unchanged.
2. For a character `eta : G -> Complex units` with open kernel and norm one
   at every group element, `twist eta rho` is square-integrable if and only if
   `rho` is. The action is `eta(g) * rho(g)`, and its scalar central character
   is `eta` restricted to the center times the original character.
3. The smooth contragredient is square-integrable if and only if `rho` is.
   Its action on a functional is precomposition with `rho(g inverse)`.
   Its scalar central character is the inverse of the original character.
   The dual action is linear over the complex field, without complex
   conjugation.
4. If `rho` is also irreducible, then for each supplied genuine
   `UnitaryCentralCharacter rho`, square-integrability is equivalent to the
   existence of a nonzero vector and a nonzero smooth-dual functional whose
   descended coefficient norm belongs to `L^2(Q, mu)`.
   Both factors must be nonzero. The supplied datum includes the actual
   scalar action and unit norm; it includes no integrability assertion.

Only the fourth clause assumes irreducibility. No canonical representative,
Hermitian form, Jacquet decomposition, induction irreducibility, or quotient
existence is supplied as input data.

## Original sources and derived content

The retained original is W. Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups*, draft of 1 May 1995:

- Literature ID: `casselman-1995-admissible-representations`.
- SHA256:
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Retained file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- Printed and PDF page numbers coincide.

Page 21 gives the open-kernel character and scalar-twist conventions and
defines the algebraic dual using the inverse group element. Page 22 defines
the smooth contragredient; Proposition 2.1.10 gives admissibility and bidual
reflexivity, and Corollary 2.1.13 preserves irreducibility. Section 2.5,
page 28, gives the matrix coefficient, its left/right translation laws
(Lemma 2.5.1 and Corollary 2.5.2), and the analytic definition of
square-integrability modulo the center. Proposition 2.5.3 on page 29 gives
the single-coefficient criterion, with a two-sentence proof sketch that the
next paragraph expands. These passages were read directly, including visual
inspection of the formula-bearing pages.

The fourth clause is the explicitly documented specialization of Proposition
2.5.3 to complex representations of positive-rank `GL_n` over finite
extensions of `Q_p`. The source is not restricted to `GL_n`; this statement is.
Its proof takes the subspace of vectors whose coefficient against a fixed
nonzero smooth functional is square-integrable. It is closed under addition
because every descended coefficient norm is locally constant, hence
measurable, and is dominated by the sum of two such norms. The translation
laws make it invariant: right translation preserves the Haar measure because
`GL_n(F)/Z` is unimodular (see the contragredient item below).
Irreducibility makes it the whole representation. The argument then applies
to the smooth contragredient, using left translation. The nonzero smooth dual and
irreducibility of that dual use the admissible duality results on page 22.

The first three clauses are derived consequences of these definitions and
duality results, not separately numbered theorems claimed to occur in the
original:

- Haar uniqueness gives a positive finite scalar between the two measures.
  Multiplication by this scalar preserves `MemLp` with exponent two and
  preserves the null sets relevant to measurability. The actual quotient
  `GL_n(F)/Z` is locally compact, Hausdorff and second countable, so the Borel
  Haar measures here have the regularity needed for uniqueness. The pinned
  Mathlib implementation supplies `Measure.haarScalarFactor_pos_of_isHaarMeasure`
  in `MeasureTheory/Measure/Haar/Unique.lean`, lines 418-424, and
  `Measure.isMulLeftInvariant_eq_smul_of_innerRegular`, lines 882-897.
  The declaration does not assume these conclusions as measure data.
- A smooth character twist leaves the smooth-dual functionals unchanged as
  a set after intersecting fixing subgroups with the character kernel.
  Its coefficient is multiplied by `eta(g)`, so a unitary twist leaves the
  coefficient norm unchanged. Admissibility is preserved using the same
  intersection argument on fixed spaces. Twisting back by `eta inverse`
  gives the reverse implication. The central action changes by
  `eta restricted to Z`, with no inverse on this twist.
- Admissible biduality identifies every smooth-dual coefficient of the
  contragredient with an original coefficient evaluated at the inverse group
  element. The quotient `GL_n(F)/Z` is unimodular, so inversion preserves
  its Haar measure. One way to check this concrete fact is to start with
  the two-sided Haar density `|det x|_F^(-n) dx` on the open matrix group:
  left and right multiplication on matrices have Jacobian `|det g|_F^n`.
  Quotienting by the closed central subgroup preserves unimodularity.
  The bidual identification and inverse character also give the converse.

These explanations specify the mathematical route, not implemented proofs.
In particular, the future formal proof still owes the required topology,
Haar uniqueness and inversion facts for this actual quotient, and the
admissible biduality and twist transports. A complete exponent criterion,
temperedness, unitarizability, and the Langlands quotient theorem are separate
obligations. The 1995 retained draft is not identified with the older
Casselman preprint cited by Silberger in 1978.

## Lean dependency and source map

Direct project imports are `Langlands.LocalField.Definitions`,
`Langlands.Representation.MatrixCoefficient.ModuloCenter`, and
`Langlands.Representation.Twist.Definitions`. The second imports the actual
smooth contragredient and matrix coefficients. Their intrinsic construction
proofs supply the objects; no pending project theorem is imported.
Mathlib supplies the nonzero irreducibility predicate, actual general linear
group, quotient topology, Borel space, Haar measure class, and `MemLp`.

The source correspondence is:

| Clause | Original or derived route | Actual Lean objects |
| --- | --- | --- |
| Haar normalization | C95 p.28 definition; Haar uniqueness as described above | `Measure.IsHaarMeasure`, `IsSquareIntegrableModCenter` |
| Unitary twist | C95 p.21 twist and character definitions; p.28 coefficient definition | `twist`, open kernel, complex norm |
| Contragredient | C95 pp.21-22 duality and p.28 coefficient definition | `smoothContragredient`, actual smooth-dual subtype |
| Single coefficient | C95 Proposition 2.5.3 and its proof sketch, p.29 | `Representation.IsIrreducible`, `UnitaryCentralCharacter`, `coefficientNorm`, `MemLp` |

This pair is authored for the pinned Lean 4.34.0 environment and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. Compilation, declaration
inspection, independent semantic review, and publication have not yet been
claimed here.

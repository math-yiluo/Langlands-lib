# Finite-quotient realization of the actual irreducible lattice

Worker 30 states seven separate prerequisites for the finite-group step in
Henniart's construction. They use Worker 24's lattice on genuine continuous
irreducible complex representation classes, with independent group, carrier
and quotient universes, and Worker 18's genuine split representation group
and subgroup induction. These are proposition definitions, not proofs.
The seven propositions form one finite-quotient theorem family.

The input is a group `G` with a topology and a finite group `H`. Each component
internally quantifies a topological-group instance on `G`, a surjective group
homomorphism `f : G →* H`, and openness of its kernel. No local Weil group or
Galois extension is fabricated from this data. Openness ensures that actual
finite-quotient representations inflate continuously; surjectivity ensures
that irreducibility and quotient character comparisons have their intended
meaning. The topology on complex coefficient spaces remains the usual
finite-dimensional topology of the imported parameter definitions.
Every component explicitly binds `Fintype H`, including those whose bodies
do not compute a finite sum. Thus finiteness is present in the elaborated
reusable propositions, rather than only in the surrounding section.

## Statements and normalization

1. `FiniteQuotientUnitaryStatement` says that the submodule supported on
   classes factoring through `f` lies in both the actual finite-image
   supported submodule and the unitary supported submodule. Finite image
   and existence of an invariant positive-definite Hermitian form remain
   different predicates. No form is selected.
2. `FiniteQuotientTraceFaithfulnessStatement` says that the trace map is
   injective on that supported submodule. It asserts no character
   faithfulness for the split representation group of an arbitrary infinite
   group, where nonsplit extensions would make such an assertion incorrect.
3. `FiniteQuotientDegreeStatement` identifies the integral rank-weighted
   degree, cast to the complex numbers, with the trace at the identity.
   Degree may be negative on virtual elements.
4. `FiniteQuotientPairingStatement` compares the integer coefficient pairing
   with `|H|⁻¹ ∑ h, a(h) conjugate(b(h))`. The scalar characters `a,b` must
   pull back to the two actual trace functions on all of `G`. Surjectivity
   makes them unique if they exist. Complex conjugation is on the second
   factor. This is the finite-character inner product; no local epsilon
   factor or Haar-measure convention is encoded by this finite sum.
5. `FiniteQuotientPositiveInductionStatement` says that each actual
   rank-one subgroup induction, after inflation, has a representative in
   the effective cone of the factoring-supported irreducible lattice.
   Equality is in the actual split virtual representation group. Its
   integral degree is the subgroup index. The coefficients are
   nonnegative for this genuine representation, without asserting
   nonnegative coefficients for Brauer expressions.
6. `FiniteQuotientBrauerSpanningStatement` includes the factoring support
   in the virtual preimage and, separately, the trace preimage of the
   span of actual inflated rank-one subgroup inductions. These inclusions
   are substantive theorem obligations, not definitions of the support
   or consequences of an assumed isometry. No converse about an arbitrary
   representation of the possibly infinite group `G` is asserted.
7. `FiniteQuotientSpanBijectionStatement` says that actual virtual
   realization restricts to a bijection from the factoring-supported
   irreducible lattice onto the inflated monomial span. Thus every element
   of that span has a unique factoring-supported irreducible realization.
   This image-surjectivity assertion is stronger than merely mapping the
   support into the span. It is a proposition, not a supplied equivalence.

`FiniteQuotientRealizationStatement` is exactly their conjunction. It does
not assume any component to construct the underlying objects, nor does it
assume an LLC equivalence. There is no automorphic representation type in
this prerequisite pair.

## Original sources and derived scope

Henniart 2000, sections 2.5–2.6, printed pp.445–447, supplies the
free irreducible lattice, integral degree and coefficient pairing.
Section 3.1, p.448, fixes the actual finite Galois setting, and section 3.7,
p.451, uses induced finite-order rank-one characters and Brauer's theorem
to include representations trivial over the chosen extension in the
induced-character lattice. These passages have been read. The present
finite-quotient formulation is a derived prerequisite for that step:
it exposes continuity, inflation, effective decomposition and trace
realization instead of assuming the identifications.

- Source `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

Serre, *Linear Representations of Finite Groups* (1977), section 1.3,
Theorem 1 and its Remark, printed p.6, gives invariant complements and
invariant Hermitian products; section 1.4, Theorem 2, p.7, gives
decomposition. Sections 2.2–2.3, pp.12–16, give the normalized character
inner product, orthogonality and multiplicities. Section 7.1,
Proposition 18, p.54, and section 7.2, pp.55–56, give actual subgroup
induction, its degree and character. Section 10.5,
pp.78–79, gives integral Brauer induction. These cited passages have been
read. Applying them to `H` and inflating along `f` explains the seven
propositions; these generic formulations are not quoted as numbered
theorems of Serre.

- Source `serre-1977-linear-representations`, SHA256
  `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.

Brauer, *On Artin's L-series with general group characters* (1947),
Theorem 1, printed p.503, formula (6), p.505, and section 9, pp.512–514,
is the original integral-induction source. Integral coefficients can have
either sign. Formula (6) is a sum over coset representatives; it agrees with
the normalized full-group sum used in the finite-character infrastructure.
No rational-only spanning conclusion is substituted.

- Source `brauer-1947-artin-l-series`, SHA256
  `7c9a789091fc6e09aeba312575b87fae1cab99ce53e842c4e378da980e21a1b5`.

## Published dependencies and remaining scope

This module imports `Langlands.VirtualRepresentation.Weil.Realization`,
whose Lean SHA256 is
`088912e4f2f9e1aa57894d0a76da12913d5fb1822be5bba09a7e3c772c467cb1`
and Markdown SHA256 is
`6771f74040ca8cf12ca278f2787da163f729c48c7082e23a1a0bba962225c335`.
The complete pair and its independent review were read. Both files were
verified byte-for-byte in Library commit
`fe68653a42ed5ae0a2d7f5cef0697a68e8acc978` before this submission.

The remaining construction imports are published in that Library:
VirtualRepresentation.Integral, Weil.Generic, Weil.Representation.Basic
and Predicates, and finite representation Classes, Induction and Virtual.
Their original authorship is preserved; no imported implementation is
part of this statement submission. The companion finite-group statements
`Langlands.FiniteCharacterTheoryStatement` and
`Langlands.FiniteRep.FiniteBrauerTheoryStatement` are published theorem
obligations. Their truth is not assumed to define this family.

A fresh Lean-service check against the published constructions confirms
that the closing declaration returns `Prop`, with only the standard
`propext`, `Classical.choice`, and `Quot.sound` assumptions. The complete
bodies were inspected in the original development, retaining the three
independent universes, finite-group binder and internal topological-group
hypothesis. The environment pins Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Actual local Weil specialization, automorphic supercuspidal lattices,
global weak-association relations, the local comparison isometry,
finite-witness independence and numerical surjectivity remain required
separate work. This pair neither assumes nor establishes those conclusions.

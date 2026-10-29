# Necessary upper bounds and opposite full-dual prefixes

Authors: Worker 84 and Worker 905. Worker 84 designed both declarations
and the initial Markdown; Worker 905 checked the conventions and
finalized the Markdown.

This is a derived internal interface for changing the convention of a
proved exponent bound. Both declarations are closed `Prop`-valued
definitions with independent field and representation universes `uF` and
`uV`. This file proves no exponent inequality or analytic theorem.

## The closed opposite-dual prefix statement

`Langlands.GLTemperedOppositeDualPrefixStatement.{uF,uV}` quantifies over
every prime `p`, actual p-adic field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, positive rank `n`, ordered block shape
`B : BlockShape n`, and representation `A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`
of the actual general linear group. It assumes that `A.ρ` is irreducible
and satisfies `T.IsTempered A.ρ`. This is the Library's analytic
predicate: for every Borel Haar measure on the quotient of `GL_n(F)` by
its full center, `A.ρ` is admissible, has a unitary central character with
open kernel, and every descended absolute smooth matrix coefficient lies
in `L^(2+ε)` for every real `ε > 0`. It is not an exponent-based
definition of temperedness. Admissibility follows from this hypothesis
(`IsTempered.isAdmissible`).

For every character `χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` with
`T.IsDualJacquetExponent B A χ`, and every `s : Fin B.length → ℝ` with
`T.IsRealPartOf χ s`, the conclusion is

```text
sum_(k <= i) s(k) <= 0
```

for every block index `i : Fin B.length`, including the last one, so the
full prefix is included.

- The dual exponent predicate is the ordinary one of `Exponents.DualJacquet`.
  The opposite Jacquet module is the actual quotient by the lower block
  unipotent subgroup, normalized by the positive upper half-modulus, and
  restricted to block scalars (`splitCentreOppositeJacquet`). Its full
  algebraic dual carries the transpose action (`splitCentreDualJacquet`),
  with no inversion or complex conjugation of the character.
  `IsDualJacquetExponent` requires that `χ` have open kernel and that the
  exponent-one space of this transpose action for exactly `χ` be nonzero.
  The statement covers every such character; it does not replace it by a
  primal eigenvector, a generalized dual component, or a selected
  constituent.
- The real part satisfies `‖χ(a)‖ = ∏_k normalizedAbs(a(k)) ^ s(k)` for all
  block-scalar tuples `a`. It is unique (`IsRealPartOf.eq`) and exists for
  every character with open kernel (`exists_isRealPartOf` in
  `Exponents.RealPartExistence`); the statement asserts neither fact.
  Thus `s(k)` is a scalar coordinate, with no additional block-size factor
  in the displayed prefix. A proof using determinant coordinates must
  account for the corresponding block sizes when converting coordinates.

The source `A` is not replaced by a tensor presentation, a
finite-dimensional representation, a scalar central layer, a unitarizable
representation, or a selected constituent. The statement assumes no
scalar central character beyond the one supplied by temperedness, no
positive form, unitarity classification, tensor factorization,
finite-dimensional carrier, or finite-length hypothesis.

## The adapter implication

`Langlands.GLTemperedOppositeDualPrefixAdapterStatement.{uF,uV}` is the
implication from the exact published
`GLProductLeviTemperedExponentNecessityStatement.{uF,uV}` to the closed
bound above, at the same universes. It isolates the conversion needed by
the analytic theorem for opposite Jacquet class exponents. The
implication's input is the entire upper necessity proposition, including
its actual refined Jacquet modules, generalized eigencharacters with
open kernel, single supplied Borel Haar measure on the full-center
quotient of the product Levi, and chamber of absolute values increasing
separately inside each outer block. The adapter neither proves that input
nor allows a source-criterion helper, citation, comparison certificate,
or pending task to replace it.

The current Library proves the input proposition as
`Langlands.glProductLeviTemperedExponentNecessity` in
[`ProductLeviTemperedExponentNecessityProof`](ProductLeviTemperedExponentNecessityProof.md).
This module neither imports nor uses that proof. Once the adapter is
proved, applying it to that theorem gives the closed statement; neither
this statement nor the adapter alone does so.

## Conversion obligations

The proposed proof route is internal to the existing Library
constructions. It is not a new translation of a literature theorem.
A proof of the adapter must supply all of the following steps rather
than assuming them as extra hypotheses.

- Detect a primal generalized character from the actual dual occurrence.
  An arbitrary dual eigenfunctional cannot simply be extended to, or
  identified with, a primal eigenvector, and its existence does not imply
  primal occurrence without a further argument. In the present
  irreducible admissible source scope, finite generation and admissibility
  of the actual opposite Jacquet module give a finite span of the
  block-scalar operators (`Exponents.DualJacquetFinitenessProof`). A valid
  finite-spectrum argument, or another proved method, must then detect
  the same character `χ` as a generalized eigencharacter of the primal
  opposite module.
- Transport the GL source to the actual Levi of a one-block shape.
  Preserve irreducibility and analytic temperedness by an actual
  topological group equivalence and change of variables on the quotient
  by the full center, including the pushed-forward Haar measure. The
  source's all-Haar hypothesis can supply the particular measure required
  by upper necessity; no tensor presentation or extra analytic comparison
  may be assumed.
- Identify the relevant refined upper quotient with the normalized
  opposite quotient after block reversal. Supply the actual coinvariant
  maps, scalar relabelling, and half-modulus identity. The upper
  normalization uses the inverse positive half-modulus; the opposite
  normalization uses the positive upper half-modulus. The existing
  `ProductLeviDualOppositeAdapter` passes from an upper generalized
  eigencharacter to an opposite one of the reversed refinement and then
  to a dual eigenfunctional. That is the sufficiency direction; its
  sufficiency implication alone does not prove this necessity conversion.
- Apply the upper bound to the correctly relabelled generalized
  character. After reversal, it bounds the opposite character on tuples
  of decreasing absolute value. For each `i`, test the tuple whose
  entries `k <= i` have a common absolute value greater than one and whose
  remaining entries are one. The real-part formula then forces the prefix
  sum through `i` to be nonpositive, including the full prefix.

The intended consumer combines the proved source bound with
`glOppositeJacquetSubquotientExponentInheritance` for arbitrary actual
subquotients, zero real-part totals on each unitary outer block, and
the separately proved dual-opposite product-Levi tempered sufficiency.
None of those consumer conclusions is asserted here.

This interface supplies no general-tempered-ambient scalar detection
theorem and no twist-class cone statement. The closed source bound and
the adapter must remain upstream of weakly critical refinement or
support, critical-to-minimal equivalence, tempered discrete-series
support, tempered block exhaustion, tempered unitarity or genericity,
regular exhaustion, and equal-exponent grouping.

## Provenance

The provenance is the explicit composition of two published statement
conventions: upper necessary bounds in
[`ProductLeviTemperedExponentNecessityStatement`](ProductLeviTemperedExponentNecessityStatement.md)
and opposite full-dual exponents in
[`DualJacquetStatement`](../Exponents/DualJacquetStatement.md), with the
constructions of `Exponents.DualJacquet`. Their paired Markdown records
the original analytic sources, among them Waldspurger 2003,
Proposition III.2.2 (necessity Markdown), and Silberger 1979, Lemma 4.5.6
(dual Jacquet Markdown). No further literature claim is made here. This
derived statement claims neither an implemented analytic necessity proof
nor that these exact coordinates and independent universes occur
verbatim in those sources.

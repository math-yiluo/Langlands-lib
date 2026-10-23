# Conjugacy of diagonal families in the actual Harris group

This module transfers the explicit diagonal conjugators and cardinality
classification to points of the constructed complex Harris group. It also
identifies the first-source-factor Kottwitz family and characterizes its
conjugacy to these diagonal families by the prescribed signature counts.
Its provenance is internal: it composes `DiagonalWeightConjugacy` with the
full group point equivalence from `ComplexGroupPoints` and the actual
cocharacter point formulas from `ComplexCocharacterPoints`.

## Matrix units and actual group point families

For a commutative ring `S`, a decidable predicate `p : Fin n → Prop`, and a
unit `u : Sˣ`, `ComplexMatrix.inverseDiagonalUnit S p u` is a unit whose
matrix and inverse matrix are respectively

\[
\operatorname{diag}(j\mapsto\text{if }p(j)\text{ then }u^{-1}\text{ else }1),
\qquad
\operatorname{diag}(j\mapsto\text{if }p(j)\text{ then }u\text{ else }1).
\]

The two unit identities are proved using multiplication of diagonal matrices
and the scalar unit identities, coordinate by coordinate.

Retain the totally real number field `E`, totally complex number field `K`,
quadratic extension and compatible algebra towers of
`D : CentralSimpleUnitaryData E K A n`, and charts
`C : HarrisSignatureCharts D.toSecondKindInvolution n Φ`.
For any scheme `T` over `Spec ℂ`, put
`S = AlgebraInvolution.complexTestAlgebra T`, the actual complex algebra of
global sections, and `G = D.complexRationalGroupScheme`.
The existing group equivalence is

\[
G(T)\ \simeq\
 \left(\prod_{\tau:E\to\mathbb R}\operatorname{GL}_n(S)\right)\times S^\times.
\]

For any family of predicates `p : (E →+* ℝ) → Fin n → Prop`,
`D.diagonalWeightPointFamily C T p u` is the inverse image under this
equivalence of

\[
\left((D_{p_\tau}(u))_\tau,\ u^{-1}\right),
\]

where `Dₚ(u)` is the inverse/trivial diagonal matrix unit just constructed.
Thus the definition constructs actual scheme points and includes the common
similitude multiplier. `diagonalWeightPointFamily_split` verifies its full
split coordinates by the inverse identity of the equivalence. Decidability
of the arbitrary support predicates is supplied classically.

## An explicit actual conjugator

Suppose `p,q` have equal support cardinalities at every real embedding:

\[
\#\{j:p_\tau(j)\}=\#\{j:q_\tau(j)\}\quad\text{for every }\tau.
\]

`D.diagonalWeightPointConjugator C T p q h` lifts the factorwise matrix units
`ComplexMatrix.diagonalWeightConjugator (p τ) (q τ) S (h τ)` through the same
point equivalence, with multiplier one.
`diagonalWeightPointConjugator_spec` proves

\[
g\,a_p(u)\,g^{-1}=a_q(u)\quad\text{for every }u\in S^\times,
\]

where `aₚ` denotes the actual diagonal point family.
The proof applies the injective group point equivalence, uses its
multiplication and inverse laws, and compares both components. Matrix-unit
extensionality reduces each matrix component to the previously proved
simultaneous diagonal conjugation identity. The multiplier is unchanged
because the conjugating point has multiplier one.

The family, conjugator, and conjugation identity are valid on every complex
test scheme, including empty schemes. They do not require nontrivial global
sections.

## Classification and the Kottwitz specialization

`D.DiagonalWeightPointConjugate C T p q` is the proposition that one arbitrary
actual point `g ∈ G(T)` conjugates the entire `p` family to the `q` family.
Assuming `[Nontrivial Γ(T.left, ⊤)]`,
`diagonalWeightPointConjugate_iff_card_eq` proves that this holds exactly when
the support cardinalities agree at every real embedding. For necessity,
apply the full point equivalence to the assumed conjugation equation and
project to each matrix factor. The resulting equation supplies the generic
`DiagonalWeightConjugate` proposition, whose classification theorem gives
the cardinality equality. Sufficiency uses the constructed actual conjugator.
The nontriviality assumption is used in the generic numerical rank argument.

Define the standard support

\[
p_\tau(j)\iff j<r_\tau,
\qquad r_\tau=
\begin{cases}
n-1&\tau=C.\mathrm{distinguished},\\
n&\text{otherwise}.
\end{cases}
\]

`diagonalWeightPointFamily_kottwitz` identifies `aₚ(u)` with the actual
point obtained by evaluating `D.kottwitzCocharacter C true` at the `Gm`
point corresponding to `u`. The proof compares their full split coordinates
using `kottwitzCocharacter_split_points`: unit extensionality and the diagonal
formula prove the matrix identities, and both multipliers are `u⁻¹`.
The Boolean `true` selects the first source factor, retaining the previously
implemented conjugation-before-inversion convention.

Finally, under the same nontriviality assumption,
`diagonalWeightPointConjugate_kottwitz_iff` proves that there is one actual
point conjugating this evaluated Kottwitz family to `a_q` exactly when

\[
\#\{j:q_\tau(j)\}=r_\tau\quad\text{for every }\tau.
\]

The implementation substitutes the Kottwitz identification into the preceding
classification, computes the standard-support cardinality with
`Fin.card_filter_val_lt`, and uses `rτ ≤ n` to remove the minimum.

These are classifications of the specified families on a fixed test scheme,
with fixed charts. The construction uses the actual scheme point group but
does not yet establish compatibility of the chosen conjugators under test
scheme pullback, a scheme cocharacter classification, chart independence,
or a Galois action and reflex stabilizer. Those are further comparison steps.

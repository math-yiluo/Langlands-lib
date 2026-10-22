# Determinant polynomials and power traces for unramified comparisons

Author: Worker 44. This is an algebraic prerequisite statement contribution to
task `369ca096-d0b6-4e25-8a06-66af3ef95878`, revision 2. All four declarations
in `Langlands.Automorphic.Unramified` are definitions of propositions.
They supply no proof or assumption that the propositions hold.

## Objects, normalization and scope

The entries are actual finite square matrices over `Complex`. For a matrix
`A`, the existing Mathlib definition `Matrix.charpolyRev` is

\[
 P_A(T)=\det(1-TA).
\]

The variable `T` is formal. In an unramified local application the substitution
is \(T=q_v^{-s}\), so the local Euler factor is \(P_A(q_v^{-s})^{-1}\).
This contribution neither defines an analytic Euler product nor chooses a
Frobenius convention or a Satake parameter for a representation. Those
identifications must come from the actual arithmetic and automorphic
definitions and their compatibility statements.

Every matrix rank is a natural number; families are indexed by `Fin a` or
`Fin b`, and ranks may vary with the index. All coefficients are complex.
There are no additional universe parameters, scalar-ring instances, group
instances, project dependencies, or supplied theorem hypotheses. Zero ranks
and empty families are allowed in these algebraic statements. Positivity of a
residue-degree input and nonvanishing of a determinant are stated where needed.

## Exact proposition definitions

`EulerProductTraceStatement` says that

\[
 \prod_{i<a}P_{A_i}(T)=\prod_{j<b}P_{B_j}(T)
 \quad\Longleftrightarrow\quad
 \forall k\geq1,\ 
 \sum_{i<a}\operatorname{tr}(A_i^k)
   =\sum_{j<b}\operatorname{tr}(B_j^k).
\]

It requires every positive integer power, not only the first trace. Repeated
matrices and repeated constituents are allowed. Invertibility and
semisimplicity are unnecessary for this algebraic equivalence. For example,
a zero eigenvalue contributes neither a positive power trace nor a factor to
\(P_A\). Thus this equivalence alone makes no assertion about equality of
matrix ranks.

`InductionPolynomialTraceStatement` quantifies positive integers \(f_i\) and
asserts the equivalence

\[
 P_B(T)=\prod_{i<a}P_{A_i}(T^{f_i})
 \quad\Longleftrightarrow\quad
 \forall k\geq1,\ 
 \operatorname{tr}(B^k)
   =\sum_{\substack{i<a\\ f_i\mid k}}
       f_i\,\operatorname{tr}(A_i^{k/f_i}).
\]

The Lean conditional term is zero when \(f_i\) does not divide \(k\).
Its division is natural-number division, and the divisibility branch has
exact integer quotient because \(f_i>0\). The family may describe all places
above one unramified place, but the statement is purely algebraic and does
not assert that any given integers arise as residue degrees.

`InductionPolynomialDegreeStatement` says that, if every \(f_i>0\) and
\(\det(A_i)\ne0\), then

\[
 \deg\!\left(\prod_{i<a}P_{A_i}(T^{f_i})\right)
   =\sum_{i<a} f_i n_i,
\]

where \(n_i\) is the size of \(A_i\). The Lean degree is `Polynomial.natDegree`.
These polynomials all have constant term one, so the product is nonzero,
including for an empty family. The determinant condition is essential for
the full rank count.

`TraceAlgebraStatement` is the conjunction of these three complete,
universally quantified targets. It introduces no assumptions under which the
targets become vacuous and no abstract automorphic types or predicates.

## Original sources and derived correspondence

1. H. Jacquet and J. Shalika, *On Euler Products and the Classification of
   Automorphic Forms II*, American Journal of Mathematics **103** (1981),
   777–815, §4.1–4.2, printed pp.805–807, and §4.3–4.4, pp.807–809.
   Literature ID: `jacquet-shalika-1981-euler-ii`.
   Retained PDF SHA256:
   `4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
   The retained original is
   `C:/Central-Library/Jacquet-Shalika--On Euler products and the classification of automorphic forms II--1981.pdf`.
   Worker 44 visually inspected printed pp.805–809 (PDF pp.30–34).
   The source defines the \(k\)-th unramified trace by
   \(\rho(v^k)=\operatorname{tr}(B_v^k)\). Theorem 4.2 tests finite linear
   relations in these traces for all \(k\geq1\), outside one finite set of
   places. Theorem 4.4 passes from equality of block sums of semisimple
   unramified classes to equality of the sums of these traces and then to
   equality, with multiplicity, of cuspidal constituents.
2. J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
   Theory of the Trace Formula*, Annals of Mathematics Studies **120**,
   Princeton University Press, 1989, Chapter III §1, p.199, and §6,
   pp.214–217, particularly Definition 6.1 and formulas (6.1)–(6.2).
   Literature ID: `arthur-clozel-1989-base-change`.
   Retained PDF SHA256:
   `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
   The retained original is
   `C:/Central-Library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`.
   Worker 44 read these original pages and visually checked p.215 and p.217.
   Unramified base change raises a Satake matrix to the residue degree.
   Unramified induction takes a direct sum at split places and all
   root-of-unity multiples of an \(f\)-th root at a place of residue degree
   \(f\). Its normalized determinant polynomial is \(P_A(T^f)\).

The three targets are explicit **derived algebraic prerequisites**, not
verbatim transcriptions of the automorphic theorems. Their generalization to
arbitrary complex matrices is justified by the formal identity

\[
 -T\,P_A'(T)/P_A(T)
   =\sum_{k\geq1}\operatorname{tr}(A^k)T^k
 \quad\text{in }\mathbb C[[T]].
\]

Multiplication of polynomials adds these series; substitution \(T\mapsto T^f\)
gives the divisibility formula and the factor \(f\). Conversely, two
polynomials with constant term one and the same logarithmic derivative agree
in characteristic zero. Finally the leading coefficient of \(P_A\) is
\((-1)^n\det(A)\), so the degree calculation follows when determinants
do not vanish. This explains the intended mathematical content and the
extension beyond semisimple matrices; it is not a Lean proof receipt.
Formal proofs of the three targets remain separate obligations.

## Dependency and coverage boundary

Only the prepared environment is used: artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1; Lean 4.34.0,
commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The imports are `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff` and
`Mathlib.Basic.Complex.Basic`. The pinned Mathlib definition `Matrix.charpolyRev`
and its constant-term and first-coefficient lemmas were inspected before
authoring; no replacement determinant-polynomial definition is introduced.
No pending project draft is imported.

This pair does not state or prove Jacquet–Shalika linear independence,
cuspidal/isobaric rigidity, existence or uniqueness of cyclic base change,
automorphic induction, or descent. In particular it does not assume those
results through a data structure. Their actual cuspidal/isobaric realizations,
local-component data, normalized spherical Hecke/Satake objects, Galois actions,
and twists remain with global definition task
`a6077a58-5c34-4ef4-9cd1-7e3d1b2332f4`. The corresponding theorem statements
remain required contributions of the current task. The present finite algebra
is useful for those later formulations but does not complete their coverage.

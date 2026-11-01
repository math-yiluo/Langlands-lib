# Convergence and rationality of Whittaker matrix integrals on the model

## Exact target and scope

`Langlands.GodementJacquet.modelWhittakerRationality.{uF,uV}` proves the existing closed proposition
`Langlands.GodementJacquet.ModelWhittakerRationalityStatement.{uF,uV}`.
The field and representation-carrier universes are independent.

For every prime, canonical p-adic field, bundled nontrivial unitary additive
character, and natural `n`, the target considers a representation of
`GL_(n+1)` satisfying the full original `IsOfWhittakerType`. For every
specified nonzero standard Whittaker functional, every Schwartz–Bruhat test
on all square matrices, and every vector of its actual coefficient image,
the shifted matrix integral converges on a right half-plane and has a
rational continuation in the canonical `q^(-s)`. The statement includes
`n = 0`, reducible representations, and tests on singular matrices.
Its half-planes and rational functions may depend on the test and model
vector. The shift is the complex number `jpssShift n = n/2`, and the measure
is the existing normalized `generalLinearHaar`.

## Implemented proof

The closing theorem applies
`Langlands.GodementJacquet.WhittakerTorus.Padic.modelWhittakerRationality`
to `Langlands.whittakerTypeAsymptotic` and
`Langlands.RankinSelberg.finiteFunctionMellin`, with explicit universe
arguments. This supplies both premises of the conditional theorem and
leaves no premise on the closing theorem.

The imported conditional theorem uses the published
`Langlands.RankinSelberg.modelAsymptoticTransfer` to transfer the full
Whittaker torus expansion to the actual coefficient image. Admissibility,
equivariance, continuity and this expansion establish
`glModelFunction_isWhittakerLike`. The imported
`IsWhittakerLike.matrixConverges` gives convergence of each unshifted
full-matrix integral on a right half-plane using finite-function Mellin
analysis and the Iwasawa reduction. The helper
`glModel_shifted_of_converges` then shifts that half-plane by
`(jpssShift n).re` and applies
`IsWhittakerLike.hasRationalContinuation` to the shifted integral.
These are the two conjuncts of the unchanged target.

## Source and provenance

This is an internal assembly of the coefficient-model analytic theorem,
the full-torus Whittaker asymptotic theorem, and finite-function Mellin
analysis. Its mathematical target is the convergence and rationality
assertion in Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), Section (5.2), printed 420–421,
registered source `jpss-1983-rankin-selberg`. There the representation is
of Whittaker type and acts on its Whittaker model; the Library uses the
actual coefficient image of the given functional.

The asymptotic source is Jacquet, Piatetski-Shapiro and Shalika,
*Automorphic Forms on GL(3) I* (1979), Proposition (2.2) and Remark
(2.2.5), printed 181–183, registered source `jps-1979-gl3-i`.
Remark (2.2.5) extends the expansion to admissible finitely generated
spaces of Whittaker functions. Proposition (3.1), printed 185–186, gives
the earlier irreducible generic matrix-integral argument. The implemented
proof uses the full-type torus expansion and Mellin analysis; it does not
extend the irreducible statement by an unsupported carrier equivalence.
The target's Markdown explains the shift and the omission of the source's
common greatest common divisor assertion.

Worker 352 prepared this closing pair. Workers 249 and 261 supplied the
conditional assembly and the closing expression reused here.

## Declaration checks

The closing module and two private complete-type assignments compile with no
errors or warnings. Both assignments use the unapplied closing constant at
independent universes `uF` and `uV`: one against the published proposition,
and one against its entire expanded quantifier prefix. Declaration inspection
reports a theorem with universe parameters `uF`, `uV` and only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

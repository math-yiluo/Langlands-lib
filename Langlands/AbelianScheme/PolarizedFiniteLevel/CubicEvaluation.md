# Actual cubic evaluation and canonical base change

This internal derivation applies `ProjectiveBundle.EvaluationBaseChange`
and `ProjectiveBundle.EvaluationFibres` to the existing actual
`Datum.cubicBundle`, `Datum.rigidificationModule`,
`Datum.cubicBundlePullbackIso` and `Datum.rigidificationBaseChangeMap`.
It preserves all data, per-datum dual witnesses and indices of the
published ordinary functor. No new external literature assertion is made.

For a datum `a` over a scheme `S` in an arbitrary universe,
`Datum.cubicEvaluationAdjoint` is the actual adjunction counit
`pi^* pi_*(a.cubicBundle) → a.cubicBundle`. The identification with
`evaluationAdjoint` for identity evaluation follows from the adjunction's
identity formula.

For every base morphism `b : S' → S`,
`Datum.cubicEvaluationAdjoint_baseChange` identifies the pullback of that
counit, with source transported through the inverse pullback-square
comparison, with the following actual composite: pull back
`a.rigidificationBaseChangeMap b` along the changed structure map, apply
the counit of `a.pullback b`, and apply the forward canonical cubic
line-bundle comparison. This uses exactly the specified direct-image
comparison, whose definition contains the inverse coefficient
comparison. The proof applies the general base-change adjoint formula,
then uses naturality of the changed counit and cancels those two inverse
coefficient comparisons. No flatness or invertibility assumption is
needed for this equality.

`Datum.cubicEvaluationGenerates_of_fibre_epi` assumes quasi-coherence
of the original rigidification module, epimorphy of its specified
base-change map at every residue field, and epimorphy of the cubic
counit on the actual pulled-back datum at each such field. The preceding
equality expresses the original fibre adjoint as a composite of
epimorphisms and the canonical coefficient isomorphism. The proved
fibrewise criterion therefore gives intrinsic relative generation.

`Datum.cubicEvaluationGenerates_of_directImage` assumes the published
`CubicDirectImageStatement`, a locally noetherian original base and
positive polarization index `d`. Its finite local rank gives local
freeness and hence quasi-coherence. Its invertibility assertion applies
to every residue-field base change and supplies the required
epimorphy. The fibre cubic-counit epimorphy assumption remains explicit.

These are conditional reductions. They do not prove
`CubicDirectImageStatement`, fibre cubic generation, a closed immersion,
or the eventual ordinary fine-moduli representability theorem.

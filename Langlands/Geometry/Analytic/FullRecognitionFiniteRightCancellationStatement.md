# Finite right cancellation over a common open base

`AffinoidAtlasPresentation.StrongHom.FiniteOverRightCancellationStatement K`
states a geometric cancellation law for actual strong maps
`g : A.saturatedPresentation → B.saturatedPresentation` and
`g' : B.saturatedPresentation → C.saturatedPresentation`. Let `V`, `U`, and
`T` be open subsets of the three underlying spaces. If `g(V) ⊆ U`,
`g'` is finite from `U` to `T`, and the specified saturated composite is
finite from `V` to `T`, then `g` is finite from `V` to `U`.

Here finiteness means the published `IsFiniteOver`: for every recognized
affinoid subset `W` of `U`, the literal subset `V ∩ g⁻¹(W)` must be
recognized, and the actual full-recognition pair map from `W` to that
preimage must be finite Banach. Thus recognition and finite Banach bounds
are conclusions. Neither algebraic finiteness alone nor a supplied
recognized preimage is a premise.

The field, space, and index universes remain independent. The ground
field is any complete ultrametric normed field. No global Hausdorff
hypothesis, nontrivial valuation, or strictness condition is imposed.

## Derived provenance and proof boundary

This is a derived geometric prerequisite of strong étale right
cancellation, rather than a verbatim assertion in the original source.
The underlying finite-morphism convention is Berkovich, *Étale cohomology
for non-Archimedean analytic spaces* (1993), Lemma 1.3.7 and the following
definition, printed pages 27–28 / retained PDF pages 24–25. That passage
identifies finiteness on a local affinoid family with finiteness on every
affinoid domain; its proof uses affinoid refinement and Kiehl's theorem.
The source is registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

On a compatible common-base affinoid triangle, the published
`BoundedAlgHom.IsFiniteBanach.of_comp` supplies the algebraic cancellation
with norm-controlled coefficient lifts. Extending those local triangles
to every recognized subset of `U`, and constructing their recognized
preimages, is the geometric content still required here. The ring-level
helper alone does not prove this statement. This module defines only the
proposition and makes no claim that the geometric extension has been
proved. It supplies neither pointwise étaleness nor étale cancellation.

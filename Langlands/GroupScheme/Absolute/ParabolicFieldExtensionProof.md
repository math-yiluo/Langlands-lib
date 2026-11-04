# Parabolic subgroups under arbitrary field extension: proof

Worker 445 wrote the final assembly. Worker 1370 contributed the solvability
proof used by the published Borel theorem and coordinated that prerequisite.

`Langlands.GroupScheme.parabolicFieldExtensionStatement` proves exactly the
published `Langlands.GroupScheme.ParabolicFieldExtensionStatement.{u}`.
For arbitrary fields `k K : Type u` with `Algebra k K`, a connected reductive
group scheme `G` over `Spec k`, and an actual homomorphism `i : P ⟶ G`,
it sends `IsParabolicSubgroup i` to

```lean
IsParabolicSubgroup
  ((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)
```

There are no additional premises on the field extension, the group, or the
parabolic. In particular the characteristic and universe are arbitrary,
imperfect fields and inseparable or transcendental extensions are included,
and neither the full-group parabolic nor the trivial group is excluded.
The statement, its imported definitions, and the actual base-change functor
are unchanged.

## Implemented proof

The proof introduces the exact statement's fields, group schemes,
homomorphism and hypotheses. It registers the smoothness and affineness
provided by `IsConnectedReductive G`.

It then chooses the published
`algebraicClosureEmbedding k K : AlgebraicClosure k →ₐ[k] AlgebraicClosure K`
and installs the algebra structure induced by its ring homomorphism.
With this local instance, the scalar map between the two closures is
definitionally that ring homomorphism. The corresponding map of spectra
is `algebraicClosureBaseMap k K`; its compatibility with the original
scalar map is already part of the published closure comparison.

The proof applies
`IsParabolicSubgroup.baseChange_of_geometricBorel` with the original
`Spec K → Spec k`, this closure map, and the natural isomorphism
`algebraicClosureBaseChangeIso k K`. It remains to prove preservation of
each Borel inclusion into `G` pulled back to `AlgebraicClosure k`.
The pulled-back ambient group is affine and smooth by stability under
pullback. Its connectedness is
`IsConnectedReductive.connectedSpace_toAlgebraicClosure`.
The published theorem `borelAlgClosedFieldExtensionStatement` now applies
between `AlgebraicClosure k` and `AlgebraicClosure K`, and discharges this
remaining obligation, including the complete maximality condition.

The applied transport lemma supplies all three fields of the resulting
parabolic predicate. Closedness follows from
`IsClosedSubgroup.baseChange`; smoothness follows from pullback stability.
For the geometric Borel factorization, it pulls back the original witness
and factor and composes with the components of the closure comparison.
`baseChangeBorelFactor_comp` proves the required equality by naturality.
`IsBorelSubgroup.comp_iso` transports the Borel inclusion to the actual
ambient group `(G_K)_K̄`. Thus the result concerns the actual homomorphism
and subgroup schemes, including their geometric factorization.

## Dependencies and provenance

The final assembly is an internal composition of published results:

- `Absolute.ParabolicFieldExtensionStatement` supplies the unchanged target.
- `Absolute.ParabolicGeometricWitnessTransport` supplies the witness
  construction and the conditional transport lemma, implemented by Worker 445.
- `AlgebraicClosureBaseChange` supplies the compatible closure embedding and
  natural comparison, implemented by Worker 1359 with contributions from
  Workers 445 and 1340.
- `GeometricConnectedness` supplies connectedness after passage to the
  chosen closure.
- `Absolute.BorelAlgClosedFieldExtensionProof`, implemented by Workers 1498
  and 1382 using Worker 1370's published solvability theorem, supplies
  unconditional Borel preservation between algebraically closed fields.
  That theorem accounts for the further chosen closures in
  `IsSolvableGroupScheme`; the final assembly does not identify an
  algebraically closed field definitionally with its chosen closure.

The statement's Markdown records the original geometric Borel criterion
and its field-extension interpretation, including Milne, *Algebraic Groups*
(2017), Theorem 17.16 and §17.66. This module adds no new literature
assertion and uses the published statements and proofs above. No
`ParabolicDynamic` theorem, maximal-torus field-extension theorem, or
connected-reductive field-extension conclusion is used.

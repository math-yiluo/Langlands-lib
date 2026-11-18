# Locality for directed subscheme exhaustions

These internal helpers support the geometric exhaustion argument of SGA 3,
Exposé IX, Lemma 6.2. They prove categorical and open-cover reductions, without
claiming the exhaustion theorem itself.

If a monomorphism contains an isomorphism as a subobject, it is a split
epimorphism and therefore an isomorphism. This remains true after an arbitrary
pullback. The actual base change of an inclusion in the slice category is
compared with its pullback along the projection of the ambient base change.
Both conventions express the same scheme-theoretic fullness.

For a nonempty directed increasing family of immersions into a quasi-compact
scheme, suppose that around every ambient point some member is all of the
ambient open subscheme. A finite subcover supplies finitely many indices,
which admit one upper bound. The corresponding immersion is full on every
member of this finite cover, so the Zariski locality of isomorphisms makes it
an isomorphism globally. This finite-cover result is bundled in the
Prop-valued `LocalityStatement` and proved by `locality`.

The provenance is internal category theory and quasi-compactness, in support
of the finite-cover and localization steps in the proof of SGA 3, Exposé IX,
Lemma 6.2, printed pp.53–54 (retained PDF pp.23–24), registered as
`sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
Neither noetherianity nor a structural morphism is required by the
finite-cover helper. It has no Artinian-testing conclusion.

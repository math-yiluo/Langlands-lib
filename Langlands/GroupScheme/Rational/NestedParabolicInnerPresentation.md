# Compatible inner presentations inherited from nested parabolics

This is derived internal support for the nested Jacquet-exponent argument in
Renard VII.2.3. It constructs a compatible root presentation for specified inner
maps from supplied fine and outer ambient presentations. It does not assert
presentation existence for arbitrary parabolics without those ambient data,
and does not prove a representation-theoretic target by itself.

Work over an arbitrary field `k` in universe `u`, with the original ambient
parabolics `p : P ⟶ G`, `q : Q ⟶ G`, Levi maps `m : M ⟶ P`, `l : L ⟶ Q`,
and split-component maps `b : B.toGrp ⟶ M`, `a : A.toGrp ⟶ L`. Supply verified
presentations `fine`, `outer`, and the original inner maps `pL : PL ⟶ L`,
`mL : M ⟶ PL`. Their common-Levi equality is
`(mL ≫ pL) ≫ (l ≫ q) = m ≫ p`. The ambient group is connected reductive,
`range p ≤ range q` on every test scheme, and the inner image is exactly
`range (pL ≫ (l ≫ q)) = range (l ≫ q) ⊓ range p`. The construction also takes
actual parabolicity of `pL`, rational-Levi status of `mL`, the split-component
predicate for `b`, and the original geometric outer radical `r : U ⟶ Q` with
an isomorphism `subgroupMultiplication l r`. Ambient affineness is explicit;
the root comparisons additionally display affineness of `L` and local finite
type of `G` and `L`. These conditions hold for the intended connected reductive
application and are not replacements for an unconditional final target.

`innerPresentationData` retains the literal fine torus, generic cocharacter,
selected-root set, and component factor. Its torus inclusion is the previously
constructed `outerFineTorusFactor` into the original `L`. The established
maximal-split and actual root comparisons give maximality and genericity. The
selected fine roots belong to the outer zero face, which is the actual simple
root set in `L`. Consequently the fine defining component cocharacter is
standard for this inherited root data.

The all-test closed-pullback identity identifies the inherited generic dynamic
parabolic with the inverse image of the original fine generic minimal
parabolic. Root-sign inclusions and negation stability show that the actual
outer radical is contained in that ambient minimal parabolic: the latter is
contained in `range p`, hence in `range q`, and the transported outer
cocharacter realizes `range q` and its radical. This uses the proved
`relativeRootSignInclusions` and `relativeRootNegation`, rather than either
statement as an extra hypothesis.

The general helper
`IsMinimalParabolicFunctor.comap_levi_of_radical_le` proves minimality of this
inverse image. For any smaller actual inner parabolic it forms the actual
parabolic extension through the supplied Levi retraction. Every point of that
extension splits into the original Levi and radical coordinates, both lying
in the ambient minimal parabolic. Ambient minimality forces equality. The
exact intersection of the extension with the original Levi then recovers the
smaller inner subgroup and proves equality of inner subgroup functors. Actual
parabolicity of the inherited generic subgroup is supplied by its affine
dynamic representative and the unconditional geometric dynamic-parabolic
recognition theorem, using reductivity of the original outer Levi. No general
parabolic correspondence or its still separate proof is assumed.

`innerPresentation` assembles the full compatibility record. The fine
component factor keeps its original image in `L`, and its defining
cocharacter realizes exactly `range pL` and `range (mL ≫ pL)` by the existing
closed-pullback identities. The standard/dynamic comparison from proved
negation stability gives the required standard-parabolic and standard-Levi
identities. Pullback of the fine minimal-parabolic containment supplies the
inner containment. The explicit defining cocharacter supplies the realization
field, including the empty-root case. Thus no inner-presentation-existence or
minimality premise is added.

The proof route is an internal derivation from the existing actual subgroup,
dynamic, Levi-extension and root-comparison constructions. The four unchanged
nested-cone support pairs bundled with this candidate retain their own
independent review bindings.

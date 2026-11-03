# Abstract normalizer and centralizer of split-torus rational points

`Langlands.GroupScheme.normalizerPointsInfiniteField` proves the exact published
proposition `Langlands.GroupScheme.NormalizerPointsInfiniteFieldStatement.{u}`.
For every infinite field `k : Type u`, connected reductive group scheme `G`
over `Spec k`, and split subtorus `i : T.toGrp ⟶ G`, it proves both equalities:

- `normalizerPoints i` is the abstract `Subgroup.normalizer` in `G(k)` of
  `(SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))`, the image of `T(k)`;
- `centralizerPoints i` is the abstract `Subgroup.centralizer` of that same set.

There are no additional field, maximality or characteristic hypotheses. The
proof uses the published definitions and changes none of their modules or
paired descriptions.

The source statements are Milne, *Algebraic Groups* (2017), Propositions 1.84
and 1.93, printed pp.32 and 34 (PDF pp.48 and 50), source
`milne-2017-algebraic-groups`. They identify normalizer and centralizer points
using rational points of a smooth subgroup that are dense over a field
extension. Here the extension is `k` itself and the subgroup is the image of a
split torus. The official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction to either
proposition. The split-torus function-detection argument is elementary internal
infrastructure, explained in `SplitTorusRationalDetection.md`.

The implemented proof follows that density argument through regular functions
and factorization, using the existing all-test subgroup functors. It does not
construct a representative scheme for the normalizer or centralizer.

For the normalizer, the first internal comparison lemma assumes that a map
`T.X ⟶ G.X` factors through `i` whenever its composites with all base points do
so. A published normalizing point already normalizes the torus over every test
scheme, so in particular it lies in the abstract normalizer of `T(k)`. In the
other direction, an abstract normalizing point `n` and its inverse both
conjugate each point of `T(k)` into its image. Applying the factorization
premise to `i ≫ int(n)` and `i ≫ int(n⁻¹)` produces two maps `T.X ⟶ T.X`.
Composing with any test point shows that both conjugations preserve torus
points over every test scheme. The published
`torusNormalizer_le_normalizerPoints` then gives membership in
`normalizerPoints i`; its monomorphism hypothesis follows from the closed
immersion `i`.

For the centralizer, the second internal comparison lemma assumes that maps
`T.X ⟶ G.X` are determined by their composites with all base points. A published
centralizing point centralizes all test points and therefore all base points.
Conversely, abstract commutation gives equality on base points of
`i ≫ int(n)` and `i`. The detection premise identifies their underlying maps;
`Grp.hom_ext` identifies the group-scheme morphisms, which is exactly the
published membership condition for `centralizerPoints i`.

Finally, the theorem instantiates these premises with
`IsSplitTorus.exists_factor_of_kpoints` and `IsSplitTorus.hom_ext_kpoints`.
The connected reductive hypothesis supplies affineness of `G`, and the split
subtorus hypothesis supplies the closed immersion and split-torus property.
The infinite-field hypothesis enters through the rational-point detection
lemmas. All statements and the proof retain the arbitrary universe `u`.

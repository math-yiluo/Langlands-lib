# Finite-fiber affine neighborhoods and the global Weil-restriction inverse

This is derived construction infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2,
printed pp.9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad discusses finite locally free restriction of scalars on p.9 and uses
finite-set affine neighborhoods and affine-open constructions on p.10. The
particular finite-fiber cover and inverse-gluing implementation below is derived.

## Objects and hypotheses

All rings and schemes use an arbitrary common universe `u`. Let `A → B` be a
commutative algebra with `Module.Finite A B` and `Module.Projective A B`, the
finite locally free setting over the affine base. Let `Y` be an actual scheme
over `Spec B` with `LocallyOfFiniteType Y.hom`. The imported
`affineChartWeilRestriction A B Y`, denoted `G`, is the actual scheme over
`Spec A` obtained by gluing the existing affine Weil restrictions of all affine
opens of `Y`. Its actual global counit defines the imported canonical comparison

`Hom_A(T, G) → Hom_B(T ×_A B, Y)`.

The final inverse and equivalence additionally require `IsSeparated Y.hom` and
`HasFiniteAffineNeighborhoods Y.left`. The latter is precisely the geometric
proposition that every finite set of underlying scheme points is contained in
one affine open. It does not assume any representing Hom bijection, gluing data,
or topology comparison. The affine specialization of this geometric property
is proved using the full affine open. Its quasi-projective specialization is
not proved in this module.

Every test scheme `T` is an arbitrary actual scheme over `Spec A`; it need not
be affine, quasi-compact, finite type, or separated. Base change is the actual
scheme pullback. No field, separability, local-ring, nonzero-rank, or topological
hypothesis occurs.

## Actual finite-fiber source neighborhoods

`finiteAffineFactorizationOpens_cover` considers a finite morphism `π : Z → W`
and a morphism `e : Z → X`, where `X` has the finite-set neighborhood property.
For each `w : W`, the set-theoretic fiber of `π` is finite, so its image in `X`
is contained in one affine open `U`. The previously constructed
`universallyClosedFactorizationOpen π e U` is the complement in `W` of the
closed image of the complement of `e⁻¹(U)`. Its proved membership criterion
puts `w` in this open exactly when the whole fiber over `w` maps into `U`.
These actual opens cover `W`; `finiteAffineFactorizationOpenCover` constructs
the corresponding scheme open cover. No surjectivity of `π` is needed.

For `q : T ×_A B → Y`, `affineChartWeilRestrictionSourceOpen` applies this
construction to the finite first projection `T ×_A B → T`. The actual cover
`affineChartWeilRestrictionSourceCover` is indexed by all affine opens `U` of
`Y`. `SourceChart` and `SourceChartι` equip its open components and inclusions
with their original structure maps to `Spec A`.

The proved `SourceChart_range` uses the actual cartesian square of base-change
maps and the whole-fiber criterion to show that restriction of `q` to the
base change of each source chart lands in its specified target affine open.
`SourceChartTarget` is the resulting actual morphism into that open subscheme;
`SourceChartTarget_fac` identifies its composite with the original open
inclusion exactly with the restricted `q`.

## Local inverses and gluing

`affineChartWeilRestrictionLocalInverse` applies the already established
all-test affine representing equivalence to `SourceChartTarget` and then
composes with the original chart inclusion into `G`. Its comparison is proved
to be exactly the restriction of `q`. Up to this point neither separatedness
nor the finite-set neighborhood property is needed, except for constructing
the cover itself.

Under relative separatedness of `Y`, the imported global comparison is
injective on every test scheme. `LocalInverse_compatible` applies that
injectivity to the actual pairwise pullbacks of source-neighborhood inclusions.
Naturality and the local comparison identities reduce compatibility to the
pullback equation for those inclusions. Thus compatibility is proved for the
specified local morphisms, rather than supplied as an assumption.

`affineChartWeilRestrictionInverse` uses the genuine source open cover and
Mathlib's scheme-morphism gluing to construct a morphism `T → G`. Its
compatibility with the map to `Spec A` follows by checking on that cover.
`Inverse_restrict` identifies its restriction with every original local
inverse. Pulling the same cover back to `T ×_A B` and checking equality on that
cover proves `Inverse_comparison`: its canonical comparison is exactly `q`.

## Representing equivalence and naturality

`affineChartWeilRestrictionTestEquiv` is the actual equivalence

`Hom_A(T, G) ≃ Hom_B(T ×_A B, Y)`.

Its forward map is definitionally the existing counit comparison; its inverse
is the explicit glued morphism just constructed. The right inverse law is
`Inverse_comparison`, and comparison injectivity proves the left inverse law.
`TestEquiv_apply` records the exact forward map. `TestEquiv_natural` proves its
contravariant naturality for every morphism of test schemes. The separate
`Inverse_natural` identity proves naturality of the explicit inverse, even
though its source cover depends on the input `q`.

## Retained scope

This gives representability by the actual glued scheme under the explicit
finite-set affine-neighborhood condition and relative separatedness. It does
not yet prove that condition for quasi-projective schemes, finite type or
quasi-projectivity of `G`, or the local and adelic homeomorphisms in Example
4.2. Those remain required parts of the whole-paper task. The construction
cannot be used to discard the neighborhood hypothesis for an arbitrary
nonaffine target.

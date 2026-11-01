# Open affine charts for the total presheaf of an algebra functor

This module constructs relatively representable open immersions from specified
affine charts into the total presheaf of an algebra functor. It proves that these
charts form a locally surjective family when they cover all field-valued
elements. It does not construct the resulting glued scheme.

All rings, algebra-functor values, chart indices, and chart rings are in
universe zero. The schemes are `Scheme.{0}`. There is no nontriviality
hypothesis on the base or test rings.

## Inputs and exported conclusion

The exported theorem is
`AlgebraicGeometry.Scheme.exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart`.
Its complete signature agrees with the pinned source wrapper. Its inputs are:

- A commutative ring `R`, a type-valued functor `F` on commutative `R`-algebras,
  its maps `Fmap`, and identity and composition laws.
- A presheaf `G` on schemes over `Spec R`, natural equivalences
  `ev A : F A ≃ G(Spec A over Spec R)`, and the hypothesis that `G.overTotal`
  is a sheaf for the big Zariski topology on schemes.
- Predicates `P i A s` indexed by `i : ι`. For each `s : F A`, an open subset
  `U ⊆ Spec A` must exist such that, for every `R`-algebra homomorphism
  `φ : A →ₐ[R] B`, the predicate holds on `Fmap φ s` if and only if the image
  of `Spec B → Spec A` is contained in `U`.
- Commutative `R`-algebras `S i` and natural equivalences from
  `{s : F A // P i A s}` to `S i →ₐ[R] A`.
- A cover condition: every element of `F K`, for every field `K` with an
  `R`-algebra structure, satisfies some `P i K`.

The conclusion supplies maps
`f i : yoneda.obj (Spec (S i)) ⟶ G.overTotal`. Each satisfies
`IsOpenImmersion.presheaf`, and `Sigma.desc f` is locally surjective for the
big Zariski topology. The value of `f i` at the identity of its affine chart
is explicitly the pair consisting of the structure morphism to `Spec R`
and the `ev`-image of the element corresponding to `AlgHom.id R (S i)`.
Thus the conclusion retains the specified chart coordinates.

Here `IsOpenImmersion.presheaf` has Mathlib's representability meaning:
pulling back along any map from a represented scheme yields a represented
open immersion. It is stronger than injectivity on the supplied affine tests.

## Total sections and chart predicates

The internal namespace is
`AlgebraicGeometry.Scheme.AlgebraFunctorOpenCharts`. Its structure `Datum`
packages exactly the inputs above; `Datum.f` is the chart map construction.
It has no representability assumption on `G.overTotal`.

For an affine scheme, `Datum.Sec A` is the type of pairs `(t, b)` with
`t : Spec A ⟶ Spec R` and `b : G(Spec A, t)`. The imported
`Langlands.CategoryTheory.OverTotalPresheaf` provides this total presheaf,
its fibre comparisons, and its functoriality. The helper `algOf` recovers
an `R`-algebra structure from any such `t` by the full faithfulness of `Spec`;
`algHomOfSpec` similarly recovers an algebra homomorphism from a compatible
affine scheme morphism.

`Datum.secOf` sends `s : F A` to the total section
`(Spec(algebraMap R A), ev A s)`. The lemmas `rd_secOf`, `secOf_rd`,
and `secOf_injective` compare these descriptions. Every affine total section
has this form for a suitable algebra structure. Equality of structure
morphisms forces equality of the recovered algebra structures.

The predicate `Datum.Q i b` on total sections is defined by existence of
such an algebra structure and an element satisfying `P i`. The lemma
`Q_secOf` proves that this agrees with `P i` for the given algebra structure,
so the existential description adds no extra chart elements.

The affine image criterion proves that `P i` persists under arbitrary algebra
homomorphisms. For an element over a field, it also descends from any nonzero
test algebra: the spectrum of the field is a singleton and the test spectrum
is nonempty. These facts imply `Q_map` and invariance under field extensions
in `Q_iff_of_field`.

## The open subset on an arbitrary scheme

For a total section `ξ` on a scheme `T`, the predicate `Datum.mem i ξ x`
tests `Q i` after restriction along
`T.fromSpecResidueField x`. The lemma `mem_map` proves its invariance under
every scheme morphism. The proof uses Mathlib's compatibility between
residue-field maps and the maps from residue-field spectra, followed by
the field-extension invariance above.

On `Spec A`, `mem_secOf_iff` identifies this pointwise predicate with membership
in the open set supplied by the affine image criterion. The key geometric
identity is that the image of the spectrum of the residue field at `x`
is the singleton `{x}`. Openness for arbitrary total sections follows by
restricting to the affine open cover of `T` and taking the corresponding open
images. This constructs the actual open subscheme `Datum.W i ξ`.

## Universal chart sections and represented pullbacks

`Datum.u i` is the chart element corresponding to the identity of `S i`,
and `Datum.univSec i` is its total section. Chart naturality shows that pulling
it back along the homomorphism corresponding to a chart element recovers that
element.

Two morphisms to `Spec (S i)` pulling back the same universal section are
equal: first use the natural chart equivalence on an affine test, then apply
the affine-open-cover morphism extensionality theorem on a general scheme.
Conversely, a section satisfying `mem i` everywhere comes from a morphism to
the chart. On affine opens, this morphism is supplied by the chart equivalence.
The uniqueness just proved makes these local morphisms compatible on
overlaps. Mathlib glues them, and the separatedness part of the assumed
Zariski sheaf condition identifies the resulting section with the original.

The map `Datum.f i` is the Yoneda transformation determined by `univSec i`.
For an arbitrary map `g : yoneda.obj T ⟶ G.overTotal`, its pullback along
`f i` is represented by the inclusion `W i (yonedaEquiv g) ⟶ T`.
The implemented proof verifies the square on every test scheme:
commutativity follows from the universal section, uniqueness from the
monomorphism of the open inclusion, and existence from the range criterion
and `IsOpenImmersion.lift`. The chart-morphism uniqueness above verifies
the other projection of the lift. Mathlib's
`MorphismProperty.relative.of_exists` then gives `IsOpenImmersion.presheaf`.

At each point of `T`, the field-valued cover hypothesis selects a chart
for the residue-field section. Hence the open subschemes `W i ξ` cover `T`.
On each, the universal chart section lifts `ξ`; the induced covering sieve
proves `Datum.isLocallySurjective`. The theorem `Datum.main` packages these
maps and their universal-section formulas.

## Scope in the representability route

This is an intermediate construction. The existence of `G`, its sheaf
condition, affine-test openness, natural chart equivalences, and field cover
are inputs to this theorem. Applying it to a specific moduli problem requires
proving those hypotheses. This module alone supplies neither a representing
scheme nor projectivity, smoothness, properness, a polarized-abelian moduli
construction, or the normalized Harris CM comparison.

## Source, dependencies, and adaptations

This is a focused port of the complete Anthropic FLT source at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, registered as
`anthropic-flt-complete-lean-source-6e837e75`. The registered distribution has
SHA-256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete source files were read and compared:

- `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.lean`,
  lines 1–484, SHA-256
  `f3c846daa73f6f9a8572f2ae5cd65818b6bbd5b86e9640cea6fcbfa91f927fd2`.
- `Theorems/Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.lean`,
  lines 1–46, SHA-256
  `f108dfe98465068495f387c548e8377a063693d517ac0a168c04a417f8dcf0fc`.

The source namespace `GrassH2.Ctx` becomes
`AlgebraicGeometry.Scheme.AlgebraFunctorOpenCharts.Datum`. Generated
`p2m_open`, `p2m_reactivate`, and wrapper elaboration are replaced by ordinary
Lean namespaces and a direct application of `Datum.main`. Scoped simp
attributes become ordinary simp attributes. The broad Mathlib import is
replaced by focused imports of `Sites.Representability` and `ResidueField`;
the source's total-presheaf definition is replaced by the published Library
module with the same Lean API.

Compatibility edits make the underlying identity composition explicit in
`map_secOf`, use `erw` at three coercion-sensitive rewrites, replace a deprecated
coproduct lemma by `Sigma.ι_comp_desc`, and use current `let` instance syntax in
six proof-local declarations. No hypotheses, universes, predicates, chart
equivalences, or conclusions are changed.

The relevant current Mathlib sources are
`CategoryTheory/MorphismProperty/Representable.lean` (relative representability),
`AlgebraicGeometry/ResidueField.lean` (point tests and their naturality),
`AlgebraicGeometry/Sites/BigZariski.lean` (the topology and covering sieves),
and `AlgebraicGeometry/Sites/Representability.lean` (the available framework
for the subsequent gluing step). This module constructs the open immersions;
it does not invoke the subsequent `LocalRepresentability.representableBy`.

The retained [license](../../licenses/Anthropic-FLT/LICENSE),
[notice](../../licenses/Anthropic-FLT/NOTICE), and
[attribution](../../licenses/Anthropic-FLT/ATTRIBUTION.md) accompany the port.
The attribution table has no separate entry for this source module.

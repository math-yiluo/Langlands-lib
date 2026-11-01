# Representing an algebra functor by gluing affine charts

The exported theorem
`AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover`
constructs a scheme over `Spec R` from an algebra functor with finite
principal-open descent and a covering family of natural open affine charts.
Its output includes natural equivalences on all affine test schemes, the
chart open immersions, their compatibility with the structure morphism,
coverage of every point of the scheme, and the chart formula for each
represented element. The representing scheme is constructed in the proof.

All rings, algebras, functor values and the chart index are in universe zero.
The base is any commutative ring. No field, nontriviality, Noetherianity,
finite generation or finiteness of the chart index is required.

## Exact hypotheses and conclusions

For every commutative `R`-algebra `A`, the input supplies a type `F A`, and for
every `R`-algebra homomorphism `φ : A →ₐ[R] B` a map
`Fmap A B φ : F A → F B`. The identity and composition laws are hypotheses.
The descent hypothesis states unique gluing for every finite family
`f : Fin n → A` spanning the unit ideal, every realization `B i` of
`A[(f i)⁻¹]`, and sections agreeing after both maps to every realization of
`A[(f i * f j)⁻¹]`. The specified `A`- and `R`-algebra structures on these
localizations form scalar towers. The hypothesis includes `n = 0`.

The chart data consist of an index type `ι`, predicates `P i A` on `F A`,
commutative `R`-algebras `S i`, and equivalences

`{s : F A // P i A s} ≃ (S i →ₐ[R] A)`.

They are natural under every `R`-algebra homomorphism. Affine-test openness
means that for each `i`, `A` and `s : F A` there exists an open
`U ⊆ PrimeSpectrum A` such that, for every `φ : A →ₐ[R] B`,
`P i B (Fmap A B φ s)` holds exactly when the image of `Spec φ` lies in `U`.
Coverage is required for every field `R`-algebra `K`: each `s : F K`
satisfies some `P i K`. There is no flatness condition on the test maps.

The theorem produces an actual `X : Scheme.{0}`, a morphism
`p : X ⟶ Spec R`, equivalences

`pt A : F A ≃ {g : Spec A ⟶ X // g ≫ p = Spec (algebraMap R A)}`,

and morphisms `j i : Spec (S i) ⟶ X`. It proves:

- For every `φ : A →ₐ[R] B` and `s : F A`, the morphism associated to
  `Fmap A B φ s` is `Spec φ ≫ (pt A s).1`.
- Each `j i` is an open immersion and its composite with `p` is the scalar
  structure morphism of `S i`.
- Every point of `X` lies in the image of some `j i`.
- For every `s` satisfying `P i A`, the morphism `(pt A s).1` is
  `Spec (chart i A s) ≫ j i`.

## Implemented construction

The module imports `Langlands.AlgebraicGeometry.AlgebraFunctorSheaf` and
`Langlands.AlgebraicGeometry.AlgebraFunctorOpenCharts`. The first constructs
an over-`Spec R` presheaf `G`, natural affine evaluation equivalences `ev`,
and the big Zariski sheaf property for `G.overTotal`, using the supplied
principal-localization descent. The second uses the openness, chart and
field-coverage hypotheses to construct relatively representable open
immersions `f i : yoneda.obj (Spec (S i)) ⟶ G.overTotal`, with a locally
surjective coproduct. Their values on identity maps are the specified
universal chart sections.

Mathlib's `Scheme.LocalRepresentability.glueData` takes the represented
pairwise pullbacks of these `f i` as overlaps. The scheme `X` in the proof
is this gluing's `glued` scheme, and `j i` is `toGlued`. With the sheaf and
local surjectivity already established, `representableBy` constructs a
representation `e` of `G.overTotal` by `X`. The open immersion instances
and pointwise coverage are those of this actual gluing.

The relative structure morphism is `e.overTotalBase`, from the imported
`CategoryTheory.Functor.RepresentableBy` API in
`Langlands.CategoryTheory.OverTotalPresheaf`. It is the first component of
the total section associated to the identity of `X`. The identity
`e.overTotal_homEquiv_fst` identifies the first component of the section
associated to any `g : T ⟶ X` with `g ≫ e.overTotalBase`.

The helper namespace
`AlgebraicGeometry.Scheme.AlgebraFunctorRepresentability` implements the
affine fibre comparison explicitly. `Pts G e A` is the subtype of
`Spec A ⟶ X` lying over the prescribed scalar map `AlgebraFunctorOpenCharts.strMap R A`.
`toPts` inserts `ev A s` into the total presheaf using `ofFibre`, then
applies `e.homEquiv.symm`. `ofPts` extracts the fibre using `toFibre`,
then applies `(ev A).symm`. Their inverse laws use the published
`toFibre_ofFibre`, `ofFibre_toFibre` and dependent-pair congruence lemmas.
The primary definition `ptEquiv` packages these maps as an equivalence.

`ptEquiv_natural` uses naturality of `ev` and of the representation `e`.
Equality in the total presheaf is checked on the scalar morphism and
the transported section separately; the scalar equality is exactly
`φ.comp_algebraMap` after applying contravariance of `Spec`.

For the final chart formula, let `u i` be the inverse-chart image of the
identity of `S i`. The identity
`yonedaGluedToSheaf_app_toGlued` identifies `e.homEquiv (j i)` with the
total section associated to `u i`. It follows that `j i` has the required
base morphism and equals the point associated to `u i`. The helper
`P_map` shows stability of each chart predicate under base change: its
openness criterion at the identity forces the controlling open subset
to be the whole spectrum. Chart naturality and injectivity then express
every chart element as the base change of `u i`. Naturality of
`ptEquiv` gives the displayed chart formula.

## Source and adaptation

This is an adaptation of the registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:

- `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_represents_of_zariskiSheaf_of_openAffineCover.lean`,
  complete lines 1–199, SHA-256
  `7fd936b70291b6fc1b284a5f7235808985edc49e96ca186ae41fd60b207c6898`.
- `Theorems/Thm_AlgebraicGeometry_Scheme_exists_represents_of_zariskiSheaf_of_openAffineCover.lean`,
  complete lines 1–48, SHA-256
  `2f5cd6377eaafe0e8aec7c0672b83f67ce571e8c0f46f2672c326341f5671a5c`.

The registered distribution has SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
Both files were read in full. The exported theorem signature is
byte-identical to the original wrapper, including all universes,
localization realizations, chart naturality, field coverage and output
formulas.

The port replaces the aggregate `Mathlib` and generated theorem imports
with the two focused Library imports, replaces the generated `P2MW`
namespace and `p2m_open`/`p2m_exact_reverting` wrapper machinery with an
ordinary namespace and theorem, and renames `GrassBridgeS1` to the helper
namespace above. The original wrapper's global simp-attribute removals
are unnecessary here. The proof changes are three `rw` to `erw`
replacements for coercion-sensitive equivalence rewrites, an explicit
`Category.comp_id` equality in the naturality proof, and `haveI` to
`have` for the proposition-valued local surjectivity instance. These
changes preserve the original construction and its hypotheses.

Mathlib's current local-representability implementation is in
`Mathlib/AlgebraicGeometry/Sites/Representability.lean`; the port uses its
actual gluing and representation constructions. Its documentation cites
the Stacks Project, Tag 01JJ. This module's cited original for the
combined algebra-functor theorem is the pinned Lean source above.

The Apache 2.0 notices are retained in
[LICENSE](../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../licenses/Anthropic-FLT/NOTICE) and
[ATTRIBUTION.md](../../licenses/Anthropic-FLT/ATTRIBUTION.md).
Those files are byte-identical to the pinned distribution. Its attribution
table has no separate entry for these two source modules.

## Scope within the CM representability task

This prerequisite constructs a scheme representing an algebra functor
once its descent, open charts and field coverage have been proved. It
does not establish these hypotheses for polarized abelian schemes or
the normalized Harris CM presheaf. The theorem asserts neither
smoothness nor projectivity. The exact normalized moduli comparison
on the full componentwise admissible category and admissibility of the
representing CM scheme remain further obligations of
`DivisionCMRepresentabilityStatement`.

The scalar map and its compatibility under algebra homomorphisms reuse
`AlgebraFunctorOpenCharts.strMap` and `AlgebraFunctorOpenCharts.spec_comp_strMap`.
These are the same scalar maps as in the source construction.

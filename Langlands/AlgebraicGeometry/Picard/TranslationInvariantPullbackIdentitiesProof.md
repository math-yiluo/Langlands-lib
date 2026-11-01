# Multiplication and inversion from ordinary translation invariance

This module proves the entire published proposition
`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement.{u}`:

```lean
theorem Langlands.AbelianScheme.algClosedFieldTranslationInvariantPullbackIdentities :
    Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement.{u}
```

The theorem has no outer parameters. It applies to every algebraically closed field
`K : Type u`, every abelian scheme `A` over `Spec K`, and every actual line bundle
`L` satisfying `GroupScheme.IsTranslationInvariant A.toGrp L`. It produces actual
module-sheaf isomorphisms

```text
m^*L ≅ p1^*L ⊗ p2^*L,
L ⊗ i^*L ≅ O_A,
```

where the first product is the categorical product in `Over (Spec K)`,
`m = p1 * p2`, and `i = ((𝟙 A.X)⁻¹).left`. Both conclusions use `Nonempty`.
The proof chooses inverses and isomorphisms internally; the theorem requires no
chosen identity-fibre trivialization or extra premise. The statement and its
imports are unchanged.

## Globalizing rational-point comparisons

The helpers lie in
`Langlands.AbelianScheme.TranslationInvariantIdentities`.

`classes_eq_of_rational` compares two rigidified classes over a parameter
`T : Over (Spec K)` whose structure morphism is locally of finite type and whose
underlying scheme is reduced. Its hypothesis is equality after pullback along
every `K`-rational point of `T`. The published theorem
`Langlands.AbelianScheme.rigidifiedClassesEqualizerClosed` supplies a closed
immersion `incl : Z ⟶ T.left` representing their agreement locus, including its
factorization property for every test scheme.

Every closed point of `T.left` comes from a `K`-rational point by
`pointOfClosedPoint`. The hypothesis and the factorization property therefore put
all closed points in the range of `incl`. The parameter is Jacobson, so its closed
points are dense; the range of a closed immersion is closed, hence `incl` is
surjective. The reduced-target theorem
`isIso_of_isClosedImmersion_of_surjective` makes `incl` an isomorphism. Factoring
the identity through it gives equality after identity pullback. The implemented
`relativePullbackId RigidifiedModule.pullbackCoherence` comparison identifies
that equality with the original equality of classes.

This uses the existing proved seesaw and descent infrastructure through the
published closed-equalizer theorem. In its import closure,
`rigidifiedClassesEqualizerClosedNoetherianAffine` applies the proved
`noetherianLineBundleSeesaw`, rigidified Zariski separatedness and
`smoothGeometricIntegrality`. The intermediate
`rigidifiedClassesEqualizerClosedNoetherianAffine_of_seesaw` establishes geometric
integrality fibrewise and the required affine-base-change global-functions
condition using `smoothProperConnectedGlobalFunctions`. The existing affine
reduction, noetherian approximation and Zariski gluing then give the closed
equalizer used here. This module neither assumes nor duplicates those results.

`iso_of_rational` compares ordinary line bundles `M` and `N` on the relative space
`T ×_K A`. It assumes an isomorphism of their restrictions to `(id,e)` and
isomorphisms of their pullbacks over each rational parameter. These are internal
helper hypotheses, discharged below for the multiplication families.

Write `f : T ×_K A ⟶ T` for the projection and `ε` for its identity section.
The proof chooses a tensor inverse `B` of `ε^*M` using
`LineBundle.exists_tensorObj_iso_structureSheaf`. The section isomorphism also
trivializes `ε^*N ⊗ B`. `LineBundle.normalize` constructs rigidified bundles with
underlying line bundles `M ⊗ f^*B` and `N ⊗ f^*B`.
On each rational fibre the given isomorphism tensors with the identity on the
common factor; the actual pullback-tensor comparisons supply the needed
underlying isomorphism. The published
`RigidifiedLineBundle.nonempty_iso_of_forget_iso` corrects that isomorphism to
respect rigidification, since `ε` has the retraction `f`. Thus the preceding
helper makes the two normalized rigidified classes equal globally. Forgetting
the resulting rigidified isomorphism and cancelling the common class `[f^*B]` in
`LineBundle.IsoClasses` yields an actual line-bundle isomorphism `M ≅ N`.

## Multiplication

`rational_addition` identifies the addition family at a rational parameter `x`
with translation by `x` after the second projection. It uses the actual
`relativeSpace` base-change map and the published `mumfordProduct`,
`mumfordFirst`, `mumfordSecond` and `mumfordAddition` definitions. The proof
checks both projections as morphisms over `Spec K`, then applies
`MonObj.comp_mul` and `GroupScheme.points_translation`.

`multiplication_class` works first on the explicit scheme fibre product
`pullback A.X.hom A.X.hom`, with the first factor as parameter. It applies
`iso_of_rational` to

```text
M = mumfordAddition^*L,
N = firstProjection^*L ⊗ secondProjection^*L.
```

The parameter `A.X.left` is reduced by smoothness over a field, using
`SmoothReducedProof.isReduced_of_smooth_over_field`; its finite-type hypothesis
comes from the abelian-scheme structure.
Along `(id,e)`, addition and first projection are the identity, and second
projection factors as `A.X.hom ≫ unitSection A`. A class pulled back through
`Spec K` is trivial by `LineBundle.pullbackHom_eq_one_of_factor`. This gives the
section isomorphism required by the helper.

For each rational parameter `x`, the first-projection pullback again factors
through `Spec K`, so its class is trivial. `rational_addition` identifies the
addition pullback with a pullback of `translation x`. The sole hypothesis
`hL x` identifies the translation pullback with `L`. The second projection is
unchanged. These identities give the required fibre isomorphism. Globalization
therefore proves `[M] = [N]`.

`categorical_multiplication_class` transports this result to
`P := A.X ⨯ A.X` in `Over (Spec K)`. A morphism `φ : P ⟶ mumfordProduct A` is
constructed explicitly by `pullback.lift` from the two categorical projections.
Its compositions with the raw first and second projections are those
categorical projections, and composition with raw addition is their group
product. Applying `LineBundle.pullbackHom` along `φ.left` to the raw class
identity gives exactly the categorical multiplication identity. No inverse to
`φ` is needed for this argument.

## Inversion and the final module isomorphisms

The final theorem obtains its first conjunct from the categorical class
identity via `LineBundle.isoClass_eq_iff`, then applies `LineBundle.forget` to
produce the required isomorphism of actual module sheaves.

For the second conjunct it sets
`j := Limits.prod.lift (𝟙 A.X) ((𝟙 A.X)⁻¹)`. The projection equations and the
group law give `j ≫ m = 1`, `j ≫ p1 = 𝟙 A.X`, and `j ≫ p2 = (𝟙 A.X)⁻¹`.
The constant identity scheme map factors as `A.X.hom ≫ unitSection A`, whose
pullback class is trivial because the intermediate scheme is `Spec K`.
Pulling back the multiplication equality along `j.left`, using the actual
composition, identity and tensor comparisons encoded in
`LineBundle.pullbackHom`, gives `[L] * [i^*L] = 1`. Applying
`LineBundle.isoClass_eq_iff` and forgetting once more gives precisely
`L.obj ⊗ i^*L.obj ≅ structureSheaf A.X.left`.

The class calculations use the published group of actual line-bundle
isomorphism classes. Its pullback multiplication law is proved from the
canonical module-sheaf pullback-tensor comparison, whose invertibility is the
unconditional theorem `pullbackTensorComparisonIsIso`. Thus passage through
classes does supply actual isomorphisms, and tensor preservation is discharged
inside the proof. No field-cube theorem, represented Picard scheme, dual
existence, translation-difference lifting or cohomology vanishing is used.
Nothing excludes dimension zero, the trivial bundle or any characteristic.

## Provenance, authorship and checks

The target's mathematical provenance is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary chapters, Lemma (7.16), printed p.104 / PDF
p.108, and the displayed multiplication and inversion identities in the proof
of (7.19), printed p.105 / PDF p.109. The registered original is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, content SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The unchanged statement Markdown records the rational-translation
interpretation and source locators in detail. A bounded local check on
2026-10-31 found no matching EVM-specific errata file in the workspace,
project-notes or Library-notes errata locations.

The helper formulations and proof assembly here are derived project work:
normalization reduces ordinary families to the published rigidified closed
equalizer, and equality of actual isomorphism classes is converted back to
module-sheaf isomorphisms. This is the implemented proof route, rather than a
formal represented-Picard comparison. The proof adds no new axiom or unproved
mathematical premise.

Worker 59 authored the Lean proof and this explanation. Workers 306 and 100
supplied the exact specification and source/ownership context reused here.
The Lean service compiled the entire module and inspected the theorem with
zero errors and warnings in the pinned Lean 4.34.0 environment. Inspection
reports universe parameter `u` and only `propext`, `Classical.choice` and
`Quot.sound`. Compilation is development evidence; independent review and
exact-target validation govern publication.

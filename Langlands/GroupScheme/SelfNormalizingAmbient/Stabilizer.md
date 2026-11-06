# Stabilizers of infinitesimal neighbourhoods in cut-out subgroups

This module works over an arbitrary commutative ring `R`. It fixes a group-valued functor `F` on
commutative `R`-algebras, corepresented by an algebra `B` through `e`
(`e : (F ⋙ forget GrpCat).CorepresentableBy B`), as in the Library module
`Langlands.GroupScheme.CorepresentedNormalizer`. It extends the normalizer ideal of that module
from cut-out subgroups to arbitrary cut-out subfunctors, and applies it to the infinitesimal
neighbourhoods of the unit in a cut-out subgroup.

## Stabilizers of cut-out subfunctors

Fix an ideal `K` of `B`.

- `VanishesOn e K x`: the classifying map `e.homEquiv.symm x : B ⟶ A` of `x ∈ F A` kills `K`.
  These points form a subfunctor of `F`, which need not be a subgroup.
- `Stabilizes e K g`, for `g ∈ F A`: for every algebra map `f : A ⟶ A'` and every `x ∈ F A'` with
  `VanishesOn e K x`, both `F.map f g * x * (F.map f g)⁻¹` and `(F.map f g)⁻¹ * x * F.map f g`
  vanish on `K`. This is the condition defining the Library `normalizerFamily`, with the subgroup
  replaced by the subfunctor cut out by `K`.

Basic facts: `vanishesOn_iff_le_ker` (vanishing means `K ≤ ker`), `VanishesOn.map` (stable under
base change), `VanishesOn.mono` (antitone in `K`), `vanishesOn_sup` (vanishing on `K ⊔ K'` means
vanishing on both).

The proof of the main criterion follows the Library proof of `isCutOutBy_normalizerFamily`, which
does not use the subgroup property of the cut-out family.

- `vanishesOn_universalCutPoint`: the Library `universalCutPoint e K A` over
  `A ⊗[R] (B ⧸ K)` vanishes on `K`.
- `exists_universalCutPoint_of_vanishesOn`: every point vanishing on `K` over an `A`-algebra
  `f : A ⟶ A'` is the image of the universal cut point under an algebra map
  `A ⊗[R] (B ⧸ K) ⟶ A'` that restricts to `f` on `A`.
- `stabilizes_iff_universal`: `Stabilizes e K g` holds exactly when the two conjugates of the
  universal cut point by the image of `g` in `F (A ⊗[R] (B ⧸ K))` vanish on `K`.
- `vanishesOn_map_tensorQuotientMap_iff` (assuming `B ⧸ K` is a projective `R`-module): for
  `φ : B ⟶ A` and `y ∈ F (B ⊗[R] (B ⧸ K))`, the image of `y` under `φ ⊗ id` vanishes on `K` exactly
  when `φ` kills the Library coefficient ideal (`ProjectiveTensorCoefficients.coefficientIdeal`) of
  the image of `K` under the classifying map of `y`.
- **`stabilizes_iff`** (assuming `B ⧸ K` is a projective `R`-module): for every `φ : B ⟶ A`,
  `Stabilizes e K (e.homEquiv φ)` holds exactly when `subgroupNormalizerIdeal e K ≤ ker φ`. So the
  Library ideal `subgroupNormalizerIdeal e K` cuts out the stabilizer of the subfunctor cut out by
  `K`, for every ideal `K` with `B ⧸ K` projective, not only for ideals of subgroups.

## Infinitesimal neighbourhoods of the unit

- The published `LinearEmbedding.counit e : B ⟶ R` is the classifying map of the unit `1 ∈ F R`, and `augIdeal e` is its kernel.
- `jetIdeal e J n` is `J ⊔ augIdeal e ^ (n + 1)`. When `J` cuts out a subgroup, it cuts out the
  `n`-th infinitesimal neighbourhood of the unit in that subgroup.
- The published `LinearEmbedding.cls_one`: the classifying map of `1 ∈ F A` is `LinearEmbedding.counit e` followed by the structure
  map `R ⟶ A`.
- `classify_mem_of_map_eq_one` and `map_eq_one_of_classify_mem`: for an ideal `N` of `A`, a point
  `x ∈ F A` becomes `1` in `F (A ⧸ N)` exactly when its classifying map sends `augIdeal e` into `N`.
- **`VanishesOn.conj`**: if `x ∈ F A` vanishes on `augIdeal e ^ m`, so does `g * x * g⁻¹` for every
  `g ∈ F A`. Proof: let `N` be the image of `augIdeal e` under the classifying map of `x`. Then `x`
  is `1` modulo `N`, hence so is `g * x * g⁻¹`, so the classifying map of `g * x * g⁻¹` sends
  `augIdeal e` into `N` and `augIdeal e ^ m` into `N ^ m`. The ideal `N ^ m` is the image of
  `augIdeal e ^ m` under the classifying map of `x`, which is zero by hypothesis.

Consequences, for an ideal `J` of `B`:

- `jetIdeal_succ_le` and `le_jetIdeal`: `jetIdeal e J (n + 1) ≤ jetIdeal e J n` and
  `J ≤ jetIdeal e J n`.
- `Stabilizes.of_succ`: a point stabilizing the subfunctor cut out by `jetIdeal e J (n + 1)` also
  stabilizes the one cut out by `jetIdeal e J n`. A point vanishing on `jetIdeal e J n` also
  vanishes on the smaller ideal `jetIdeal e J (n + 1)`, so its conjugates vanish on `J` by
  hypothesis, and they vanish on `augIdeal e ^ (n + 1)` by `VanishesOn.conj`.
- `stabilizes_of_mem`: if a subgroup family `H` is cut out by `J` (Library `IsCutOutBy e H J`),
  every `g ∈ H A` stabilizes the subfunctor cut out by `jetIdeal e J n`: conjugates of points of
  `H` by `g` lie in `H`, and `VanishesOn.conj` handles the power of the augmentation ideal.
- **`subgroupNormalizerIdeal_jetIdeal_le`**: if `H` is cut out by `J` and `B ⧸ jetIdeal e J n` is
  projective, then `subgroupNormalizerIdeal e (jetIdeal e J n) ≤ J`. Proof: the quotient map
  `B ⟶ B ⧸ J` classifies a point of `H`, which stabilizes by `stabilizes_of_mem`, so its kernel `J`
  contains the stabilizer ideal by `stabilizes_iff`.
- **`subgroupNormalizerIdeal_jetIdeal_mono`**: if `B ⧸ jetIdeal e J n` and
  `B ⧸ jetIdeal e J (n + 1)` are projective, then
  `subgroupNormalizerIdeal e (jetIdeal e J n) ≤ subgroupNormalizerIdeal e (jetIdeal e J (n + 1))`.
  Proof: the quotient map by the right-hand ideal classifies a point stabilizing the
  `(n + 1)`-st neighbourhood by `stabilizes_iff`, hence the `n`-th one by `Stabilizes.of_succ`, and
  `stabilizes_iff` again gives the inclusion.

## Provenance

These are internal helper definitions for the proof of
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. They formalize the first step of
the standard construction of a projective representation whose stabilizer is a given smooth closed
subgroup: the subgroup is recovered from the stabilizers of its infinitesimal neighbourhoods of
the unit. Here the stabilizers are described by ideals of the coordinate ring, which works over an
arbitrary base ring once the jet quotients `B ⧸ jetIdeal e J n` are projective.

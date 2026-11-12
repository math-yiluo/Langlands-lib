# The Weil class of a finite Galois extension is its fundamental class

Author: Worker 5095, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`.

Let `E/F` be a finite Galois extension of `p`-adic fields. This module shows that the
actual Weil pushout class `finiteGaloisClass F E f hE eE heE`
(`Langlands.Weil.Local.FiniteGaloisPushout`) is the fundamental class. The hypotheses
are an invariant family satisfying the relative class-formation laws and the arithmetic
normalization, and geometric Weil reciprocity for every `p`-adic field.

This is Tate, *Number theoretic background* (1979), §1.2, printed p.5 (PDF p.14):

> For E/F cyclic, this isomorphism determines a_{E/F}, and it follows that a_{E/F} is
> the "canonical" or "fundamental" class of class field theory. The same is true for
> arbitrary E/F as one sees by taking a cyclic E₁/F of the same degree as E/F, and
> inflating a_{E/F} and a_{E₁/F} to EE₁/F, where they are equal by (1.2.4).

The Lean proof follows this argument with `E₁ = M₀` unramified (hence cyclic) of
degree `[E:F]`. The Library's common closure (`exists_unramified_commonClosure`,
Worker 1839, `Langlands.Weil.Local.FiniteGaloisCommonClosure`) supplies `M₀`. It also
supplies a finite Galois `L₀` containing both, with the tower embeddings
`towerFieldEmbedding`.

All declarations are in `Langlands.Weil.Local.FiniteGaloisTower`. `LP` denotes the
intermediate field `L₀` of the closure of `F` packaged as a `p`-adic field
(`L₀.asPadicField`).

## Declarations

### `relativeInflation_finiteGaloisClass_of_le_of_norm`

For `E/F` Galois with `E ⊆ L₀` (`hEL`) and `L₀/F` Galois, with candidates `eE`, `eL`
satisfying the geometric relation:

`inf (finiteGaloisClass F E f hE eE heE) = [L₀ : E] • finiteGaloisClass F LP (ι ∘ f) _ eL heL`,

where `ι = towerFieldEmbedding F E f L₀ hEL`. This is the Library's
`relativeInflation_finiteGaloisClass_of_le` (`FiniteGaloisTowerConstruction`) without
the transfer hypothesis. The proof applies `relativeInflation_finiteGaloisClass_of_norm`
(`Langlands.Weil.Local.FiniteGaloisNormInflation`) to the tower embedding, with
`towerFieldEmbedding_isGalois` and `towerFieldEmbedding_hF1`.

### `relative_finiteGaloisClass_congr`

If `g : F → LP` equals the literal inclusion `intermediateEmbedding F L₀`, then the
invariant `J.relative F LP` of `finiteGaloisClass F LP g _ eL heL` (with `LP` an
`F`-algebra through `g`) equals the invariant of the class for the literal inclusion.
Proof: substitute `g`; both sides then agree by `rfl`.

### `relative_finiteGaloisClass_eq_of_le`

With `J.InflationCompatibility`, the invariant of the class of `E/F` is

`J.relative F E (finiteGaloisClass F E f hE eE heE) =
  [L₀ : E] • J.relative F LP (finiteGaloisClass F LP (intermediateEmbedding F L₀) _ eL heL)`.

Proof: inflation compatibility rewrites the left side as the invariant of the inflated
class. Then apply `relativeInflation_finiteGaloisClass_of_le_of_norm` and additivity of
`J.relative`. Finally use `relative_finiteGaloisClass_congr` with `towerFieldEmbedding_comp`
(`ι ∘ f = intermediateEmbedding F L₀`).

### `finiteGaloisClass_isFundamental` (main theorem)

Hypotheses:

- `hW : WeilReciprocityExistenceUniqueness.{u}`;
- `E/F` Galois for `f` (`hE`), and a candidate `eE` satisfying the geometric relation;
- an invariant family `J` with `J.RelativeClassFormation` and `J.ArithmeticNormalization`.

Conclusion:

`IsFundamentalClass F E (J.relative F E) (finiteGaloisClass F E f hE eE heE)`,

that is, its invariant is `1/[E:F]`.

Proof.

1. `exists_unramified_commonClosure` gives `M₀`, unramified over `F` of degree `[E:F]`,
   and `L₀` Galois containing the images of `E` and `M₀`.
2. `hW` provides geometric reciprocity candidates `eM` for `M₀` and `eL` for `L₀`
   (canonical topological data).
3. By `finiteGaloisClass_isFundamental_of_unramified_of_order`
   (`Langlands.Weil.Local.FiniteGaloisUnramifiedClass`), the invariant of the Weil class
   of `M₀/F` is `1/[M₀:F]`.
4. By `relative_finiteGaloisClass_eq_of_le`, applied to `E` and to `M₀`, the two
   invariants are `[L₀:E] • x` and `[L₀:M₀] • x`, where `x` is the invariant of the Weil
   class of `L₀/F`.
5. `[L₀:E] = [L₀:M₀]` because `[E:F] = [M₀:F]` (`towerFieldEmbedding_finrank_eq`). So the
   invariant of the class of `E/F` equals that of `M₀/F`, which is `1/[M₀:F] = 1/[E:F]`.

The hypothesis `hW` is used only to obtain `eM` and `eL`. Inflation compatibility is the
third component of `RelativeClassFormation`.

### The local Weil class map

The remaining declarations take the hypotheses of the main theorem together with a
normalized cocycle `z : NormalizedTwoCocycle Gal(E/F) Eˣ` whose class is fundamental
(`hz`). `E` is an `F`-algebra through `f`, and `Eˣ` carries the canonical topology of
`E`.

- `cohomologyClass_finiteGaloisCocycle_eq`: the class of the Library's Weil pushout
  cocycle `finiteGaloisCocycle F E f hE e he` equals the class of `z`. Both classes are
  fundamental, by `finiteGaloisClass_isFundamental` and `hz`. The relative invariant is
  injective (the `RelativeImages` component of `RelativeClassFormation`), so fundamental
  classes are unique.
- `weilClassMap` (definition): the continuous homomorphism `W_F →ₜ* z.Extension`
  obtained as the Library's Weil pushout `finiteGaloisPushout` (Worker 1839,
  `Langlands.Weil.Local.FiniteGaloisPushout`) followed by the continuous equivalence
  `NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq` (Worker 1556,
  `Langlands.GroupTheory.CocycleClassEquiv`) for the equality of classes above. That
  equivalence is the identity on `Eˣ` and on `Gal(E/F)`. The topology of `Gal(E/F)` is
  its Krull topology, which is discrete. The units of `E` form a topological group for the
  canonical topology, which makes `E` a nonarchimedean local field.
- `weilClassMap_projection_apply`: for `g ∈ W_F` and `x ∈ E`, the image of
  `weilClassMap g` in `Gal(E/F)` acts on `x` as `localProjection F g` does, through
  `extensionFieldEmbedding F E f : E → \bar F`. This is
  `finiteGaloisPushout_projection_apply`, since the equivalence preserves projections.
- `weilClassMap_extensionWeilMap`: for `y ∈ W_E`,
  `weilClassMap (extensionWeilMap F E f y) = (inl (reciprocityUnits E e y))⁻¹`. This
  follows from `finiteGaloisPushout_extensionWeilMap`, since the equivalence preserves the
  unit inclusion (`continuousEquivOfCohomologyClassEq_inl`).

Together these give the local Weil–Shafarevich map of Tate (1979), §1.2: `W_F` maps to
the extension attached to a fundamental class, compatibly with the Galois projection and
with inverse reciprocity on `W_E`.

## Provenance

The main theorem is the statement of Tate (1979), §1.2, printed p.5, quoted above, for
the Library's actual Weil pushout classes. The definition `weilClassMap` is the resulting
map of `W_F` into the extension attached to any fundamental class (the same section of
Tate). The proof follows Tate's argument; it uses
(1.2.4) (`relativeInflation_finiteGaloisClass_of_norm`) and the unramified case
(`finiteGaloisClass_isFundamental_of_unramified_of_order`). The three auxiliary
declarations are internal.

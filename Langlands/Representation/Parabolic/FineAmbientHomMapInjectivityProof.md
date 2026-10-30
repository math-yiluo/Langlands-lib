# Injectivity of the specified fine-to-ambient Hom map: proof

Authors: Worker 796, Worker 526 and Worker 359.

`Langlands.RelativeHomComparison.fineAmbientHomMapInjective` proves exactly
`Langlands.RelativeHomComparison.FineAmbientHomMapInjectivityStatement.{uF, uV, uW, uZ}`.
The universes of the field and of the fine, coarse and ambient representation
carriers remain independent. The statement module
`Langlands.Representation.Parabolic.FineAmbientHomMapInjectivityStatement` is
imported from the published Library unchanged; this module contains only the
proof and one helper theorem.

## The helper: actual values preserve surjections

`fineAmbientHomMap_surjective` takes the data of the public map: smooth `ω`,
arbitrary real parameters `v₀` and `t`, and arbitrary `π` and `J`. It also takes a
surjective specified outer intertwiner `q` and a surjective inner intertwiner
`f : A₀.ρ.IntertwiningMap π.ρ`, where `A₀ = innerInduced T B S (fineTwist T B S ω v₀ 0)`.
It proves that the actual value `fineAmbientHomMap T B S ω v₀ t hω π J q f`
is surjective. The proof follows the formula
`C_q(f) = q ∘ T.normalizedParabolicInducedMap B fₜ ∘ E_flat⁻¹`:

1. The source `A₀` is smooth normalized refined induction
   (`T.isSmooth_normalizedRefinedInduced`). Its surjective image is therefore
   smooth, so `IsSmooth π.ρ` holds by `isSmooth_of_surjective`. This derived
   smoothness is local to the given surjective `f`. It is not a hypothesis of the
   theorem.
2. `fₜ = coarseTwistHom T B S ω v₀ t π f` is the common-character twist of `f`
   (the same underlying map) composed with the inverse of the fixed equivalence
   `coarseTwistEquiv T B S ω v₀ t`, so it is surjective.
3. The source of `fₜ` is the smooth inner induction at parameter `t`, and its
   target `T.leviRealPowerTwist B t π.ρ` is smooth by
   `T.isSmooth_leviRealPowerTwist_iff` and step 1. The published
   `Langlands.Parabolic.normalizedInducedSurjectivity_of_smoothInductionSurjectivity`,
   applied to the proved `Langlands.Induction.smoothInductionSurjectivity`, makes
   `T.normalizedParabolicInducedMap B fₜ` surjective.
4. Rewriting the value by `fineAmbientHomMap_apply` (which holds by `rfl`), the value
   is `q` composed with that induced map, composed with the inverse of the fixed
   `flatStagesEquiv T B S ω v₀ t hω`. A composite of surjections is surjective.

The proof works with the actual value of the linear map. It does not replace
that value by an existentially chosen transport.

## The main theorem

Fix the data of the statement with `π` irreducible, `J.V` nontrivial and `q`
surjective. Write `C = fineAmbientHomMap T B S ω v₀ t hω π J q`.

- **Zero kernel.** Suppose `C f = 0` but `f ≠ 0`. Mathlib's
  `Representation.IsIrreducible.surjective_or_eq_zero` makes the nonzero
  intertwiner `f` into irreducible `π` surjective. The helper then makes `C f`
  surjective. Choose `w ≠ 0` in `J.V` (`exists_ne`), which uses nontriviality.
  A preimage `x` gives `C f x = w`, whereas `C f = 0` gives `C f x = 0`. This is a
  contradiction, so `f = 0`.
- **Injectivity.** For arbitrary inner intertwiners `f` and `g` with `C f = C g`,
  linearity gives `C (f - g) = C f - C g = 0`, so `f - g = 0` and `f = g`.

The argument covers the whole Hom space, including zero and non-surjective maps,
because the zero-kernel step is applied to the arbitrary difference `f - g`.

## Hypotheses used

The proof uses only the hypotheses of the statement: smoothness of `ω`
(needed already to form the map), irreducibility of `π`, nontriviality of
`J.V`, and surjectivity of `q`. Smoothness of `π` is derived, not assumed. No
positive rank, irreducibility of `J`, admissibility, cuspidality, unitarity,
temperedness, chamber, support, finite-length, finite-dimensionality or
chosen-equivalence hypothesis appears. Every normalization of the public map is
used unchanged: the normalized upper parabolic inductions with right
translation and positive-half covariance, the fine exponent
`-v₀ k + t ((B.flattenBlockEquiv S).symm k).1`, the residue-normalized
determinant characters, and the fixed equivalences `coarseTwistEquiv` and
`flatStagesEquiv`.

## Provenance and scope

This is an internal algebraic deduction, not a theorem transcribed from the
literature. It adapts the unreviewed prototype
`FineAmbientHomMapInjectivityPrototype` from shared draft revision 8 of parent
task `ebf9d80c-dcd4-45c5-91f8-428ad29b1363`. Worker 359 supplied the
nonzero-map argument and its application to arbitrary differences. Worker 526
implemented the actual surjection-preservation step. Worker 796 adapted the
prototype to the published statement: the helper was renamed and the main
theorem now proves the published proposition. The proof itself is unchanged.
The imported map `fineAmbientHomMap` was constructed by Workers 796, 430, 435
and 373. The use of smooth induction surjectivity follows the published
specified-surjection transport `Langlands.fineAmbientQuotientTransport` of
Workers 373 and 430. These imports keep their own provenance.

The module proves neither surjectivity of the map between Hom spaces nor any
reverse dimension inequality. It also gives no analytic reflection or
continuation and does not prove the parent J-specific relative comparison.

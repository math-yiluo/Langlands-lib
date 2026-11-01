# The global closed normalized Harris determinant locus in a supplied family

Author: Worker 344.

This internal construction produces a global closed determinant locus
inside the base of a supplied actual abelian scheme with rational algebra
action. It uses the existing normalized Harris determinant condition with
its conjugated reflex scalar map. Neither an affine base nor a global
finite free Lie chart is assumed.

The arithmetic parameters are the existing universe-zero totally real
field `E`, totally complex quadratic extension `F`, central simple unitary
datum `D`, imaginary quadratic field `L` with its embedding into `F`, and
normalized Harris signature charts `C`. The geometric input consists of
an arbitrary universe-zero scheme `S`, an actual `p : S ⟶ Spec F`, an
actual `B : AbelianScheme S`, and `i : A →ₐ[ℚ] End0 B`. There is no added
`IsCMField F` hypothesis. Division of the algebra is not used for this
closed-locus construction.

`harrisTaylorCMGlobalDeterminantLocus` is an actual scheme and
`harrisTaylorCMGlobalDeterminantLocusι` is an actual closed immersion into
`S`. For every universe-zero test scheme `T` and actual map `g : T ⟶ S`,
`harrisTaylorCMGlobalDeterminantLocus_factors_iff` proves

```text
(∃ k : T ⟶ harrisTaylorCMGlobalDeterminantLocus, k ≫ ι = g)
  ↔ HarrisTaylorCMRationalLieDeterminantCondition
       C (g ≫ p) ((baseChange g).obj B)
       ((rationalBaseChangeEnd g B).comp i).
```

Thus factorization detects the full existing condition for every finite
order family, every finite Lie chart and every smaller open. The test
scheme has no affineness, flatness or reducedness hypothesis. The condition
is equality in actual structure-sheaf section rings and retains nilpotent
coefficients. It is not replaced by a condition only on geometric points.

The implemented proof has the following parts.

1. `harrisTaylorCMDeterminantPullbackCondition_baseChange_iff` compares the
   determinant property formed from the actual pulled-back family along
   `b : T ⟶ S`, followed by `g : T' ⟶ T`, with the property of `g ≫ b`
   for the original family. It unfolds the existing class-based
   `HarrisTaylorCMDeterminantPullbackCondition`. The equality of the
   rational-action classes follows from `pullbackClass_comp`, which uses
   the existing actual pullback comparison. Associativity identifies the
   structure maps. No literal equality between differently parenthesized
   actual abelian schemes is assumed.

2. `harrisTaylorCMDeterminantCoverData` uses `affineLieBasisCover B`.
   Each member is affine and has the constructed
   `affineLieBasisTrivialization B V` on the actual pullback of `B`.
   The local object and inclusion are precisely
   `harrisTaylorCMDeterminantLocus` and
   `harrisTaylorCMDeterminantLocusι` for that family, that pulled-back
   rational action, and that chart. The local closedness instance is
   inherited. The local factorization equivalence applies the affine
   locus theorem, converts its actual representative condition to the
   class-based test-map condition, then uses the comparison in part 1.
   Consequently these are genuine local charts for one common property
   of all maps into `S`.

3. The actual global scheme and inclusion apply
   `ClosedLocusFromDirectedCover.Data.scheme` and `.inclusion` to these
   constructed charts. The cover's inclusion preorder is small and thin,
   and its locally directed structure has already been proved.
   Precomposition stability is supplied by
   `harrisTaylorCMDeterminantPullbackCondition_comp`.
   The generic construction determines the transition maps by local
   factorization, proves their cartesian property, glues the actual
   schemes, and proves that its inclusion is closed.

4. The global factorization theorem applies the generic `.factors_iff`.
   Its locality hypothesis is supplied by
   `harrisTaylorCMDeterminantPullbackCondition_of_openCover` on the
   pullback of the affine Lie-basis cover along the arbitrary test map.
   The existing
   `harrisTaylorCMDeterminantPullbackCondition_iff` then recovers exactly
   the determinant predicate on the actual single-step pullback family
   and action displayed above.

`harrisTaylorCMGlobalDeterminantLocus_unique_factors_iff` strengthens the
factorization to a unique actual scheme map, because a closed immersion
is a monomorphism. In particular the chosen local charts introduce no
ambiguity in lifts. `harrisTaylorCMGlobalDeterminantLocus_condition`
applies the factorization criterion to the inclusion and its identity
lift: the actual pulled-back universal family over this closed locus
satisfies the unchanged normalized all-family determinant condition.

The provenance is internal. The coefficient-locus construction supplies
the full-section equations and the unchanged conjugated reflex map; the
affine Lie cover, actual rational-action class coherence, determinant
locality and generic closed-locus gluing supply the remaining steps.
There is no new external representability assertion or assumed global
locus.

This result is a closed locus in a supplied family. It does not construct
the ambient polarized PEL moduli scheme, impose its polarization,
Rosati or level-orbit conditions, identify the rational-isogeny moduli
quotient, or prove admissibility, smoothness, projectivity or the
normalized natural moduli comparison required by the full division-case
representability statement. Those remain separate obligations.

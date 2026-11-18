# Geometry of the chosen dual parameter scheme over a quasi-separated base: proof

Worker 892, 17 November 2026.

## Result

`Langlands.AbelianScheme.relativeDualSchemeGeometry` has type exactly
`Langlands.AbelianScheme.RelativeDualSchemeGeometryStatement.{u}`. That statement is
imported by Lean name from
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement`.
Let `S : Scheme.{u}` satisfy `QuasiSeparatedSpace S`, let `A : AbelianScheme S`, and let
`hA : HasDualScheme A` be an actual universal Picard-zero family that classifies every
test scheme. For all such data the theorem proves `DualSchemeGeometry A hA`: the
structure morphism `(dualScheme A hA).hom` of the chosen dual is smooth, proper and
geometrically connected. The proof adds no hypothesis. The base stays
quasi-separated as in the statement, and `hA` is any proof of `HasDualScheme A`; the
proof does not choose a particular one.

The module also proves a helper lemma,
`Langlands.AbelianScheme.dualScheme_smooth_of_quasiSeparated`: for `S` quasi-separated,
`A : AbelianScheme S` and `hA : HasDualScheme A`, the morphism
`(dualScheme A hA).hom` is smooth.

## Implemented proof

### Smoothness (`dualScheme_smooth_of_quasiSeparated`)

1. **An abelian scheme carrying a universal family.** The published
   `smoothFamilyAbelianRepresentabilityOfFiniteType`, applied to the published
   `finiteTypeSmoothFamilyAbelianRepresentability`, is a proof of
   `SmoothFamilyAbelianRepresentabilityStatement.{u}`. Applied to `S` and `A`, it gives
   an abelian scheme `B : AbelianScheme S`, a rigidified family
   `L : RigidifiedFamily A B.X`, and a proof `hL` that `L` is universal for
   smooth-family classes on quasi-separated test schemes.
2. **Universality on all test schemes.** The published
   `universalPicardZeroOnQuasiSeparatedTests_of_smoothFamily` (module
   `RelativeDualSchemeExistenceProof`) turns `hL` into universality for geometric
   Picard-zero classes on quasi-separated tests. The published
   `picardZeroQuasiSeparatedExtension` then extends this to every test scheme, giving
   `hU : IsUniversalPicardZero A L`. The proof of `relativeDualSchemeExistence` uses the
   same two steps; here the abelian-scheme structure of `B` is kept for step 3.
3. **Transport of smoothness.** `dualScheme A hA` and `B.X` both carry universal
   Picard-zero families. The published
   `smooth_dualScheme_iff_of_universal A hA L hU` (module `DualSchemeSmoothTransport`)
   proves `Smooth (dualScheme A hA).hom ↔ Smooth B.X.hom`. It uses the
   isomorphism `dualSchemeIsoOfUniversal` over `S`, which is built from
   `picardZeroUniversalUniqueness` and the published rigidified pullback coherence.
   The right-hand side holds by the instance `AbelianScheme.smooth` for `B`, so the
   left-hand side holds.

### Geometry (`relativeDualSchemeGeometry`)

With smoothness available as a local instance, the published
`dualSchemeGeometry_of_smooth relativeDualSchemeValuativeExistence A hA` (module
`DualSchemeGeometryAssembly`) gives `DualSchemeGeometry A hA`.

- Smoothness is the instance from the previous section.
- Properness is `dualScheme_isProper_of_smooth_of_valuativeExistence`. It combines
  separatedness (`relativeDualSchemeSeparated`), quasi-compactness of a smooth chosen
  dual over a quasi-separated base (`dualScheme_quasiCompact_of_smooth`), and universal
  closedness from the valuative criterion applied to the published
  `relativeDualSchemeValuativeExistence`. Local finite type follows from smoothness by
  instance.
- Geometric connectedness is `dualScheme_geometricallyConnected`, proved over every base.

## Relation to the earlier reduction

An earlier published reduction, `relativeDualSchemeGeometryFlatReduction` (module
`RelativeDualSchemeGeometryFlatReduction`), derives the same target from three inputs:
field smoothness, relative flatness and relative local finite presentation of the
chosen dual. This proof does not use it. Once the representer of step 1 was
published, transporting smoothness from `B.X` avoided the separate flatness input.
Workers 3269 and 3449 pointed out this route.

## Provenance

This is an internal composition of published Library theorems. The source mathematics
(the dual abelian scheme as the identity component of the relative Picard functor,
following Lan's revised thesis, Theorem 1.3.2.3, over quasi-separated bases) is
documented in `RelativeDualSchemeGeometryStatement.md` and in the paired Markdown of
the imported results. This module adds no construction and no new source comparison.

The proof uses no `sorry`, `admit` or new axiom. A development `lean_check` reported
0 errors, 0 warnings, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

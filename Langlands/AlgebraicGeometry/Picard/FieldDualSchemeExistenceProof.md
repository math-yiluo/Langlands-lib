# Existence of the universal geometric Picard-zero family over a field: proof

Author: Worker 603.

`Langlands.AbelianScheme.fieldDualSchemeExistence.{u}`, in module
`Langlands.AlgebraicGeometry.Picard.FieldDualSchemeExistenceProof`, proves
the unchanged published statement
`Langlands.AbelianScheme.FieldDualSchemeExistenceStatement.{u}` for every
universe `u`. For every field `k : Type u` and every
`A : AbelianScheme (Spec k)`, it gives `HasDualScheme A`: there are an
actual scheme `P` over `Spec k` and an actual rigidified family
`L : RigidifiedFamily A P` with `IsUniversalPicardZero A L`. That is, `L`
is geometrically Picard-zero, and its actual rigidified pullback classifies
every geometric Picard-zero rigidified class over every test `k`-scheme
(nonreduced ones included) by a unique morphism to `P`.

The field `k` is arbitrary; it need not be perfect or algebraically closed.
No hypothesis is added, and no universe or quantified object is changed.

## Published inputs

The proof applies one published conditional reduction to one published
proof.

| Library theorem | Module | Content |
| --- | --- | --- |
| `Langlands.AbelianScheme.fieldDualSchemeExistence_of_rigidifiedRepresentability` | `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeExistenceReduction` | `FieldRigidifiedPicardRepresentabilityStatement.{u}` implies `FieldDualSchemeExistenceStatement.{u}`. |
| `Langlands.AbelianScheme.fieldRigidifiedPicardRepresentability` | `Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityProof` | Proves `FieldRigidifiedPicardRepresentabilityStatement.{u}`. For every abelian scheme over a field, it gives a parameter scheme locally of finite type and a rigidified family that is universal for all rigidified line-bundle classes. |

## Proof

The theorem is the term

```
fieldDualSchemeExistence_of_rigidifiedRepresentability
  fieldRigidifiedPicardRepresentability
```

at universe `u`. The imported reduction, described in the paired Markdown
of `FieldDualSchemeExistenceReduction`, runs as follows for a field `k` and
an abelian scheme `A` over `Spec k`.

1. `fieldRigidifiedPicardRepresentability` gives an ambient parameter
   `P` and a family `L : RigidifiedFamily A P` that is universal for every
   rigidified line-bundle class.
2. `exists_geometricPicardZeroOpenLocus` gives an open subset `U` of
   `P.left`. Its input is the Library's Mumford criterion
   (`mumfordTrivialLocus`, `isTranslationInvariant_fibreLineBundle_iff`),
   and `picardZeroGeometricDetection` turns it into
   `IsPicardZeroOpenLocus A L U`. So a morphism from any test scheme into
   `P` pulls `L` back to a Picard-zero class exactly when its image lies
   in `U`.
3. `geometricPicardZeroParameter A L` is the open subscheme `U` over
   `Spec k`. `geometricPicardZeroFamily A L` is the actual restriction of
   `L` to it. `geometricPicardZeroFamily_universal` (via
   `restrictedRigidifiedFamily_universal`) shows that this restriction
   satisfies `IsUniversalPicardZero`. Ambient universality classifies a
   Picard-zero class by a unique map into `P`, the image of that map lies
   in `U`, and the open immersion gives the unique lift.
4. `hasDualScheme_of_rigidifiedUniversal` packages the parameter, family
   and universality proof as `HasDualScheme A`.

The local-finite-type conclusion of the representability theorem is not
used. `lean_check` reports that the theorem depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This proof composes published Library results and makes no new
mathematical claim. It follows the route of Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, preliminary draft (registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter VI §3,
printed p.95–96 (PDF pp.99–100). There, representability of the Picard
functor of an abelian variety over a field gives a scheme with a
Poincaré bundle, and Definition (6.19) restricts that bundle to the
Picard-zero part. The Library chooses the Picard-zero part as an open
locus by a geometric translation-invariance criterion. It does not
identify that locus with the identity component of the Picard scheme.

## Scope

The theorem asserts only what the target states: a parameter scheme and a
universal Picard-zero family exist. It gives no group structure,
smoothness, properness, geometric connectedness, projectivity or
dimension for the parameter scheme. Those are separate Library
statements.

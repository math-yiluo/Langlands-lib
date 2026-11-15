# Geometry of the chosen dual over a finite-type integer algebra

This module proves the published statement
`Langlands.AbelianScheme.FiniteTypeDualSchemeGeometryStatement.{u}` (module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryStatement`). It
adds no definitions and no new hypotheses.

## Theorem

`Langlands.AbelianScheme.finiteTypeDualSchemeGeometry :
FiniteTypeDualSchemeGeometryStatement.{u}`.

So for every commutative ring `R : Type u` with `[Algebra.FiniteType ℤ R]`, every
abelian scheme `A : AbelianScheme (Spec (CommRingCat.of R))` and every proof
`hA : HasDualScheme A`, the predicate `DualSchemeGeometry A hA` holds. This means
the structure morphism `(dualScheme A hA).hom` of the chosen parameter scheme to
`Spec R` is smooth, proper and geometrically connected (Mathlib's `Smooth`,
`IsProper` and `GeometricallyConnected`). The statement is conditional on `hA`:
it does not assert that a dual scheme exists.

## Proof

The proof is one term. It applies three published theorems:

```lean
finiteTypeDualSchemeGeometryReduction relativeDualSchemeValuativeExistence.{u}
  picardZeroArtinianLifting.{u}
```

- `finiteTypeDualSchemeGeometryReduction :
  FiniteTypeDualSchemeGeometryReductionStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.DualSchemeGeometryAssembly`). Its type is
  `RelativeDualSchemeValuativeExistenceStatement.{u} →
  PicardZeroArtinianLiftingStatement.{u} → FiniteTypeDualSchemeGeometryStatement.{u}`.
- `relativeDualSchemeValuativeExistence :
  RelativeDualSchemeValuativeExistenceStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceProof`).
  Over every quasi-separated base, `(dualScheme A hA).hom` satisfies the existence
  part of the valuative criterion.
- `picardZeroArtinianLifting : PicardZeroArtinianLiftingStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingProof`). Geometric
  Picard-zero rigidified families on an abelian scheme lift along elementary
  thickenings of local Artinian rings.

Inside the published reduction the three properties come from these steps.

1. *Smoothness.* `R` is noetherian, being of finite type over `ℤ`.
   `finiteType_dualScheme_smooth_of_picardZeroArtinianLifting` (module
   `DualSchemeSmoothOfArtinianLifting`) turns the Artinian lifting theorem into
   `Smooth (dualScheme A hA).hom`.
2. *Geometric connectedness.* `dualScheme_geometricallyConnected` holds over every
   base. Each residue-field fibre of the chosen dual is identified with the chosen
   dual of the base-changed abelian scheme over the residue field
   (`dualSchemeResidueFieldIso`). That one is geometrically connected by
   `fieldDualSchemeGeometricallyConnected`.
3. *Properness.* `Spec R` is affine, hence quasi-separated. The chosen dual is
   separated (`relativeDualSchemeSeparated`). Being smooth, it is quasi-compact
   (`dualScheme_quasiCompact_of_smooth`, from the proper geometrically connected
   residue fibres of the smooth group scheme). The valuative existence theorem
   gives universal closedness by Mathlib's
   `UniversallyClosed.of_valuativeCriterion`. Together these give `IsProper`.

`lean_check` of this module reports no errors or warnings. The theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Excluded inputs

The task forbids `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`,
`SmoothFamilyAbelianRepresentabilityStatement`, their proofs and any route
through them, because they consume this result. The source text of the 2,343
`Langlands` modules in this module's import closure (Library commit
`4abbe7aabd9c92005d91c9d5bba86b879e928bb3`) contains no occurrence of
`SmoothFamilyAbelianRepresentability`.

## Provenance

The result is the specialization to `Spec R`, `R` of finite type over `ℤ`, of the
statement on printed p.3 (PDF p.15) of G. Faltings and C.-L. Chai, *Degeneration
of Abelian Varieties* (1990), Chapter I: `Aᵗ = Pic⁰(A/B)` is proper and smooth
over `B`. With Definition 1.1, printed p.1 (PDF p.13), this includes geometrically
connected fibres. The source is registered as
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`
(SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`).
The statement's paired Markdown records how the Lean target differs from the
source. Smoothness through Artinian lifting is the route of Remark 1.5(c),
printed p.2 (PDF p.14): `Pic⁰(X/S)` is formally smooth. The Lean proof given here
only assembles published Library theorems. It follows the Library's reduction,
not a route taken from the source.

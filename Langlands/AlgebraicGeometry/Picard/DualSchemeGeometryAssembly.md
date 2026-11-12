# Reduction of the finite-type geometry of the chosen dual

This module reduces the geometry of the actual chosen parameter scheme
`dualScheme A hA` to two inputs: smoothness and valuative existence. It proves
geometric connectedness over every base unconditionally. Its main declaration
is the reduction proposition `FiniteTypeDualSchemeGeometryReductionStatement`,
proved here as `finiteTypeDualSchemeGeometryReduction`.

## The reduction statement

`FiniteTypeDualSchemeGeometryReductionStatement.{u}` is the implication

```
RelativeDualSchemeValuativeExistenceStatement.{u} →
  PicardZeroArtinianLiftingStatement.{u} →
    FiniteTypeDualSchemeGeometryStatement.{u}
```

All three propositions are published Library statements, used unchanged:

- `RelativeDualSchemeValuativeExistenceStatement`: for every quasi-separated
  scheme `S`, every abelian scheme `A` over `S` and every
  `hA : HasDualScheme A`, the structure morphism of the chosen dual satisfies
  the existence part of the valuative criterion;
- `PicardZeroArtinianLiftingStatement`: geometric Picard-zero rigidified
  families lift along elementary Artinian thickenings;
- `FiniteTypeDualSchemeGeometryStatement`: for every commutative ring `R` of
  finite type over `ℤ`, every abelian scheme `A` over `Spec R` and every
  `hA : HasDualScheme A`, the structure morphism of `dualScheme A hA` is
  smooth, proper and geometrically connected (`DualSchemeGeometry A hA`).

The reduction proves neither hypothesis. Each input is the subject of separate
proof work.

## Residue fibres

`dualScheme_fiberToSpecResidueField_isProper_geometricallyConnected` holds
for every scheme `S`, every abelian scheme `A` over `S`, every
`hA : HasDualScheme A` and every point `s`. It proves that
`(dualScheme A hA).hom.fiberToSpecResidueField s` is proper and geometrically
connected. Let `b = S.fromSpecResidueField s` and let `A'` be the base change
of `A` along `b`, with `hA'` from `hasDualScheme_baseChange`. Then:

- `dualScheme_locallyOfFiniteType` gives local finite type of the chosen dual
  of `A'` over the affine scheme `Spec κ(s)`;
- the published field lemmas `fieldDualSchemeProper_of_locallyOfFiniteType`
  and `fieldDualSchemeGeometricallyConnected` (module
  `FieldDualSchemeGeometryReduction`) give properness and geometric
  connectedness of that chosen dual. Neither uses smoothness: they rest on
  `fieldDualSchemeSeparated` and `fieldDualSchemeSurjection`;
- the published `dualSchemeResidueFieldIso` identifies the fibre of the
  chosen dual over `s` with the chosen dual of `A'` over `Spec κ(s)`, and
  both properties are transported along this isomorphism.

## Geometric connectedness

`dualScheme_geometricallyConnected` holds for every scheme `S`, every abelian
scheme `A` over `S` and every `hA : HasDualScheme A`. Mathlib's
`GeometricallyConnected.iff_geometricallyConnected_fiber` reduces it to
geometric connectedness of every residue fibre, proved above.

## Quasi-compactness and properness under smoothness

`dualScheme_quasiCompact_of_smooth` assumes `[QuasiSeparatedSpace S]` and a
`Smooth` instance for the structure morphism of the chosen dual. It proves
that this morphism is quasi-compact, using the group scheme structure from
`nonempty_grpObj_dualScheme` and the criterion `quasiCompact_of_residueFibers`
of this unit. The criterion needs, for every `s`:

- a smooth residue fibre: the residue fibre is a base change of the smooth
  structure morphism (Mathlib's base-change instance for `Smooth`);
- a connected fibre: it is geometrically connected over `κ(s)`, by the
  residue-fibre lemma above;
- a compact fibre: it is proper, hence quasi-compact, over the one-point
  space `Spec κ(s)`.

`dualScheme_isProper_of_smooth_of_valuativeExistence` assumes the proposition
`RelativeDualSchemeValuativeExistenceStatement.{u}` as an explicit hypothesis,
a quasi-separated base and the `Smooth` instance. It proves properness from:

- separatedness, from the published `relativeDualSchemeSeparated`;
- quasi-compactness, from `dualScheme_quasiCompact_of_smooth`;
- universal closedness, from Mathlib's `UniversallyClosed.of_valuativeCriterion`
  applied to quasi-compactness and the assumed valuative existence;
- local finite type, which follows from smoothness;
- `isProper_iff`, which combines these.

## Conditional assemblies

`dualSchemeGeometry_of_smooth` proves `DualSchemeGeometry A hA` over a
quasi-separated base, assuming valuative existence and a `Smooth` instance
for the chosen dual.

`finiteTypeDualSchemeGeometry_of_smooth` proves
`FiniteTypeDualSchemeGeometryStatement.{u}`. It assumes valuative existence
and smoothness of the chosen dual over `Spec R` for every finite-type
`ℤ`-algebra `R`. Both are explicit hypotheses. `Spec R` is affine, hence
quasi-separated.

`finiteTypeDualSchemeGeometryReduction` proves the reduction statement. It
passes to `finiteTypeDualSchemeGeometry_of_smooth` the smoothness supplied by the
published `finiteType_dualScheme_smooth_of_picardZeroArtinianLifting`
(module `DualSchemeSmoothOfArtinianLifting`), which derives smoothness over
`Spec R`, for `R` of finite type over `ℤ`, from
`PicardZeroArtinianLiftingStatement`.

## Scope

Every quasi-compactness and properness result here assumes smoothness of the
chosen dual over the given base. The unit proves none of the separate Library
targets `FieldDualSchemeSmoothStatement`, `FieldDualSchemeGeometryStatement`
or `RelativeDualSchemeQuasiCompactStatement`, and does not use them.

## Supporting module in this unit

The unit also adds
`Langlands.GroupScheme.RelativeIdentityComponent.QuasiCompactOfFibres`: a
group scheme over a quasi-separated base with smooth, connected,
quasi-compact residue fibres is quasi-compact. Its own Markdown explains the
proof.

## Provenance

This is internal derived mathematics. No source states the reduction
proposition. It records how Faltings–Chai's assertion (Chapter I, printed
p.3) that the dual of an abelian scheme is proper and smooth with
geometrically connected fibres splits into a valuative input, the formal
smoothness of `Pic⁰` (Remark 1.5(c), printed p.2) and the fibrewise
properties. It combines published Library theorems with Mathlib's valuative
criterion, its fibrewise characterization of geometric connectedness and the
base-change stability of smoothness. No representability result is used:
neither `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` nor
`SmoothFamilyAbelianRepresentabilityStatement` is in the import closure.

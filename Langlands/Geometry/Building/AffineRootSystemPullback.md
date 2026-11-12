# Affine root systems detected by pullback along a surjective affine map

This internal helper module, in namespace
`Langlands.Geometry.Building.AffineRootSystem`, transfers the affine root
system axioms along a surjective real affine map `π : A → A'`. It serves the
proof that AS 2 and AS 3 pass from an apartment class of `G` to its
restriction to a Levi subgroup, where `π` is the projection of apartments.

## Setting

`Ψ` is a set of affine functionals on `A` and `Ψ'` a set of affine
functionals on `A'`, with `ψ' ∈ Ψ'` exactly when `ψ' ∘ π ∈ Ψ`. Affine root
systems are the Library predicate `IsAffineRootSystemWithRankZero` (KP
Definition 1.3.1, admitting rank zero), from
`Langlands.Geometry.Building.RankZeroAffineRootSystem`.

## Results

- `comp_injective_of_surjective`, `linear_comp_injective_of_surjective`:
  pullback of affine functionals along `π`, and of linear forms along its
  linear part, is injective.
- `exists_comp_eq_of_linear_eq`: an affine functional on `A` whose derivative
  factors through `π.linear` is the pullback of an affine functional on `A'`
  with the given derivative.
- `sub_smul_comp`, `smul_comp'`: pullback commutes with `η - c • ψ` and with
  scalar multiples.
- `isCoroot_unique_of_finite_of_span`: a coroot vector is unique when the
  derivatives are finite and span (KP Remark 1.3.2 (2)). The proof applies
  Mathlib's `Module.Dual.eq_of_preReflection_mapsTo` and
  `Module.eval_apply_injective`.
- `span_eq_top_of_finite_of_forall_eq_zero`: a finite set of linear forms with
  trivial common kernel spans the dual. The proof uses Mathlib's
  `Subspace.dualCoannihilator_dualAnnihilator_eq`.
- `derivativeRoots_eq_of_comp`: if membership is detected by pullback, the
  derivatives of `Ψ'` contained in `R` equal `R` once every form of `R` pulls
  back to a derivative of `Ψ`.
- `isAffineRootSystemWithRankZero_of_comp`: if `π` is surjective, `Ψ` is an
  affine root system, membership in `Ψ'` is detected by pullback, and the
  derivatives of `Ψ'` span, then `Ψ'` is an affine root system.

## Proof of the main result

Finiteness of the derivatives of `Ψ'` follows by injectivity of linear
pullback from finiteness for `Ψ`. Nonzero derivatives pull back to nonzero
derivatives. A coroot `v` of `ψ' ∘ π` for `Ψ` maps to a coroot `π.linear v`
of `ψ'` for `Ψ'`, because pullback commutes with `η' - c • ψ'`. Integrality
of the pairings uses coroot uniqueness for `Ψ'`, so the chosen coroot of
`Ψ'` is the image of one for `Ψ`. Each infinite fibre of `Ψ` over a
derivative consists of pullbacks, by `exists_comp_eq_of_linear_eq`, so
the fibres of `Ψ'` are infinite. Bounded-value finiteness transfers by
injectivity of pullback, since a bound on `A'` gives the same bound on `A`.

## Provenance

Derived. KP §6.7.2 obtains the affine roots of a Levi subgroup from those of
`G` through the projection of apartments. This module isolates the
corresponding statement about abstract affine root systems; it uses no source
assertion beyond KP Definition 1.3.1 and Remark 1.3.2 as encoded in the
Library predicate.

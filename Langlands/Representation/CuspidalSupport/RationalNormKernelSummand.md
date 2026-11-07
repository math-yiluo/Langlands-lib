# A smooth summand of a restriction, from an invariant subspace

Author: Worker 1842.

Module `Langlands.Representation.CuspidalSupport.RationalNormKernelSummand`, namespace
`Langlands.CuspidalSupport`.

The first clause of Renard VI.3.2(i), the published `RationalNormKernelOrbitStatement`,
supplies an irreducible invariant subspace
`W : Subrepresentation (π.representation.comp (rationalCommonNormKernel G).subtype)`.
The VI.4.1 and VI.4.4 statements (`RationalSummandHomEquivalenceStatement`,
`RationalSummandCenterGroupAlgebraStatement`) instead quantify over an irreducible
`ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)` and an injective
`j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`. This module
converts the first into the second. It is stated for an arbitrary subgroup `H` of a
topological group `G : Type uF` and an arbitrary `π : SmoothRep.{0, uF, uV} ℂ G`.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`), VI.3.2 (printed
pp.143–144 / PDF pp.149–150), where the irreducible subrepresentations ρ of the
restriction of π to ⁰G are the ones used in VI.4.1–VI.4.5 (printed pp.149–160 / PDF
pp.155–166). Provenance: internal adapter between two published Lean interfaces. No
source statement is translated.

## Declarations

- `restrictionSummand H π W : SmoothRep.{0, uF, uV} ℂ H` is the published
  `SmoothRep.subrepresentation (SmoothRep.restrictSubgroup H π) W`. It is Mathlib's
  subrepresentation of the restriction on the submodule `W`, with the carrier of `π`
  (a submodule of it, in `Type uV`). The published constructor inherits smoothness
  through the injective inclusion. `W` is a subrepresentation of
  `π.representation.comp H.subtype`, which is by definition the representation of
  `SmoothRep.restrictSubgroup H π`.
- `restrictionSummandι H π W : restrictionSummand H π W ⟶ SmoothRep.restrictSubgroup H π`
  is the published inclusion `SmoothRep.subtype`.
- `restrictionSummandι_injective`: the underlying linear map of
  `restrictionSummandι H π W` (`SmoothRep.hom`) is injective. This is
  `SmoothRep.subtype_injective`.
- `restrictionSummand_isIrreducible H π W hW`: if `W.toRepresentation.IsIrreducible`,
  then `(restrictionSummand H π W).IsIrreducible`. The proof is the hypothesis itself.
  `SmoothRep.IsIrreducible` is `Representation.IsIrreducible` of the representation
  of `restrictionSummand H π W`, and that representation is definitionally
  `W.toRepresentation`.

With `H = rationalCommonNormKernel G`, the pair
`(restrictionSummand H π W, restrictionSummandι H π W)` is exactly the input `(ρ, j)`
of the VI.4.1 and VI.4.4 statements, together with the two premises `ρ.IsIrreducible`
and `Function.Injective (SmoothRep.hom j)`.

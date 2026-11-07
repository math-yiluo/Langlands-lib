# Prime-to-`m` cohomology of the actual geometric CM tower

This internal construction applies the restricted away cohomology of
`Langlands.Shimura.RestrictedSplitLevelTowerCohomology` to the published
actual geometric CM scheme tower and its shrinking-level cohomology
(`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`). For `m ≠ 0`
it splits the level group `GG(A_f)ᵐᵒᵖ` of the rational involution of `D` as
the opposite points at the places dividing `m` times the opposite
prime-to-`m` points. It fixes a level `K₀` at the places dividing `m` and
forms the tower of CM schemes at the sufficiently small levels
`e⁻¹ (K₀ × K')`, indexed by the prime-to-`m` levels `K'`. It then forms its
colimit cohomology with the action of `GG(A_f^{(m)})ᵐᵒᵖ` and compares it
with the shrinking-level cohomology of the CM tower. If `K₀` is sufficiently
small at one place dividing `m`, every prime-to-`m` level occurs, and the
construction gives a tower and cohomology over all prime-to-`m` levels. All
declarations are in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Proposition 4.10 on printed p. 311, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies, with the component of the level at `ℓ, p` fixed. In
this module the fixed component is `K₀` at the places dividing `m`, and the
varying one is the prime-to-`m` level `K'`.

The module constructs no spectral sequence and no new scheme: the schemes are
those of the published `cmGeometricSchemeTower`. It does not vary `K₀` and
does not show that levels `K₀` satisfying `CMDividingLevelSufficientlySmall`
exist. In the rational case the places dividing `m` are the finite places of
`ℚ` whose prime ideal contains `m`; they are not identified with rational
primes. The rational involution of `D` is not identified with Harris's
inner form, and its finite adelic points are not identified with Harris's
`GG(A_f)`. Harris's passage is motivation only; no statement from it is
formalized.

## Inputs

The CM data are those of the published
`HarrisTaylorCMSmallLevelCohomology`: the number fields `E`, `F`, `L` with
their CM and quadratic structures, the central simple unitary data `D`,
the Harris signature charts `C`, the named propositions `preservation`
through `htor`, and `q : CMRepresentabilityStatement ...`. That module
provides `SmallCMLevel D` (the sufficiently small levels of
`D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`), the tower
`cmGeometricSchemeTower ... q : SmallCMLevel D ⥤ Scheme`,
`cmGeometricSchemeTower_restrictedSelfArrow`, and, under the further explicit
inputs `existence`, `geometry`, `hRigid` and `criterion`, the étaleness of its
arrows `cmSmallLevelTowerEtale`, the coefficient diagrams
`cmSmallLevelCoefficientDiagram ... R`, the level-triviality property
`cmSmallLevelTrivialCoefficients`, the degreewise cohomology
`cmSmallLevelCohomology` and the shrinking-level colimit cohomology
`cmSmallLevelColimitCohomology ... R coeff d`, an object of
`Action (ModuleCat R) D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`. All scheme
and coefficient-ring universes are zero, and the finite dimensionality of
the algebra over `ℚ` is derived as in that module.

The module `Langlands.Shimura.Unitary.OppositePointsSplit`, submitted together
with this one, provides `finiteAdelicPointsOpSplit`,
`DividingLevelSufficientlySmall` and `levelSufficientlySmall_transport_prod`.
The module `Langlands.Shimura.RestrictedLevelTowerExtension`, submitted
together with this one, provides `extendTower`, `extendCoefficients`,
`isLevelTrivialCoefficients_extend`, `colimitCohomologyExtendIso` and
`smoothColimitCohomologyExtendIso`.

The module `Langlands.Shimura.RestrictedSplitLevelTowerCohomology`, from an
earlier accepted submission, provides, for a splitting `e : G ≃ₜ* H × H'`, a
level `K₀` of `H` and a property `P` of levels of `G`: `awayProperty e P K₀`,
`awayFunctor e P K₀`, `awayLevelTower e K₀ T`, `awayLevelTower_selfArrow`,
`awayCoefficients e K₀ D`, `isLevelTrivialCoefficients_away`,
`awayCohomologyComparison`, `ι_awayCohomologyComparison`,
`translate_awayCohomologyComparison_apply_of_mem` and `awayCohomologyIso`.
The published `Langlands.Shimura.SplitLevelTower` provides `factorHom e`,
`awayHom e` and `awayOver e K₀`. The published
`Langlands.Shimura.RestrictedLevelTowerCohomology` and
`Langlands.Shimura.LevelTowerCohomology` provide the coefficient diagrams,
level triviality, `colimitCohomology` and `smoothColimitCohomology` over
levels satisfying a property and over all levels.

## The tower

Let `m : ℕ` and `hm : m ≠ 0`. Write `G` for
`D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ` and `small` for
`D.rationalInvolution.LevelSufficientlySmall`.

- `cmPrimeToSplit D m hm` is
  `D.rationalInvolution.finiteAdelicPointsOpSplit m hm`, the isomorphism of
  topological groups
  `G ≃ₜ* (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ × (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.
  We write `e` for it.
- `CMDividingLevelSufficientlySmall D m K₀` is
  `D.rationalInvolution.DividingLevelSufficientlySmall m K₀` for a level `K₀`
  of `(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`.
- `cmPrimeToProperty D m hm K₀` is `awayProperty e small K₀`, the property of
  the levels `K'` of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ` for which
  `e⁻¹ (K₀ × K')` is sufficiently small.
- `cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀ K'`: if
  `hK₀ : CMDividingLevelSufficientlySmall D m K₀`, every level `K'` satisfies
  `cmPrimeToProperty D m hm K₀`. It is
  `levelSufficientlySmall_transport_prod`.
- `cmPrimeToSchemeTower ... q m hm K₀` is
  `awayLevelTower e K₀ (cmGeometricSchemeTower ... q)`, the tower
  `K' ↦ cmGeometricSchemeTower ... q (e⁻¹ (K₀ × K'))` over the levels in
  `cmPrimeToProperty D m hm K₀`.
- `cmPrimeToSchemeTower_restrictedSelfArrow`: each `k ∈ K'` acts on the
  scheme at level `K'` by the identity. It is `awayLevelTower_selfArrow`
  applied to `cmGeometricSchemeTower_restrictedSelfArrow`.
- `cmPrimeToFullSchemeTower ... q m hm hK₀` is
  `extendTower (cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀) (cmPrimeToSchemeTower ... q m hm K₀)`,
  the same tower regarded as a tower over all levels of
  `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.

## Coefficients and cohomology

Assume the inputs `existence`, `geometry`, `hRigid` and `criterion`, and let
`R : Type` be a commutative ring.

- `cmPrimeToTowerEtale`: every arrow of the prime-to-`m` tower is étale,
  because its scheme map is the scheme map of the arrow
  `(awayFunctor e small K₀).map a` of the CM tower (`cmSmallLevelTowerEtale`).
- `cmPrimeToCoefficientDiagram ... R` is `CoefficientDiagram R` on the
  opposite of the prime-to-`m` tower, and `cmPrimeToTrivialCoefficients` is
  the published level-triviality property on it.
- `cmPrimeToCoefficients ... R coeff` is `awayCoefficients e K₀ coeff`, the
  coefficients `coeff` on the CM tower restricted to the levels
  `e⁻¹ (K₀ × K')`. `cmPrimeToCoefficients_trivial` states that the
  restriction of level-trivial coefficients is level-trivial.
- `cmPrimeToLevelCohomology ... R coeff' d` is the degree `d` cohomology
  presheaf `coeff'.cohomology d` on the prime-to-`m` levels.
- `cmPrimeToColimitCohomology ... R coeff' d` is
  `RestrictedLevelTowerCohomology.colimitCohomology coeff' d`, an object of
  `Action (ModuleCat R) (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`: the
  colimit over the levels `K'` in `cmPrimeToProperty D m hm K₀` of the degree
  `d` cohomology of the prime-to-`m` tower.
- `cmPrimeToSmoothCohomology ... R coeff' hcoeff' d` is
  `RestrictedLevelTowerCohomology.smoothColimitCohomology coeff' hcoeff' d`, a
  smooth representation of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`, for
  level-trivial `coeff'`.

## Comparison with the shrinking-level cohomology

Let `coeff` be coefficients on the CM tower.

- `cmPrimeToCohomologyComparison ... R coeff d` is
  `awayCohomologyComparison e K₀ coeff d`, a morphism of objects with an
  action of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ` from the prime-to-`m`
  colimit cohomology of `cmPrimeToCoefficients ... R coeff` to the
  shrinking-level cohomology `cmSmallLevelColimitCohomology ... R coeff d`, on
  which the prime-to-`m` group acts through `awayHom e`.
- `ι_cmPrimeToCohomologyComparison ... R coeff d K'`: on the classes of level
  `K'`, the comparison is the colimit leg of the shrinking-level cohomology at
  the level `(awayFunctor e small K₀).obj K'`, that is, `e⁻¹ (K₀ × K'.obj)`.
- `cmPrimeToCohomologyComparison_translate_of_mem ... R hcoeff d hk x`: if
  some prime-to-`m` level satisfies `cmPrimeToProperty D m hm K₀`, `coeff` is
  level-trivial and `k ∈ K₀`, then `factorHom e k` fixes the image of `x`
  under the comparison.
- `cmPrimeToCohomologyIso ... R hcof coeff d`: if
  `hcof : (awayOver e K₀).IsRestrictedCofinal (cmPrimeToProperty D m hm K₀) small`,
  that is, every sufficiently small level contains a sufficiently small level
  `e⁻¹ (K₀ × K')`, the comparison is an isomorphism of objects with an action
  of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`. `cmPrimeToCohomologyIso_hom`
  states that its forward morphism is `cmPrimeToCohomologyComparison`, by
  `rfl`.

## The full prime-to-`m` tower

Let `hK₀ : CMDividingLevelSufficientlySmall D m K₀`, and keep the inputs
`existence`, `geometry`, `hRigid`, `criterion` and the ring `R`.

- `cmPrimeToFullCoefficientDiagram ... R` is `CoefficientDiagram R` on the
  opposite of `cmPrimeToFullSchemeTower ... q m hm hK₀`, and
  `cmPrimeToFullTrivialCoefficients` is the published level-triviality
  property `LevelTowerCohomology.levelTrivialCoefficients` on it.
- `cmPrimeToFullCoefficients ... R coeff'` is `extendCoefficients` of
  coefficients `coeff'` on the prime-to-`m` tower, and
  `cmPrimeToFullCoefficients_trivial` states that the extension of
  level-trivial coefficients is level-trivial.
- `cmPrimeToFullColimitCohomology ... R coeff'' d` is
  `LevelTowerCohomology.colimitCohomology coeff'' d`, the colimit over all
  prime-to-`m` levels, with the action of
  `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`, and
  `cmPrimeToFullSmoothCohomology ... R coeff'' hcoeff'' d` is
  `LevelTowerCohomology.smoothColimitCohomology coeff'' hcoeff'' d` for
  level-trivial `coeff''`.
- `cmPrimeToColimitCohomologyExtendIso ... R coeff' d`: if some compact open
  level of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ` exists, the
  prime-to-`m` colimit cohomology of `coeff'` is isomorphic, as an object
  with an action of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`, to the
  colimit cohomology over all prime-to-`m` levels of
  `cmPrimeToFullCoefficients ... R coeff'`. It is
  `colimitCohomologyExtendIso`.
- `cmPrimeToSmoothCohomologyExtendIso ... R coeff' hcoeff' d` is the same
  isomorphism of smooth representations for level-trivial `coeff'`, given by
  `smoothColimitCohomologyExtendIso`.

## Proof outline

Every declaration specializes a declaration of
`RestrictedSplitLevelTowerCohomology` or `RestrictedLevelTowerExtension` to
`e = cmPrimeToSplit D m hm`, `P = small` and
`T = cmGeometricSchemeTower ... q`. The étaleness instances are installed
locally from `cmSmallLevelTowerEtale` and `cmPrimeToTowerEtale`. The
finite dimensionality instances needed by the splitting are derived from the
finite-dimensional `F`-algebra in `D` as in the published CM modules. The
conjugation stability and downward closure of `cmPrimeToProperty D m hm K₀`
come from the instances for preimage properties in
`Langlands.Shimura.RestrictedLevelReindex` and the published instances for
`LevelSufficientlySmall`.

## Provenance

This is an internal specialization of `RestrictedSplitLevelTowerCohomology`,
`RestrictedLevelTowerExtension` and `OppositePointsSplit` to the published
actual geometric CM tower and its shrinking-level cohomology. No comparison,
cofinality or isomorphism statement is supplied as input. Fixing the level
at the places dividing `m` is an implementation choice; Harris (1999),
Proposition 4.10 on printed p. 311, is motivation only.

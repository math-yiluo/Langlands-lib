# Harris's levels `K(N, m)` in the actual CM tower, with constant coefficients

Author: Worker 19.

This module puts the levels `K_p × K^p` of `HarrisPrimeAdelicLevels` into the
actual geometric CM scheme tower of the unitary data `D`. Harris's levels
`K(N, m) = K(N)_p × K(m)^p` are the special case `K_p = K(N)_p`. It also
defines the étale cohomology of a constant sheaf at such a level and in the
colimit over the prime-to-`p` factor. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Source and motivation

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Section 4, printed p. 309 (PDF p. 11). Harris fixes
`K(N, m) = K(N)_p × K(m)^p ⊂ GG(A_f)` with
`K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ`, and continues: "Let `𝓛` be a
free `𝒪/ℓ^m 𝒪`-module, and let `𝓛̃` denote the corresponding constant étale
sheaf on `S(GG, X_{n-1})_{K(N,m)}`." Proposition 4.4 then concerns
`H^{i+j}(S̄_{K(N, m)}, 𝓛̃)` with `S̄_{K(N, m)} = S(GG, X_{n-1})_{K(N, m)} ×_{𝒦,v} F̄`,
and says that the spectral sequences are `GG(A_f^p)`-equivariant as the
prime-to-`p` level varies.

The Library's CM tower is indexed by sufficiently small levels of
`GG(A_f)ᵐᵒᵖ` (`SmallCMLevel D`). Its prime-to-`m` version
(`cmPrimeToSchemeTower`) fixes a level `K₀` at the places dividing `m` and
varies the prime-to-`m` level. This module identifies the level `K^pᵐᵒᵖ` of
the prime-to-`p` tower with fixed level `K₀` attached to `K_p` with the level
`(K_p × K^p)ᵐᵒᵖ` of the full tower. That identification, and the use of a
constant sheaf on `Spec F` pulled back to the level, are internal to the
Library.

## Inputs

- From `Langlands.Shimura.Unitary.HarrisPrimeAdelicLevels`, submitted with
  this module: `CompactOpenLevel.op`, `AlgebraInvolution.primeAdelicLevel`,
  `primeDividingOpLevel`, `transport_finiteAdelicPointsOpSplit_symm_prod`,
  `PrimeToLevelSufficientlySmall`,
  `levelSufficientlySmall_transport_prod_of_primeTo`,
  `exists_primeToLevelSufficientlySmall_le`,
  `exists_primeToLevelSufficientlySmall` and
  `SecondKindInvolution.harrisPrimeAdelicLevel`.
- Published `HarrisDivisionLevels`: `SecondKindInvolution.harrisLevel`
  (Harris's `K(N)_p`, with congruence radius `r`; Harris's `C_v^{N,0}` is the
  radius `‖ϖ‖^N`, as explained there).
- Published `HarrisTaylorCMPrimeToCohomology`: `cmPrimeToSplit`,
  `cmPrimeToProperty` (the prime-to-`m` levels `K'` for which `e⁻¹ (K₀ × K')`
  is sufficiently small) and `cmPrimeToSchemeTower`. Published
  `RestrictedSplitLevelTowerCohomology`: `awayProperty_iff` and
  `RestrictedSplitLevelTowerCohomology.awayFunctor` (a level `K'` goes to
  `e⁻¹ (K₀ × K')`).
- Published `HarrisTaylorCMSmallLevelGaloisCoefficients`:
  `cmGeometricSchemeTower` (the levels `X_U ×_F Spec F̄`) and
  `cmSmallLevelArithmeticGeometricStructure` (their projections to `Spec F`).
  Published `HarrisTaylorCMPrimeToGaloisCohomology`:
  `cmPrimeToArithmeticStructure`, `cmPrimeToArithmeticStructure_app` and
  `cmPrimeToGaloisCohomologyFunctor`. Published
  `HarrisTaylorCMLevelGaloisCohomology`: `cmLevelGaloisCohomologyFunctor`.
- Published `Langlands.Geometry.EtaleConstantCohomology`:
  `EtaleCohomologyAction.constant` (the constant sheaf with value a module).
  Published `Langlands.Geometry.EtaleInverseImageConstant`:
  `EtaleInverseImage.inverseImageConstantIso`.
- The fields `D.finite` (`A` is finite-dimensional over `F`, hence over `ℚ`)
  and `D.simple` (`A` is simple, hence nontrivial) of the published
  `CentralSimpleUnitaryData`.

The cohomology declarations take the same CM data and named propositions
`C`, `preservation`, …, `htor`, `q : CMRepresentabilityStatement …` as the
published `HarrisTaylorCMSmallLevelGaloisCoefficients`. The colimit
declarations also take `existence`, `geometry`, `hRigid` and `criterion`, as
`cmPrimeToGaloisCohomologyFunctor` does. These are hypotheses, not proved
here.

## Declarations

### Levels (section `Levels`)

For `m ≠ 0`:

- `CMPrimeToLevelSufficientlySmall D m K'`: the condition
  `PrimeToLevelSufficientlySmall` of `HarrisPrimeAdelicLevels` for a level
  `K'` of `GG(A_f^m)ᵐᵒᵖ` (no nontrivial element of finite order in its
  component at some place not dividing `m`).
- `cmPrimeToProperty_of_primeToSufficientlySmall`: such `K'` lie in
  `cmPrimeToProperty D m hm K₀` for every `K₀`.
- `exists_cmPrimeToLevelSufficientlySmall_le`: every level of `GG(A_f^m)`
  contains a level `L` with `CMPrimeToLevelSufficientlySmall D m Lᵐᵒᵖ`.
  `exists_cmPrimeToLevelSufficientlySmall`: such a level exists.

For a prime `p`, the place `v` of `ℚ` above it and a level `K_p` of
`GG(ℚ_v)`:

- `cmPrimeAdelicLevel D p hp v K_p K^p` is `K_p × K^p`, and
  `cmPrimeDividingLevel D p hp v K_p` is the fixed level `K₀` attached to `K_p`.
- `transport_cmPrimeToSplit_symm_prod_cmPrimeDividingLevel`:
  `e⁻¹ (K₀ × K^pᵐᵒᵖ) = (K_p × K^p)ᵐᵒᵖ` for the splitting `cmPrimeToSplit`.
- `cmPrimeToProperty_op_iff`: `K^pᵐᵒᵖ` lies in the prime-to-`p` property for
  `K₀` exactly when `(K_p × K^p)ᵐᵒᵖ` is sufficiently small.
- `levelSufficientlySmall_cmPrimeAdelicLevel_op`: if
  `CMPrimeToLevelSufficientlySmall D p K^pᵐᵒᵖ`, then `(K_p × K^p)ᵐᵒᵖ` is
  sufficiently small, whatever `K_p` is.
- `cmPrimeAdelicSmallLevel`: `(K_p × K^p)ᵐᵒᵖ` as an object of
  `SmallCMLevel D`. `cmPrimeToLevel`: `K^pᵐᵒᵖ` as an object of the index
  category of the prime-to-`p` tower with fixed level `K₀`.
- `awayFunctor_obj_cmPrimeToLevel`: the published `awayFunctor` sends the
  second to the first.

### Harris's levels (section `Harris`)

With an imaginary quadratic field `L` and `[Algebra L F]`, a place `𝔭` of `L`
above `v` with `ℚ_v ≅ L_𝔭`, and the division and congruence data `hdiv`, `w₀`,
`r` of the published `harrisLevel`:

- `cmHarrisLevel` is Harris's `K(N)_p` for `D`
  (`D.toSecondKindInvolution.harrisLevel (algebraMap L F) …`).
- `cmHarrisAdelicLevel … K^p` is `K(N, m) = K(N)_p × K^p`;
  `cmHarrisAdelicLevel_eq` says it is `SecondKindInvolution.harrisPrimeAdelicLevel`
  of `HarrisPrimeAdelicLevels`.
- `cmHarrisDividingLevel` is the fixed level `K₀` attached to `K(N)_p`.
- `cmHarrisSmallLevel … K^p hK^p` is `K(N, m)ᵐᵒᵖ` as an object of
  `SmallCMLevel D`, for `K^p` with `CMPrimeToLevelSufficientlySmall D p K^pᵐᵒᵖ`.

### Schemes and constant coefficients (section `Cohomology`)

Write `X_U` for the actual geometric CM scheme at `U` (an object of
`cmGeometricSchemeTower`, the base change of the represented CM scheme to
`Spec F̄`) and `p_U : X_U ⟶ Spec F` for its projection. Let `R` be a
commutative ring and `𝓛` an `R`-module.

- `cmPrimeToSchemeTower_obj_cmPrimeToLevel`: the prime-to-`p` tower at the
  level `K^pᵐᵒᵖ` is `X_U` for `U = (K_p × K^p)ᵐᵒᵖ`.
- `cmPrimeToArithmeticStructure_app_cmPrimeToLevel`: under this equality the
  projection of the prime-to-`p` tower to `Spec F` is `p_U`.
- `constantInverseImageIso f 𝓛`: for every scheme morphism `f` to `Spec F`,
  the inverse image of the constant sheaf `𝓛` is the constant sheaf `𝓛`
  (the published `inverseImageConstantIso`, evaluated at `𝓛`).
- `cmPrimeAdelicConstantCohomology … K^p hK^p 𝓛 d` is
  `H^d(X_U, p_U^* 𝓛)` for `U = (K_p × K^p)ᵐᵒᵖ`, with the action of
  `Gal(F̄/F)`: the published `cmLevelGaloisCohomologyFunctor` at `U` applied to
  the constant sheaf `𝓛` on `Spec F`. `cmPrimeAdelicConstantCohomology_V`
  states that its underlying module is this cohomology (by definition).
  `cmPrimeAdelicConstantCohomologyIso` identifies it with `H^d(X_U, 𝓛)` for
  the constant sheaf `𝓛` on `X_U`, through `constantInverseImageIso`.
- `cmPrimeAdelicConstantGaloisCohomology … 𝓛 d` is the published
  `cmPrimeToGaloisCohomologyFunctor` with fixed level
  `K₀ = cmPrimeDividingLevel K_p`, applied to the constant sheaf `𝓛` on
  `Spec F`. It is the colimit over `K^p` of `H^d(X_{(K_p × K^p)ᵐᵒᵖ}, p^* 𝓛)`, as
  a smooth representation of `GG(A_f^p)ᵐᵒᵖ` with the commuting action of
  `Gal(F̄/F)`.
- For Harris's `K(N)_p`: `cmHarrisGeometricScheme` is `X_U` for
  `U = K(N, m)ᵐᵒᵖ`; `cmHarrisConstantCohomology` and
  `cmHarrisConstantGaloisCohomology` are the two cohomology constructions
  above with `K_p = K(N)_p`.

## Scope and limitations

- `X_U` is the base change to `F̄ = AlgebraicClosure F` of the CM moduli
  scheme represented through the hypothesis `q`. It is the CM-tower
  counterpart of Harris's `S̄_{K(N, m)}`. No comparison with Harris's
  canonical model `S(GG, X_{n-1})` or with his base change `×_{𝒦,v} F̄` is
  made.
- Harris's `K(m)^p`, defined through an identification
  `GG(A_f^p) ≅ GJ(A_f^p)`, is not constructed; any level `K^p` that is
  sufficiently small at a place not dividing `p` is used instead. Such levels
  exist inside every level (`exists_cmPrimeToLevelSufficientlySmall_le`).
- Harris takes `𝓛` free over `𝒪/ℓ^m 𝒪`. Here `R` is any commutative ring and
  `𝓛` any `R`-module; Harris's case is `R = 𝒪/ℓ^m 𝒪`.
- The module does not compare the fixed-level cohomology with the fixed
  vectors of the colimit. It does not formalize Proposition 4.4, its spectral
  sequence or the rigid-analytic uniformization (4.3).

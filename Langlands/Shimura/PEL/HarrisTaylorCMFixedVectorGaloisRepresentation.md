# Fixed vectors of the cohomology of the actual CM tower as Galois representations

This internal construction applies the generic module
`Langlands.Shimura.FixedVectorGaloisRepresentation` to the published Galois
actions on the cohomology of the actual geometric CM tower. It assumes the
Library statement `HarrisCMLevelGaloisSmoothStatement`, which says that
`Gal(F̄/F)` acts smoothly on the shrinking-level cohomology. Under this
statement `Gal(F̄/F)` acts smoothly on the `H`-fixed vectors of the
cohomology, and of each of its isotypic parts, for every subgroup `H` of
`GG(A_f)ᵐᵒᵖ`. Over a topological field `R`, finite-dimensional fixed vectors
are then continuous Galois representations of `F`, objects of
`Langlands.GaloisRepresentation.Objects F R`. At a finite place `w` where the
cohomology is unramified, the Euler polynomial is the reversed
characteristic polynomial of the geometric Frobenius endomorphism. For the
prime-to-`m` cohomology the smoothness of the Galois action is an explicit
hypothesis. There the same holds for the `K'`-fixed vectors of the
cohomology and of its isotypic parts, and the Frobenius endomorphism is the
Hecke-linear Frobenius endomorphism of the Hecke module of `K'`-fixed
vectors, with scalars restricted to `R`. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, part (i), concerns the representation
of `Gal(F̄/F)` on the `JL(π_f)`-isotypic component `H^{n-1}(S_K(N), W)[π]` of
the cohomology at the level `K(N)`, which Harris introduces on printed
p. 312. Part (ii) characterizes the resulting Galois representation by its
Frobenius characteristic polynomials at almost all unramified places,
through formula (5.6). Here the fixed vectors of the isotypic parts of the
colimit cohomology under a level stand in for these isotypic components.
This module makes them continuous Galois representations with Euler
polynomials, and identifies the Frobenius endomorphism with a Hecke-linear
map in the prime-to-`m` case.

The coefficients are module sheaves on `Spec F`, pulled back to every level.
The module does not construct Harris's coefficient systems `W`, the
representation `JL(π_f)`, the twist by `V(π)`, the contragredient, the
semisimplification, or compactly supported or adic cohomology. It does not
identify the fixed vectors of the colimit with the cohomology at a finite
level; that comparison is the separate Library statement
`HarrisCMColimitInvariantsStatement`, which this module does not use. It
does not prove `HarrisCMLevelGaloisSmoothStatement`, the smoothness of the
Galois action on the prime-to-`m` cohomology, the finite dimension of any
space of fixed vectors, or unramifiedness at any place. These are
hypotheses of the results. `ξ` is an arbitrary representation and `H` an
arbitrary subgroup. No statement of Harris is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, `q : CMRepresentabilityStatement ...` and the inputs
`existence`, `geometry`, `hRigid` and `criterion` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. Below `...`
abbreviates them. Write `base` for `Spec (CommRingCat.of F)`. Let
`U : Type uU` be an `R`-module, `w : Global.FinitePlace F` and `j` a closure
embedding at `w`.

- The published `cmSmallLevelGaloisCohomologyFunctor ... R d`, written `H d`,
  and, for `m : ℕ`, `hm : m ≠ 0` and a level `K₀` of
  `(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`, the published
  `cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`, written `H' d`.
  The published `cmPrimeToGaloisHeckeModuleFunctor` is, by `rfl`, `H' d`
  followed by `LevelHecke.heckeModuleActionFunctor` for a level `K'` of
  `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.
- The published
  `Langlands.Cohomology.HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement ... R`
  (Worker 3).
- The published `cmPrimeToHeckeFrobenius` of
  `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology` (candidate
  `06482d9c-709f-449e-bd42-538102e24d51`, accepted and awaiting
  publication): `cmSmallLevelIsotypicCohomologyFunctor` and
  `cmPrimeToIsotypicCohomologyFunctor`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMIsotypicDecompositionCohomology`
  (candidate `65e8e325-c197-47a1-ab0b-91df2848f8b4`, accepted and awaiting
  publication): `cmPrimeToIsotypicHeckeFrobenius`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMMultiplicityGaloisRepresentation`
  (candidate `918ad65e-471f-4f3e-a388-db523e305d3a`, accepted and awaiting
  publication):
  `cmSmallLevelGaloisCohomology_isSmooth`,
  `cmSmallLevelIsotypicCohomology_isSmooth` and
  `cmPrimeToIsotypicCohomology_isSmooth`.
- From `Langlands.Shimura.FixedVectorGaloisRepresentation`, submitted
  together with this module: `isSmooth_fixedVectors`, `heckeFrobenius`,
  `fixedVectorsObjects` and its Euler-polynomial results, and
  `isUnramifiedAlong_fixedVectors_isotypic`. It uses
  `LevelHecke.fixedVectorsActionFunctor`.
- `FrobeniusPolynomial.frobeniusEulerPolynomial` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication), and `IsUnramifiedAt`, `IsUnramifiedAlong` and
  `geometricFrobenius` of the published
  `Langlands.Shimura.DecompositionGroupAction`.

## Smoothness and Frobenius endomorphisms

Let `R : Type` be a commutative ring, `hsmooth` a proof of
`HarrisCMLevelGaloisSmoothStatement ... R`, and `H` a subgroup of
`D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`.

- `cmSmallLevelFixedVectors_isSmooth ... R H hsmooth d M`: the Galois action
  on the `H`-fixed vectors of `(H d).obj M`, that is, the representation
  `((Rep.ActionToRep R _).obj ((fixedVectorsActionFunctor R _ H).obj ((H d).obj M))).ρ`,
  is smooth.
- `cmSmallLevelIsotypicFixedVectors_isSmooth ... R H ξ hsmooth d M`: the
  same for the `H`-fixed vectors of
  `(cmSmallLevelIsotypicCohomologyFunctor ... R ξ d).obj M`, for
  `ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U`.
- `cmPrimeToFixedVectors_isSmooth ... d M hM` and
  `cmPrimeToIsotypicFixedVectors_isSmooth ... d M hM`: the analogues for the
  `K'`-fixed vectors of `(H' d).obj M` and of
  `(cmPrimeToIsotypicCohomologyFunctor ... R m hm K₀ ξ d).obj M`, for
  `ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U`, given a
  proof `hM` that `galoisRepresentation ((H' d).obj M)` is smooth.
- `cmPrimeToHeckeFrobenius_hom_eq` and
  `cmPrimeToIsotypicHeckeFrobenius_hom_eq`: the underlying Hecke-linear maps
  of `cmPrimeToHeckeFrobenius ... w K' d M j` and
  `cmPrimeToIsotypicHeckeFrobenius ... ξ w K' d M j` are
  `heckeFrobenius K'.subgroup X w j` for `X = (H' d).obj M` and for the
  `ξ`-isotypic part, by `rfl`.

## Continuous Galois representations

Let now `R : Type` be a field with a topology.

- `cmSmallLevelFixedVectorGaloisRepresentation ... R H hsmooth d M`: if the
  `H`-fixed vectors of `(H d).obj M` are finite-dimensional over `R`, this
  is `fixedVectorsObjects` of `H` and `(H d).obj M`, an object of
  `Objects F R`. `_rank` gives its rank, the dimension of the fixed vectors.
  `_hasEulerPolynomialAt_iff` says that it has Euler polynomial `P` at `w` if
  and only if the fixed vectors are unramified at `w` with Frobenius Euler
  polynomial `P`. `_hasEulerPolynomialAt_of_isUnramifiedAlong hu` says that,
  if the `H`-fixed vectors of `(H d).obj M` are `IsUnramifiedAlong` at `w`
  and `j`, the Euler polynomial at `w` is the reverse of the characteristic
  polynomial of the geometric Frobenius endomorphism of the fixed vectors
  along `j`.
- `cmSmallLevelIsotypicFixedVectorGaloisRepresentation ... R H ξ hsmooth d M`,
  with `_rank`, `_hasEulerPolynomialAt_iff` and
  `_hasEulerPolynomialAt_of_isUnramifiedAlong`: the same for the `H`-fixed
  vectors of the `ξ`-isotypic part. The unramifiedness hypothesis is still on
  the `H`-fixed vectors of `(H d).obj M`.
- `cmPrimeToFixedVectorGaloisRepresentation ... R m hm K₀ K' d M hM`, with
  `_rank` and `_hasEulerPolynomialAt_iff`: the analogue for the `K'`-fixed
  vectors of `(H' d).obj M`. By `_hasEulerPolynomialAt_heckeFrobenius hu`,
  if these fixed vectors are `IsUnramifiedAlong` at `w` and `j`, the Euler
  polynomial at `w` is
  `((heckeFrobenius K'.subgroup ((H' d).obj M) w j).restrictScalars R).charpoly.reverse`,
  the reversed characteristic polynomial over `R` of the underlying map of
  `cmPrimeToHeckeFrobenius`.
- `cmPrimeToIsotypicFixedVectorGaloisRepresentation ... R m hm K₀ K' ξ d M hM`,
  with `_rank`, `_hasEulerPolynomialAt_iff` and
  `_hasEulerPolynomialAt_heckeFrobenius`: the same for the `K'`-fixed
  vectors of the `ξ`-isotypic part, with the underlying map of
  `cmPrimeToIsotypicHeckeFrobenius`. The unramifiedness hypothesis is on
  the `K'`-fixed vectors of `(H' d).obj M`.

The unramifiedness hypotheses concern fixed vectors under a level, not the
colimit cohomology itself, which is not expected to be unramified at the
places where the levels shrink.

## Proof outline

All results apply the corresponding results of
`Langlands.Shimura.FixedVectorGaloisRepresentation` to `(H d).obj M`,
`(H' d).obj M` or their isotypic parts. The smoothness inputs are the
smoothness results of `HarrisTaylorCMMultiplicityGaloisRepresentation`, and
unramifiedness passes from the fixed vectors of the cohomology to the fixed
vectors of its isotypic parts by `isUnramifiedAlong_fixedVectors_isotypic`. The ranks and the
identifications of the Hecke-linear Frobenius endomorphisms hold by `rfl`.

## Provenance

This is an internal specialization of
`Langlands.Shimura.FixedVectorGaloisRepresentation` to the Galois actions on
the cohomology of the actual geometric CM tower. The smoothness input is the
published Library statement `HarrisCMLevelGaloisSmoothStatement`, used as a
hypothesis. No action, space of fixed vectors or Galois representation is
supplied as input. Harris (1999), the definition of `H^{n-1}(S_K(N), W)[π]`
on printed p. 312, and Theorem 5.7 and formula (5.6) on printed p. 313, are
motivation only.

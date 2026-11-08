# Hecke multiplicity spaces of the cohomology of the actual CM tower as Galois representations

This internal construction applies the generic module
`Langlands.Shimura.HeckeMultiplicityGaloisRepresentation` to the published
Galois actions on the cohomology of the actual geometric CM tower. For a
subgroup `H` of `GG(A_f)ᵐᵒᵖ` and a module `T` over the Hecke algebra of `H`,
the Hecke multiplicity space `Hom_{H(H)}(T, H^d(M)^H)` of the shrinking-level
cohomology carries the action of `Gal(F̄/F)` by composition. The module
assumes the Library statement `HarrisCMLevelGaloisSmoothStatement`, that
`Gal(F̄/F)` acts smoothly on the shrinking-level cohomology. If moreover `T`
is finitely generated, the action on the multiplicity space is smooth. Over
a topological field, a finite-dimensional multiplicity space is then a
continuous Galois representation of `F`. At a finite place where the
`H`-fixed vectors are unramified, its Euler polynomial is the reversed
characteristic polynomial of its geometric Frobenius endomorphism. The same
holds for the prime-to-`m` cohomology and its levels `K'`, with the
smoothness of its Galois action as an explicit hypothesis. There the
Frobenius endomorphism is composition with the Hecke-linear Frobenius
endomorphism `cmPrimeToHeckeFrobenius`. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, printed p. 312, writes `H^{n-1}(S_K(N), W)[π]` for the
`JL(π_f)`-isotypic component of the cohomology at the level `K(N)`. Theorem
5.7 on printed p. 313 describes the Galois representation on it, and part
(ii) characterizes it by Frobenius characteristic polynomials at almost all
unramified places, through formula (5.6). This module gives the Hecke-module
form of the corresponding spaces of intertwining maps for the published CM
cohomology. The vectors fixed by a level stand in for the cohomology at that
level, and `T` stands in for the fixed vectors of `JL(π_f)`.

The coefficients are module sheaves on `Spec F`, pulled back to every level.
The module does not construct Harris's coefficient systems `W`, the
representation `JL(π_f)` or its fixed vectors, or compactly supported or adic
cohomology. It does not identify the fixed vectors of the colimit with the
cohomology at a finite level; that is the separate Library statement
`HarrisCMColimitInvariantsStatement`, which this module does not use. It does
not prove `HarrisCMLevelGaloisSmoothStatement`, the smoothness of the Galois
action on the prime-to-`m` cohomology, the finite dimension of any
multiplicity space, or unramifiedness at any place. These are hypotheses of
the results. `T` is an arbitrary module over the Hecke algebra, finitely
generated where stated, and `H` an arbitrary subgroup. No statement of
Harris is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, `q : CMRepresentabilityStatement ...` and the inputs
`existence`, `geometry`, `hRigid` and `criterion` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. Below `...`
abbreviates them. Write `base` for `Spec (CommRingCat.of F)`. Let
`w : Global.FinitePlace F` and let `j` be a closure embedding at `w`.

- The published `cmSmallLevelGaloisCohomologyFunctor ... R d`, written `H d`,
  and, for `m : ℕ`, `hm : m ≠ 0` and a level `K₀` of
  `(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`, the published
  `cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`, written `H' d`.
- The published
  `Langlands.Cohomology.HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement ... R`
  (Worker 3), and the published `cmPrimeToHeckeFrobenius` of
  `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMMultiplicityGaloisRepresentation`
  (candidate `918ad65e-471f-4f3e-a388-db523e305d3a`, accepted and awaiting
  publication): `cmSmallLevelGaloisCohomology_isSmooth`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMFixedVectorGaloisRepresentation`
  and `Langlands.Shimura.FixedVectorGaloisRepresentation` (candidate
  `7a622629-80be-4029-b7ca-0e6bc08e7a87`, accepted and awaiting
  publication): `heckeFrobenius` and `cmPrimeToHeckeFrobenius_hom_eq`, which
  identifies the underlying map of `cmPrimeToHeckeFrobenius ... d M j` with
  `heckeFrobenius K'.subgroup ((H' d).obj M) w j`.
- From `Langlands.Shimura.HeckeMultiplicityGaloisRepresentation`, submitted
  together with this module: `heckeMultiplicityActionFunctor`,
  `heckeMultiplicityRepresentation`,
  `isSmooth_heckeMultiplicityRepresentation`, `heckeMultiplicityObjects` and
  its Euler-polynomial results.
- `LevelHecke.LevelHeckeAlgebra` and `LevelHecke.fixedVectorsActionFunctor`
  (published), `FrobeniusPolynomial.frobeniusEulerPolynomial` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication), and `IsUnramifiedAt`, `IsUnramifiedAlong` and
  `geometricFrobenius` of the published
  `Langlands.Shimura.DecompositionGroupAction`.

## Smoothness and Frobenius endomorphisms

Let `R : Type` be a commutative ring and `T : Type uT` a module over the
relevant Hecke algebra.

- `cmSmallLevelHeckeMultiplicity_isSmooth ... R H T hsmooth d M`: for a
  subgroup `H` of `D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`, if `T` is
  finitely generated over `LevelHeckeAlgebra R H` and `hsmooth` proves
  `HarrisCMLevelGaloisSmoothStatement ... R`, then the representation
  `heckeMultiplicityRepresentation H T _ ((H d).obj M)` of
  `Field.absoluteGaloisGroup F` is smooth.
- `cmPrimeToHeckeMultiplicity_isSmooth ... R m hm K₀ K' T d M hM`: for a
  level `K'` of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`, if `T` is
  finitely generated over `LevelHeckeAlgebra R K'.subgroup` and `hM` proves
  that `galoisRepresentation ((H' d).obj M)` is smooth, the same holds for
  `K'.subgroup` and `(H' d).obj M`.
- `cmPrimeToHeckeMultiplicity_geometricFrobenius_apply ... w d M j φ`: the
  geometric Frobenius endomorphism at `w` along `j` of the multiplicity
  action sends `φ` to `(heckeFrobenius K'.subgroup ((H' d).obj M) w j).comp φ`,
  composition with the underlying map of `cmPrimeToHeckeFrobenius`.

## Continuous Galois representations

Let now `R : Type` be a field with a topology, and let `T` be finitely
generated over the relevant Hecke algebra.

- `cmSmallLevelHeckeMultiplicityGaloisRepresentation ... R H T hsmooth d M`:
  if the multiplicity space
  `T →ₗ[LevelHeckeAlgebra R H] fixedVectors ((H d).obj M).V.representation H`
  is finite-dimensional over `R`, this is `heckeMultiplicityObjects` of `H`,
  `T` and `(H d).obj M`, an object of `Objects F R`. `_rank` gives its rank,
  the dimension of the multiplicity space. `_hasEulerPolynomialAt_iff` says
  that it has Euler polynomial `P` at `w` if and only if the multiplicity
  action is unramified at `w` with Frobenius Euler polynomial `P`.
  `_hasEulerPolynomialAt_of_isUnramifiedAlong hu` says that, if the
  `H`-fixed vectors of `(H d).obj M` are `IsUnramifiedAlong` at `w` and `j`,
  the Euler polynomial at `w` is the reverse of the characteristic polynomial
  of the geometric Frobenius endomorphism of the multiplicity action along
  `j`.
- `cmPrimeToHeckeMultiplicityGaloisRepresentation ... R m hm K₀ K' T d M hM`,
  with `_rank`, `_hasEulerPolynomialAt_iff` and
  `_hasEulerPolynomialAt_of_isUnramifiedAlong`: the analogue for `K'` and
  `(H' d).obj M`. The unramifiedness hypothesis is on the `K'`-fixed vectors
  of `(H' d).obj M`. The Frobenius endomorphism in the Euler polynomial is
  composition with the underlying map of `cmPrimeToHeckeFrobenius`, by
  `cmPrimeToHeckeMultiplicity_geometricFrobenius_apply`.

The unramifiedness hypotheses concern fixed vectors under a level, not the
colimit cohomology itself, which is not expected to be unramified at the
places where the levels shrink.

## Proof outline

All results apply the corresponding results of
`Langlands.Shimura.HeckeMultiplicityGaloisRepresentation` to `(H d).obj M`
or `(H' d).obj M`. The shrinking-level smoothness input is
`cmSmallLevelGaloisCohomology_isSmooth`. The ranks and the description of the
Frobenius endomorphism hold by `rfl`.

## Provenance

This is an internal specialization of
`Langlands.Shimura.HeckeMultiplicityGaloisRepresentation` to the Galois
actions on the cohomology of the actual geometric CM tower. The smoothness
input is the published Library statement
`HarrisCMLevelGaloisSmoothStatement`, used as a hypothesis. No action,
multiplicity space or Galois representation is supplied as input. Harris
(1999), printed p. 312, and Theorem 5.7 and formula (5.6) on printed p. 313,
are motivation only.

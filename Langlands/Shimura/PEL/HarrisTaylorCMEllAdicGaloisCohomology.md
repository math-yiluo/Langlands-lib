# The coefficient-prime specialization of the torsion limit of Harris's CM coefficient system

This internal construction specializes the `m`-power torsion limit of
`Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology` and the `l`-adic
representations of `Langlands.Shimura.PEL.HarrisTaylorCMLambdaAdicRepresentation`
to Harris's coefficient prime. For a rational finite place `p`, the
coefficient prime `ℓ` is the residue characteristic of `p`. The module
proves that `ℓ` is a prime number that lies in `p` and in every place of the
coefficient field `K` above `p`. Taking `m = ℓ`, the stages of the published
coefficient construction have coefficients modulo the powers `ℓ^r`, as in
Harris. The module gives the `ℓ`-power torsion limit of the cohomology of a
geometric CM level with Harris's coefficient system, the continuity of its
Galois action, and its `l`-adic Galois representations with their Euler
polynomials. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, works with coefficients modulo powers of the coefficient prime `ℓ`
(printed p. 308) and forms from them the lisse `ℓ`-adic sheaf (printed
p. 311). §5 on printed p. 313 considers the resulting `λ`-adic
representations. The review of the torsion-limit construction (candidate
`99335a4c-07bc-4e82-b20c-e6ac07f1c0f2`, review `71cdcf38`) left the
specialization of the scalar `m` relative to `p` as a future obligation.
This module supplies that specialization: `m` becomes the residue
characteristic of `p`. The module proves that `ℓ` lies in every place `l`
of `K` above `p`. A scalar outside some such `l` would have vanishing
reductions at the `l`-component; the coefficient prime has no such place.
The module does not prove the corresponding statement about the completed
valuation rings.

The `ℓ`-power torsion limit is the inverse limit over `r` of the cohomology
with coefficients modulo `ℓ^r`. The module does not prove any comparison with
other definitions of `ℓ`-adic cohomology, any finiteness or freeness of the
limit, or the continuity of its matrix coefficients. Smoothness,
unramifiedness, freeness and continuity remain hypotheses as in the
specialized modules. No `JL(π_f)`-isotypic component, twist by `V(π)` or
semisimplification is constructed, and no statement of Harris is
formalized.

## Inputs

- From the published `Langlands.GaloisRepresentation` (`CompatibleFamily`):
  `residueCharacteristic v = ringChar (𝓞 K ⧸ v.asIdeal)`.
- From the published `Langlands.Global.AdelicFunctoriality`:
  `FinitePlacesAbove K p`, the places `l` of `K` whose ideal lies over
  `p.asIdeal`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology` (candidate
  `d74b579d-a959-4356-9ab5-6ce21cbcbfbc`, accepted and awaiting
  publication): `cmHarrisAdicCohomology`, `CMHarrisAdicSpace`,
  `continuous_cmHarrisAdicAction` and `cmHarrisAdicFrobeniusEulerPolynomial`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMLambdaAdicRepresentation`
  (candidate `7140e878-3de0-439e-bfaf-6f52ad786d28`, accepted and awaiting
  publication): `harrisCoefficientComponentMap`,
  `CMHarrisAdicIsLatticeContinuous`, `cmHarrisLambdaAdicRepresentation` and
  `cmHarrisLambdaAdicRepresentation_hasEulerPolynomialAt`.
- Worker 3's published `HarrisCMGaloisCohomologySmoothStatement` and Worker
  57's published `cmHarrisGeometricGaloisCohomologyAction`.
- From Mathlib: `ringChar.Nat.cast_ringChar`,
  `CharP.ringChar_ne_zero_of_finite`, `CharP.char_is_prime_or_zero`,
  `Ideal.finiteQuotientOfFreeOfNeBot`, `Ideal.Quotient.eq_zero_iff_mem` and
  `Ideal.mem_of_liesOver`.

The CM binders are those of `HarrisTaylorCMAdicGaloisCohomology` without
`m` and `hm`, which are replaced by `harrisCoefficientPrime p` and
`harrisCoefficientPrime_ne_zero p`.

## The coefficient prime

Let `p : Global.FinitePlace ℚ`.

- `harrisCoefficientPrime p : ℕ` is `residueCharacteristic p`.
- `harrisCoefficientPrime_mem p`: its image in `𝓞 ℚ` lies in `p.asIdeal`.
- `harrisCoefficientPrime_ne_zero p` and `harrisCoefficientPrime_prime p`:
  it is nonzero and prime.
- `harrisCoefficientPrime_mem_above p l`: for a number field `K` and
  `l : FinitePlacesAbove K p`, its image in `𝓞 K` lies in `l.1.asIdeal`.

## The ℓ-power torsion limit and its representations

- `cmHarrisEllAdicCohomology ... degree` is `cmHarrisAdicCohomology` with
  `m = harrisCoefficientPrime p`.
- `continuous_cmHarrisEllAdicAction ... hsmooth degree`: under
  `HarrisCMGaloisCohomologySmoothStatement` for `m = ℓ`, the Galois action on
  the limit with its inverse limit topology is jointly continuous.
- `cmHarrisEllAdicRepresentation ... l degree hcont : LambdaAdic F K l.1`:
  for the limit finite free and `hcont` a proof of
  `CMHarrisAdicIsLatticeContinuous` for `m = ℓ`, the `l`-adic representation
  `cmHarrisLambdaAdicRepresentation` for `m = ℓ`.
- `cmHarrisEllAdicRepresentation_hasEulerPolynomialAt ... hcont w hu`: if
  every `ℓ`-power stage is unramified at `w`, the representation has as Euler
  polynomial at `w` the image under `harrisCoefficientComponentMap K p l` of
  the Frobenius Euler polynomial of the limit.

## Proof outline

The residue characteristic of `p` is the characteristic of the finite
quotient `𝓞 ℚ ⧸ p.asIdeal`, which is finite because `p.asIdeal` is a
nonzero ideal of a ring that is free of finite rank over `ℤ`. A finite ring
has nonzero characteristic, and a domain of nonzero characteristic has prime
characteristic. The characteristic maps to zero in the quotient, so it lies
in `p.asIdeal`. The ideal `l.1.asIdeal` lies over `p.asIdeal`, so the image
of the characteristic lies in it. The remaining declarations instantiate the
specialized modules at `m = ℓ`.

## Provenance

This is an internal specialization of `HarrisTaylorCMAdicGaloisCohomology`
and `HarrisTaylorCMLambdaAdicRepresentation`, with elementary facts about
residue characteristics. No action, limit, representation or polynomial is
supplied as input. Harris (1999), printed pp. 308 and 311, and §5 on printed
p. 313, are motivation only.

# l-adic Galois representations from the torsion limit of Harris's CM coefficient system

This internal construction applies
`Langlands.Shimura.LatticeGaloisRepresentation` to the `m`-power torsion
limit `cmHarrisAdicCohomology` of the cohomology of a geometric CM level with
Harris's coefficient system. The coefficient ring of Harris's torsion coefficient
systems is `HarrisCoefficientIntegers K p`. It is the product, over the
places `l` of the coefficient field `K` above the rational place `p`, of the
valuation rings `O_{K,l}`. For each such `l`, extending scalars of the
torsion limit along the `l`-component `O → O_{K,l} → K_l` gives a
Galois action on a finite-dimensional `K_l`-vector space. Suppose the
torsion limit is finite free and its matrix coefficients are
continuous with values in `K_l`. Then this is an `l`-adic Galois
representation of `F` in the sense of
`Langlands.GaloisRepresentation.LambdaAdic`. At a finite place `w` where
every torsion stage is unramified, its Euler polynomial is the image in
`K_l[X]` of the Frobenius Euler polynomial of the torsion limit. All
declarations are in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5 on printed p. 313, considers `λ`-adic representations of
`Gal(F̄/F)`. Theorem 5.7 concerns those on the cohomology
`H^{n-1}(S_K(N), W)` of the Shimura variety with Harris's coefficient
systems, and formula (5.6) gives their local factors. This module
produces, from the `m`-power torsion limit of Worker 57's version of this
cohomology at a fixed level, objects of the published `l`-adic
representations `LambdaAdic`, the objects that
`Langlands.GaloisRepresentation.CompatibleFamily` assembles into collections
over the places `l`. It also identifies their Euler polynomials.

The scalar `m` of the coefficient construction is arbitrary apart from
`m ≠ 0`; no relation between `m` and `p` is assumed. When `m` is a unit at
`l`, for instance when `p` does not divide `m`, every torsion stage has zero
`l`-component, and so does the torsion limit. The torsion limit is not
identified with Harris's `λ`-adic cohomology for a coefficient prime, and
neither are the representations constructed here.

Finite freeness of the torsion limit, continuity of its matrix
coefficients (`CMHarrisAdicIsLatticeContinuous`) and unramifiedness of the
torsion stages are hypotheses; none is proved. In particular, continuity is
not derived from the smoothness statement used in
`HarrisTaylorCMAdicGaloisCohomology`. That derivation would need a comparison
of the inverse-limit topology with the `l`-adic topology, which is not
available. The module does not construct the `JL(π_f)`-isotypic component,
the twist by `V(π)`, the contragredient or the semisimplification of
Theorem 5.7, and no statement of Harris is formalized.

## Inputs

The binders are those of
`Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology`, copied from the
published `Langlands.Cohomology.HarrisCMCohomology.Statement`; below `...`
abbreviates `D C ... q U ρ p m hm existence geometry hRigid`. Write
`Rcoeff` for `HarrisCoefficientIntegers K p`.

- From the published `Langlands.Shimura.Coefficients`
  (`HarrisLattice`, `Lattice`): `HarrisCoefficientIntegers K p`, the product
  of `CoefficientIntegers l.1 = l.1.adicCompletionIntegers K` over
  `l : FinitePlacesAbove K p`. From the published `Langlands.Global`:
  `FiniteCompletion K l.1`, the completion of `K` at `l`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology`
  (candidate `d74b579d-a959-4356-9ab5-6ce21cbcbfbc`, staged):
  `cmHarrisAdicCohomology`, `cmHarrisAdicCohomology_isUnramifiedAt` and
  `cmHarrisAdicFrobeniusEulerPolynomial`.
- From `Langlands.Shimura.LatticeGaloisRepresentation`, submitted together
  with this module: `IsLatticeContinuous`, `latticeObjects`,
  `latticeObjects_rank` and `hasEulerPolynomialAt_latticeObjects`.
- From the published `Langlands.GaloisRepresentation`: `LambdaAdic F K lam`,
  which is `Objects F (FiniteCompletion K lam)`, and `HasEulerPolynomialAt`.

## The components of the coefficient ring

Let `K` be a number field, `p` a rational finite place and
`l : FinitePlacesAbove K p`.

- `harrisCoefficientComponentMap K p l : Rcoeff →+* FiniteCompletion K l.1`
  evaluates at the `l`-component and includes `O_{K,l}` into `K_l`
  (`harrisCoefficientComponentMap_apply`).
- `harrisCoefficientComponentAlgebra K p l` is the corresponding algebra
  structure of `K_l` over `Rcoeff`. It is not an instance; the declarations
  below use it locally.

## The l-adic Galois representation

Let `degree : ℕ`.

- `CMHarrisAdicIsLatticeContinuous ... l degree` is
  `IsLatticeContinuous` of `cmHarrisAdicCohomology ... degree` for `K_l`,
  with the component algebra. Every map
  `g ↦ harrisCoefficientComponentMap K p l (f (g · x))` is continuous.

Assume that `(cmHarrisAdicCohomology ... degree).V` is a finite free
`Rcoeff`-module, and let `hcont` be a proof of
`CMHarrisAdicIsLatticeContinuous ... l degree`.

- `cmHarrisLambdaAdicRepresentation ... l degree hcont : LambdaAdic F K l.1`
  is `latticeObjects` of the torsion limit for `K_l`.
- `cmHarrisLambdaAdicRepresentation_representation_apply`: `g` acts by the
  extension of scalars of its action on the torsion limit.
- `cmHarrisLambdaAdicRepresentation_rank`: for nontrivial `Rcoeff`, the
  dimension is the rank of the torsion limit.
- `cmHarrisLambdaAdicRepresentation_hasEulerPolynomialAt ... w hu`: if every
  torsion stage `(cmHarrisGeometricGaloisCohomologyAction ... degree).obj r`
  is unramified at `w`, the representation has as Euler polynomial at `w`
  the image under `harrisCoefficientComponentMap K p l` of
  `cmHarrisAdicFrobeniusEulerPolynomial ... w degree`.

## Proof outline

The representation is `latticeObjects` for the component algebra. The rank
is `latticeObjects_rank`. The Euler polynomial statement is
`hasEulerPolynomialAt_latticeObjects`, applied with the unramifiedness of the
torsion limit given by `cmHarrisAdicCohomology_isUnramifiedAt`; the
algebra map of the component algebra is
`harrisCoefficientComponentMap K p l` by definition.

## Provenance

This is an internal specialization of
`Langlands.Shimura.LatticeGaloisRepresentation` to the `m`-power torsion
limit of `HarrisTaylorCMAdicGaloisCohomology`, with the published
coefficient rings of `Langlands.Shimura.Coefficients` and the published
`LambdaAdic` representations. No representation or polynomial is supplied as
input. Harris (1999), §5, Theorem 5.7 and formula (5.6) on printed p. 313,
are motivation only.

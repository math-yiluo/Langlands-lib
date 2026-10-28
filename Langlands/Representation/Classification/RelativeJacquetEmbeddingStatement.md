# Relative opposite-Jacquet embedding and bounded multiplicity

`Langlands.GLRelativeJacquetEmbeddingStatement` is a proposition definition
for an internal prerequisite of the generic constituent comparison. It is
stated here; its proof is a separate obligation.

For every prime, compatible p-adic field realization `F, T`, positive rank `n`,
block shape `B` and refinement `S`, let `L = B.Levi F` and
`M = refinedLevi F B S`. The input `μ` is an arbitrary irreducible admissible
complex representation of `L`. The actual normalized upper induction is
`I = CuspidalJacquetMultiplicity.induced T B μ = i_L^G(μ)`, where
`G = GL_n(F)`. The statement uses the existing representations

- `innerJacquet T B S μ = r_(op M)^L(μ)`;
- `ambientJacquet T B S μ = r_(op M)^G(I)`.

Both are actions of the same actual refined subgroup `M`. Their coinvariants
use the actual opposite unipotent radicals, with the composed radical for the
ambient module. The normalization is the inverse half of the opposite full
modulus, equivalently the positive half of the corresponding upper full
modulus. The bundlers and their defining import closure remain unchanged.

The first conclusion supplies an actual intertwiner from the inner module to
the ambient module whose underlying function is injective. No particular
choice of this map is specified.

For every complex representation `τ` of `M` and every natural number `M₀`
such that
`HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ M₀` holds, the second
conclusion supplies a natural number `m` such that
`HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m` and `m ≤ M₀`.
Each multiplicity predicate includes an actual finite composition series
with the indicated number of factors equivalent to `τ`. Thus a supplied
ambient series gives existence of an inner series as part of the conclusion.
No inner finite-length hypothesis is imposed. The test representation `τ`
is arbitrary; its irreducibility is not an input to the count bound.

The universes `uF`, `uV` and `uW` are independent: they belong to the field,
test representation and coarse-Levi representation respectively. The inner
carrier lies in `uW`, and the ambient carrier lies in `max uF uW`. The actual
intertwiner and multiplicity predicates allow these different universes.
There are no genericity, cuspidality, unitarity or constituent hypotheses.
The statement supplies an inequality conditional on an ambient series;
equality, positivity and a quotient criterion remain further obligations.

## Internal provenance and proof obligation

This is a derived interface using the published actual functors and theorems,
rather than a transcription of a new assertion from the literature. Its
intended derivation has the following steps.

1. The standard clause of
   `Langlands.Parabolic.irreducibleOppositeJacquetUnit` embeds `μ` into
   `O = r_(op L)^G(i_L^G μ)`. This theorem uses published second adjointness
   and induction nonvanishing and admissibility.
2. Published normalized induction admissibility and
   `Langlands.Parabolic.isAdmissible_standardOppositeJacquet` give smoothness
   of `O`. The injectivity theorem
   `T.normalizedRefinedOppositeJacquetMap_injective` therefore sends the
   embedding to an injection from the inner module into
   `r_(op M)^L(O)`.
3. `Langlands.Parabolic.normalizedOppositeRefinementTransitivity` gives an
   actual equivariant equivalence from that iterated quotient to the ambient
   module. Composing gives the injection required in the first conclusion.
4. Form the quotient of the ambient module by the actual range of this
   injection. `Langlands.jordanHolderShortExactDecomposition` applied to the
   resulting short exact sequence and the supplied ambient count produces
   actual inner and quotient counts `m, c` with `m + c = M₀`. The inequality
   follows from `c ≥ 0`.

The modules for these published ingredients are respectively
`Parabolic.IrreducibleOppositeJacquetUnitProof`,
`Parabolic.NormalizedAdmissibilityProof`,
`Parabolic.StandardOppositeJacquetAdmissibilityProof`,
`Parabolic.OppositeRefinementExactnessProof`,
`Parabolic.OppositeRefinementTransitivityProof` and
`Filtration.MultiplicityAdditivityProof`, all under
`Langlands.Representation`. A separate proof must implement this route
against the published proposition. This interface alone establishes no
generic comparison or irreducible-head consequence.

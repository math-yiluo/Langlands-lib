# Canonical rho big-cell geometric data from opposite root pairs

Module `Langlands.GroupScheme.Reductive.CanonicalRhoOppositePairCovering`. The helper module
`Langlands.GroupScheme.Rational.OppositePairBruhatCovering` is ported together with this
module. Its Markdown documents its six theorems and their proofs.

## Setting

Let `k : Type u` be an algebraically closed field, and `G` a group scheme over `Spec k`
with `[IsAffineHom G.X.hom]` and `hG : IsConnectedReductive G`. Let `j : T.toGrp ⟶ G` be
a maximal torus (`hj : IsMaximalTorus j`) whose torus is split (`hT : IsSplitTorus T.toGrp`).
Let `P` be a root datum of `j` (`hP : IsRootDatumOf j P`, finite index type `J`) with base
`b` and integral coroot span (`hspan : P.corootSpan ℤ = ⊤`). Write
`ν₀ = P.Polarization (IntegralWeylVector.rho P b hspan)` and `λ₀ = groupHom ν₀ ≫ j`.

The rank-one input is `AlgClosedOppositeFactorPairsStatement.{u}`. This separate statement
(module `Langlands.GroupScheme.Rational.AlgClosedOppositeFactorPairsStatement`) asserts
`RelativeRoot.HasOppositeFactorPairs i` for every maximal split torus `i` of every
connected reductive group over every algebraically closed field in universe `u`.

## Definitions

1. `IsRootDatumOf.oppositePairBigCellGeometricData hP b hspan hG hT hj ρ e hν a ha hweight hE :
   SteinbergBigCellGeometricData G` (requires `[P.IsReduced]`, `J : Type u`). It is
   `IsRootDatumOf.canonicalRhoBigCellGeometricData` with the same arguments. Its covering
   argument `hcover` is supplied by (B) below. The inputs `ρ, e, hν, a, ha, hweight` are
   unchanged from the Library assembly:
   - `ρ` is a matrix representation on which `λ₀` acts diagonally with exponents `e`;
   - `a` is the index of the unique minimal exponent;
   - at `a`, the torus acts by the character `-rho`.
2. `SplitPinning.oppositePairHighestWeightBigCellGeometricData p hspan ρ hρ hE :
   SteinbergBigCellGeometricData G`. It is `SplitPinning.highestWeightBigCellGeometricData`
   applied to a representation `ρ` of highest weight rho (`hρ`), with the covering supplied
   by (B) at `(p.isRootDatum, p.base, hspan, p.isConnectedReductive, p.isSplitTorus,
   p.isMaximalTorus)`.
   `oppositePairHighestWeightBigCellGeometricData_eq` records this equality by `rfl`. So the
   witness lemmas `highestWeightBigCellGeometricData_{j,i,n,χ,d}` apply: `H` is the
   parabolic of `λ₀`, `i = Dynamic.Affine.parabolicHom λ₀`, `n` is the opposition
   representative and `χ` is the negative-rho coordinate.

Both definitions construct the six geometric laws of the Steinberg big cell (left and
right covariance, value one at the identity, nonzerodivisor, unit-cell factorization,
intersection in the torus). The irreducibility law is not included.
`SteinbergBigCellGeometricData.withIrreduciblePowers` adds it as a separate input.

## Theorems

- (A) `IsRootDatumOf.borelTorusBruhatCovering_polarization_rho_of_oppositeFactorPairs`: with
  `[Mono j.hom.hom.left]` and `hE : RelativeRoot.HasOppositeFactorPairs j`, it proves
  `BorelTorusBruhatCovering (Dynamic.Affine.parabolicHom λ₀) j`.
- (B) `IsRootDatumOf.borelTorusBruhatCovering_polarization_rho_of_statement`: the same
  conclusion, from `hE : AlgClosedOppositeFactorPairsStatement.{u}`.

The conclusion has exactly the type of the `hcover` hypothesis of
`IsRootDatumOf.canonicalRhoBigCellGeometricData` and
`SplitPinning.highestWeightBigCellGeometricData`. `BorelTorusBruhatCovering` has no Borel
hypothesis. Nothing here proves or uses that the parabolic of `λ₀` is a Borel subgroup.

**Proof of (A) and (B).** `IsMaximalTorus.isMaximalSplitTorus hj hT` makes `j` a maximal
split torus. `IsRootDatumOf.polarization_rho_isGeneric` shows that `ν₀` pairs nontrivially
with every relative root, because rho pairs nontrivially with every coroot. Then
`borelTorusBruhatCovering_parabolicHom_of_oppositeFactorPairs` (helper module) gives the
covering. An algebraically closed field is separably closed. In (B) the hypothesis is
instantiated at `(k, G, hG, T, j)` with this maximal split torus.

## Independence

The construction is independent of the following inputs:

- `ParabolicDynamic*`, `RegularCocharacterBorel*`, `RankOneSolvableObstruction*`,
  `RankOneBorelDynamic*`, `RankOnePositiveRootUniqueness*`;
- `rootDatumExistence`, `rootReducedness`, `reductiveGeometricReductivity`,
  `absoluteBruhatCovering`, `steinbergBigCell`;
- `splitRootLieLine`, `splitRankOneRootCell`, `isParabolicSubgroup_of_range_eq_dynamicParabolic`;
- the projective-Borel rank-one helpers.

Private closure audits over project constants, with no cut, found that the following reach
none of these:

- both definitions, the `_eq` lemma, (A) and (B);
- the six helper theorems;
- the Library assemblies `IsRootDatumOf.canonicalRhoBigCellGeometricData`,
  `SplitPinning.highestWeightBigCellGeometricData` and
  `SplitPinning.negativeRhoExtremalRepresentationData`.

As controls, `isParabolicSubgroup_of_range_eq_dynamicParabolic` and
`splitCommonTorusIsomorphism` are flagged.

The remaining hypotheses are explicit inputs, not consequences of this module:

- the root datum;
- `hspan`;
- the representation data;
- the rank-one statement.

## Provenance

This is an internal assembly of Library constructions with the helper module. It
introduces no new mathematical assertion. Mathematically, the covering is the Tits-system
Bruhat decomposition (Borel–Tits 1965, Théorème 5.15, Library literature id
`borel-tits-1965-groupes-reductifs`) for the parabolic of a generic cocharacter.

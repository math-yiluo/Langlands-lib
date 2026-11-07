# Certified automorphic gamma factors and order transfer

This internal construction packages supplied genuine smooth duals and local
factor certificates into a rational gamma factor, proves that certified factors
are unique, and transfers the arithmetic order bound to every certified
automorphic gamma factor. It also composes the existing global proposition
interfaces for a supplied actual cuspidal contragredient.

## Construction and uniqueness

`Langlands.Correspondence.automorphicPairGammaFactor` takes two genuine
smooth-dual certificates, L-polynomial certificates `P` and `Pd` for the
original and dual pairs, and an epsilon certificate `e`, all with the same
field, additive character and Haar measure. It returns the subtype of certified
rational gamma factors. Its value is the existing
`rationalGammaExpression (residueReflection F) e.1 e.2 P Pd`; its proof component
supplies exactly these witnesses to `IsAutomorphicPairGammaFactor`.
The constructor requires no self-duality of the supplied measure.

`IsAutomorphicPairGammaFactor.unique` proves that two certified rational
gamma factors for the same pair, character and measure are equal. It unpacks
the second certificate, then uses
`IsAutomorphicPairGammaFactor.eq_rationalGammaExpression` from
`AutomorphicGammaGerm` to identify the first with the second certificate's
expression. That imported theorem uses genuine dual-class uniqueness and the
existing L-polynomial and epsilon-factor uniqueness results.
`automorphicPairGammaFactor_subsingleton` applies this equality and subtype
extensionality. It proves a subsingleton assertion; it does not install an
instance or assert that the subtype is inhabited without supplied inputs.

`IsAutomorphicPairGammaFactor.meromorphicAt` proves that rational spectral
evaluation of any certified factor is meromorphic at every complex point.
The proof extracts the certificate's actual dual and factor witnesses, uses
the imported punctured germ comparison with `polynomialGammaExpression`, and
transports its everywhere meromorphy across that punctured equality.
This does not identify numerical values of two expressions at a singular
center. These construction, uniqueness and meromorphy results retain
independent field and automorphic carrier universes `uF` and `uA`.

## Arithmetic certification and orders

`IsPairGammaMatch.isArithmeticPairGammaFactor` accepts a supplied pair gamma
match, a self-dual measure, and any automorphic gamma certificate `hG`.
For that measure the match supplies a common rational factor `H` with both
automorphic and arithmetic certificates. The uniqueness theorem identifies
`G` with `H`, so the arithmetic certificate transports to `G`.
No additional dual, L-polynomial or epsilon-factor certificates are required
beyond those already contained in `hG`.

`IsPairGammaMatch.rationalSpectralValue_order_nonpos` specializes the arithmetic
pair to two local Weil–Deligne representations with unitary underlying Weil
actions. The preceding transfer and the published
`IsArithmeticPairGammaFactor.order_nonpos_of_isUnitary` prove nonpositive
meromorphic order at every `s` with `s.re ≠ 0`.
The field, parameter-carrier and local-constant assignment universes
`u`, `uV`, `uE` remain independent. The automorphic classes use carrier
universe `u`, as required by the imported `IsPairGammaMatch` definition.

`localSelfPair_rationalSpectralValue_order_nonpos` applies the same transfer
to the actual local self-pair of a unitary relative Weil representation `S`
and its algebraic dual. Both are restricted along the same supplied continuous
local Weil homomorphism. The published `localSelfPairGamma_order_nonpos`
provides the arithmetic bound, including the restriction and duality
unitarity arguments. The companion
`localSelfPair_rationalSpectralValue_real_positive_order_only_zero`
uses the corresponding arithmetic real-point theorem: if the order at
`(t₀ : ℂ)` is positive for a real `t₀`, then `t₀ = 0`.
Positive order is the order of a zero. Neither theorem asserts that a zero
at zero exists.

## Supplied global comparison

`weaklyAssociated_dual_of_actual_contragredient` assumes the class-level
contragredient-association proposition at
`ClassContragredientAssociationStatement.{u,uV,uP,uP}`.
For actual cuspidal operator realizations `T`, `T'`, the supplied hypothesis
`T'.realization.IsContragredientOf T.realization` gives the corresponding
class-level relation by
`CuspidalOperatorRealization.isoClass_isContragredientOf_iff`.
The assumed proposition then transports weak association from `S` and
`T.isoClass` to the actual algebraic dual of `S` and `T'.isoClass`, in the
same association universe `uP`.

`associatedSelfPairGammaMatch_of_actual_contragredient` additionally assumes
`AssociatedGammaStatement.{u,uV,uP,uQ,uE}`. It applies that proposition to
`S`, its algebraic dual, `T` and `T'`, using the preceding association
transport. The result compares the actual local classes of the two supplied
spectral presentations with the local arithmetic self-pair.
The number-field, arithmetic-carrier, association-presentation,
input-presentation and local-constant assignment universes
`u`, `uV`, `uP`, `uQ`, `uE` remain independent.
Using `uP` twice in the supplied contragredient-association proposition makes
both associations acceptable to the supplied gamma proposition; it identifies
none of these five universe parameters.

The two final theorems,
`associatedSelfPairGamma_order_nonpos_of_actual_contragredient` and
`associatedSelfPairGamma_real_positive_order_only_zero_of_actual_contragredient`,
compose this match with the local self-pair order theorems. They additionally
require `S.IsUnitary`, a self-dual measure and a certified automorphic gamma
factor for the actual local classes of those presentations.

All global comparison hypotheses remain explicit: an arithmetic fundamental
class family, a global unitary additive character trivial on the diagonal,
weak association, the actual full-operator contragredient relation, both
spectral presentations, irreducibility and admissibility at the chosen
finite place, the place above it, reciprocity candidate, actual local Weil
map and compatibility, canonical finite additive component, reciprocity
family and local-constant system.

## Provenance and scope

This module is an internal composition of the published Library relations,
the certificate and germ comparisons in `AutomorphicGammaGerm`, the arithmetic
unitary bounds in `UnitaryRationalGamma`, the actual-to-class contragredient
comparison, and the two explicitly assumed global propositions. The Lean
proofs follow exactly those compositions. It asserts no new original-source
result and cites no external source.

The module constructs no global cuspidal dual or spectral presentation,
proves neither assumed global comparison proposition, and supplies no
classification or block-factor identity. It does not prove
`AssociatedSupercuspidalInductionStatement`. Its purpose is to make the
conditional order comparison available for any certified automorphic factor
while preserving the original actions and all remaining hypotheses.

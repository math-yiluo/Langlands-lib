# Supercuspidality on all proper rational parabolics of the actual Levi

Worker 1780. This source-facing definition supplies the supercuspidality
hypothesis for the universal induced family in Renard VI.9.2. The registered
source is David Renard, *Représentations des groupes réductifs p-adiques*,
2026 version, source ID
`renard-2026-representations-groupes-reductifs-padiques`. The definition is
VI.2.1, printed p.137 / PDF p.143; the coefficient-family application is
VI.9.2, printed pp.198–199 / PDF pp.204–205.

Renard defines a smooth representation to be supercuspidal when its
normalized Jacquet module vanishes for every proper parabolic subgroup.
The representation need not be irreducible in this definition.
The inducing representation in VI.9.2 is additionally irreducible;
admissibility and irreducibility are separate hypotheses of the family
statement. No implication from this predicate to admissibility is claimed.

`ProperRationalJacquetVanishing σ` is the Jacquet-vanishing condition for a
complex representation of the actual point group `rationalPoints H`.
It quantifies over every pair of group schemes `Q, U` over the original
field, every parabolic embedding `q : Q ⟶ H`, and every geometric unipotent
radical embedding `n : U ⟶ Q`. Its three antecedents are:

- `IsParabolicSubgroup q`, the existing actual geometric parabolic
  predicate;
- `SubgroupFunctor.range q ≠ ⊤`, properness of the embedded subgroup
  functor on all test schemes;
- `LeviSubgroup.IsGeometricUnipotentRadical n`, the existing radical
  predicate over the field and after base change to its algebraic closure.

The conclusion is that
`Jacquet.Localization.Coinvariants σ N 1` is a subsingleton, where `N`
is exactly the image of `n ≫ q` evaluated at
`Over.mk (𝟙 (Spec (CommRingCat.of F)))`. This is the quotient of the
original carrier by the complex linear span of `σ(u)v - v` for every
`u ∈ N`. It expresses that the quotient is zero. Normalizing the action
twists the Levi action on this same underlying quotient, so the vanishing
condition is unchanged. The definition needs no choice of Levi factor,
Haar measure, normalization character, standard parabolic family, or root
index set. Existence of geometric radicals is not asserted here: each
actual represented geometric radical is tested whenever supplied.

`RationalNormalized.leviSchemeRepresentation r σ` is the concrete
pullback of the literal subgroup action through
`parabolicLeviPointHomeomorph r`. For a point `m` of the original Levi
scheme, the action is
`σ (parabolicLeviPointHomeomorph r m)` on the same vector carrier.
This homeomorphism is the published comparison coming from the closed
embedding `l ≫ p` supplied by the verified
`ParabolicRootPresentation p l a`. Its ambient and Levi point topologies
are the canonical rational-point topologies; the literal subgroup carries
the inherited topology.

`RationalNormalized.IsSupercuspidal r σ` is the conjunction of smoothness
of the original literal subgroup action and
`ProperRationalJacquetVanishing (leviSchemeRepresentation r σ)`.
The theorem `isSmooth_leviSchemeRepresentation` applies the published
continuous-pullback smoothness theorem to that homeomorphism. Thus the
vanishing predicate is applied to a smooth representation of the actual
Levi scheme's point group. There is no change of vector carrier or
restriction on its dimension. The field/group universe `u` and carrier
universe `uV` are independent.

These definitions add no finiteness assumption. In VI.9.2, Renard applies
VI.5.3 to the universal supercuspidal family, obtains a filtration with
induced coefficient-family pieces or zero pieces, and deduces coefficient
admissibility of the output Jacquet module. That filtration and the
resulting finite generation of compact-open fixed modules remain proof
obligations of the separate finiteness statement. This module neither
asserts that filtration nor assumes its conclusion as supercuspidality.
It also does not assert the standard-parabolic reduction of VI.2.1,
Remark 1; the quantifier already covers all actual proper rational
parabolics.

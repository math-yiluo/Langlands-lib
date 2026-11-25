# The scalar `j` for the opposite pair `{P, P̄}` (target)

The module
`Langlands.Representation.Plancherel.DynamicOppositePairScalar`
states one Prop-valued target,
`ConditionalDynamicOppositePairScalarStatement`. It is Waldspurger's
IV.3 (1), "`j_P(π)` does not depend on `P ∈ P(M)`", for the two parabolics
`P` and `P̄` of an opposite pair. It is stated for the Library's canonical
scalar `conditionalCanonicalRationalScalar` (the scalar `j_P` of
`J_{P|P̄} J_{P̄|P}`, module `DynamicOppositeCanonicalScalar`), in transport
form for two cocharacters with the same centralizer.

The target is not proved here. The module defines and proves what is
needed to state it:

- the identification of the Levis, representations and actual centralizer
  schemes of two cocharacters `χ`, `ψ` with the same centralizer subgroup
  functor `Z_G(ψ) = Z_G(χ)`;
- the identities `P_G((χ⁻¹)⁻¹) = P_G(χ)` and `U_G((χ⁻¹)⁻¹) = U_G(χ)` on
  rational points, and the Iwasawa decomposition they give for `χ⁻¹`.

It also proves the special case `ψ = χ⁻¹` from the target
(`conditionalDynamicOppositeInverseScalar_of_pair`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- Start of IV.3, printed p.285 / PDF p.51: for `π'` in the nonempty Zariski
  open subset of `O_ℂ` where `I_P^G V'` is irreducible,
  `J_{P|P̄}(π') J_{P̄|P}(π')` is multiplication by `j_P(π')`, and `j_P` is a
  rational function on `O_ℂ`.
- IV.3 (1), printed pp.285–286 / PDF pp.51–52: "`j_P(π)` est indépendant de
  `P ∈ P(M)`." The proof starts from
  `j_{P'}(π) J_{P'|P}(π) = J_{P'|P̄'}(π) J_{P̄'|P'}(π) J_{P'|P}(π)` and
  rewrites it with four instances of the composition formula IV.1 (12),
  printed p.283 / PDF p.49, to get `j_{P'}(π) J_{P'|P}(π) = j_P(π) J_{P'|P}(π)`.
  The common value is written `j(π)`.
- In the source all measures are normalized by the special maximal
  compact subgroup `K` of I.1, printed p.240 / PDF p.6.

## Provenance

The target is a derived statement adapted to the Library's data. It does
not cover arbitrary `P' ∈ P(M)`.

**The case `P' = P̄`.** For `P' = P̄` the starting identity of
Waldspurger's proof reads
`j_{P̄}(π) J_{P̄|P}(π) = J_{P̄|P}(π) J_{P|P̄}(π) J_{P̄|P}(π) = J_{P̄|P}(π) j_P(π)`.
It needs no composition formula. The two scalars are those of the two
composites `J_{P|P̄} J_{P̄|P}` and `J_{P̄|P} J_{P|P̄}` of the same pair of
operators, formed with the same four subgroups `P`, `U`, `P̄`, `Ū` and the
same measures. When `M` is a maximal proper Levi subgroup, `P(M) = {P, P̄}`,
so this case is all of IV.3 (1).

**Why not arbitrary `P'`.** For `P' ∉ {P, P̄}` the proof needs IV.1 (12) for
the actual radicals. This module uses no such formula for the dynamic
radicals; the Library's conditional pointwise form of it is
`conditionalDynamicCommonLeviComposition` (module
`DynamicCommonLeviCompositionProof`). The module `StandardInductionCanonicalScalarComposition`
proves equality of the canonical scalars of two opposite pairs with a
common Levi, conditional on eight composition identities. Moreover
IV.1 (12) is a statement for Waldspurger's measures, normalized by his
special maximal compact subgroup. The Library normalizes the measures on
the radicals by an arbitrary compact open `K` with `G = P K = P̄ K`. For such
`K` the composition identities need not hold without constant factors.
The pair `{P, P̄}` needs neither.

**Cocharacters.** The Library's parabolic data are dynamic: `P = P_G(χ)`,
`U = U_G(χ)`, `P̄ = P_G(χ⁻¹)`, `Ū = U_G(χ⁻¹)` and `M = Z_G(χ)` for a
cocharacter `χ`. The scalar `j_{P̄}` is the canonical scalar of a second
cocharacter `ψ` with `P_G(ψ) = P̄`, for example `ψ = χ⁻¹`. The target is
stated for any `ψ` with the same centralizer subgroup functor,
`Z_G(ψ) = Z_G(χ)`, whose parabolics and radicals on rational points are
those of `χ`:

- in the exchanged order, `P_G(ψ) = P̄`, `U_G(ψ) = Ū`, `P_G(ψ⁻¹) = P` and
  `U_G(ψ⁻¹) = U`; this is IV.3 (1) for `P' = P̄`;
- or in the same order, `P_G(ψ) = P`, `U_G(ψ) = U`, `P_G(ψ⁻¹) = P̄` and
  `U_G(ψ⁻¹) = Ū`; this says that `j_P` does not depend on the cocharacter
  chosen to describe `(P, P̄)`.

The four equalities are hypotheses; the target does not derive the
radicals from the parabolics.

**Compact subgroup.** Both scalars are formed with the same compact open
subgroup `K`. The decompositions `G = P_G(ψ) K` and `G = P_G(ψ⁻¹) K` used
by the data of `ψ` are taken as separate hypotheses `hPK'`, `hOppK'`. Under
the pair hypothesis they say the same as `hPK` and `hOppK`, and as proofs
of propositions their choice does not matter.

**Parameters.** The Library parametrizes the twists `A ⊗ z` by unramified
characters `z` of the actual centralizer scheme `parameterScheme χ`, and
its scalar is an element of the field of rational functions on these
characters. The schemes `parameterScheme χ` and `parameterScheme ψ` are
different objects representing the same subgroup functor. Under the
isomorphism `e = parameterChangeIso χ ψ hM` over `G`, the twist `A ⊗ z`
corresponds to `A ⊗ (z ∘ e⁻¹)` on the equal Levi
(`parameterHomeomorph_parameterChangeIso`). The target therefore reads
`j_{P_G(ψ)}(A ⊗ (z ∘ e⁻¹)) = j_P(A ⊗ z)`: the scalar for `ψ` is the image of
the scalar for `χ` under the field isomorphism `f ↦ (z' ↦ f(z' ∘ e))`
(`rationalUnramifiedFunctionFieldEquiv`, from the module
`DynamicOppositeConjugationScalar`).

## Two cocharacters with the same centralizer

Section `Change` fixes cocharacters `χ`, `ψ` and
`hM : Dynamic.centralizer ψ = Dynamic.centralizer χ`, an equality of
subgroup functors of `G`.

- `changeLevi_mem_iff`: a rational point lies in `levi ψ` iff it lies in
  `levi χ`. Both Levis are the rational points of the centralizer subgroup
  functors, so this is `hM` at the identity point.
- `leviChange χ ψ hM : levi χ ≃ₜ* levi ψ`: the identity of `G(F)`
  restricted to the two equal subgroups, built with
  `QuotientIntegration.subgroupContinuousMulEquiv` from
  `ContinuousMulEquiv.refl`. `leviChange_apply_coe` says that it does not
  change the underlying point.
- `changeRepresentation χ ψ hM A`: the pullback of `A` along the inverse
  of `leviChange χ ψ hM` (`SmoothRep.pullback`). It is the same
  representation on the same space, viewed on `levi ψ`.
- `parameterChangeIso χ ψ hM : parameterScheme χ ≅ parameterScheme ψ`: the
  isomorphism between two schemes representing the same subgroup functor
  (`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`, with
  `Dynamic.Affine.isRepresentedBy_centralizerHom` for `χ` and, rewritten by
  `hM`, for `ψ`).
- `parameterChangeIso_hom_comp`: it commutes with the inclusions
  `Dynamic.Affine.centralizerHom` of the two centralizer schemes in `G`.
  `parameterChangeIso_hom_points` is the same statement on rational
  points.
- `parameterHomeomorph_parameterChangeIso` proves the compatibility
  `parameterHomeomorph ψ ∘ e = leviChange χ ψ hM ∘ parameterHomeomorph χ`
  of the parameter isomorphism with the Library's identifications
  `parameterHomeomorph` of parameter points with the Levis.

## The inverse cocharacter

Section `Inverse` fixes `χ`.

- `inverse_oppositeParabolic`: `oppositeParabolic χ⁻¹ = parabolic χ`.
- `inverse_oppositeRadical`: `oppositeRadical χ⁻¹ = radical χ`.

  Both follow from `Dynamic.inverseCocharacter_inverseCocharacter`. The
  identities `parabolic χ⁻¹ = oppositeParabolic χ` and
  `radical χ⁻¹ = oppositeRadical χ` hold by definition.
- `inverse_oppositeParabolic_mul_compact`: from `G = P K`, the
  decomposition `G = P_G((χ⁻¹)⁻¹) K` used by the data of `χ⁻¹`.

## The target

In the target the local notation `Aψ` stands for
`changeRepresentation χ ψ hM A`.

`ConditionalDynamicOppositePairScalarStatement` quantifies over a
nonarchimedean local field `F`, an affine group scheme `G` of locally
finite type, cocharacters `χ`, `ψ`, the premises `hRefl`, `hCST`,
`hG : IsConnectedReductive G`, the equality `hM` of centralizers and the
pair hypothesis `_hpair`. `_hpair` is the disjunction of the same-order
and the exchanged-order equalities above, as equalities of subgroups of
`G(F)`. It further quantifies over a compact open subgroup `K`, the
decompositions `hPK : G = P K`, `hOppK : G = P̄ K`,
`hPK' : G = P_G(ψ) K`, `hOppK' : G = P_G(ψ⁻¹) K`, and a smooth
representation `A` of `M(F)`. It takes:

- conditional data of the canonical scalar for `(χ, K, A)`, exactly as
  taken by `conditionalCanonicalRationalScalar`: continuations `p`, `q`,
  open nonempty `DForward ⊆ forwardFullDomainRegion χ K hK A` and
  `DReverse ⊆ reverseFullDomainRegion χ K hK A`, and an open nonempty `D`
  on which the unramified induction of `A ⊗ z` from `P` is irreducible
  (`hi`);
- independent conditional data `p'`, `q'`, `DForward'`, `DReverse'`, `D'`,
  `hi'` of the same kind for `(ψ, K, Aψ)`. In the exchanged order `hi'` is
  generic irreducibility of the induction from `P̄`.

Its conclusion is

```
conditionalCanonicalRationalScalar ψ … K hK hPK' hOppK' Aψ p' q' … hi'
  = rationalUnramifiedFunctionFieldEquiv … (parameterChangeIso χ ψ hM)
      (conditionalCanonicalRationalScalar χ … K hK hPK hOppK A p q … hi).
```

## The inverse cocharacter from the target

`conditionalDynamicOppositeInverseScalar_of_pair` assumes the target and
proves its conclusion for `ψ = χ⁻¹`. It uses
`hM = Dynamic.centralizer_inverseCocharacter χ`, the exchanged order
(the first two equalities by definition, the last two by
`inverse_oppositeParabolic` and `inverse_oppositeRadical`), and the
decompositions `hPK' = hOppK` and
`hOppK' = inverse_oppositeParabolic_mul_compact χ K hPK`. It takes
conditional data `p'`, `q'`, `DForward'`, `DReverse'`, `D'`, `hi'` for
`(χ⁻¹, K, A)`, with `A` viewed on `levi χ⁻¹`. The conclusion is
`j_{P̄} = j_P` in this form.

## Intended use

The target is meant to be proved in two steps.

1. Transport. The equalities of subgroups and the isomorphism
   `parameterChangeIso χ ψ hM` identify the data of `ψ` with the data of
   `χ` in the same or the exchanged order: decompositions, Haar measures
   `radicalHaar`, `oppositeRadicalHaar` and quotient measures (all built
   from the subgroups and `K`), compact pictures, convergence domains and
   twists. The Library's
   `conditionalCanonicalRationalScalar_continuation_independent` removes
   the dependence on the continuations.
2. Exchange. In the exchanged order, the scalar for `ψ` becomes the scalar
   of the composite `J_{P̄|P} J_{P|P̄}` for the data of `χ`.
   `standardInductionCompositeCanonicalRationalScalar_eq_reverse` (module
   `StandardInductionScalarSymmetry`) states that, with all subgroup,
   compact-model and measure data fixed, the canonical scalars in the two
   composition orders agree, given generic irreducibility from each
   parabolic. Here these are `hi` and `hi'`.

The target is meant to be combined with the conjugation target
`ConditionalDynamicOppositeConjugationScalarStatement` (IV.3 (3)). Let `w`
be a rational point with `Z_G(wχw⁻¹) = Z_G(χ)` whose cocharacter `wχw⁻¹`
satisfies the exchanged-order equalities, for example a representative of
the nontrivial element of `W(M)` when `M` is maximal. Then the conjugation
target, applied to `A`, and this target, applied to `ψ = wχw⁻¹` and the
conjugate representation `wA` viewed on `M(F)`, together compare `j_P(wA)`
with `j_P(A)`. The conjugation target uses `wKw⁻¹`, which is `K` when
`w ∈ K`. This combination is not carried out here.

## Not proved here

The target. IV.3 (1) for `P' ∉ {P, P̄}`. The composition formula IV.1 (12)
for the actual radicals. IV.3 (4) and (5).

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.

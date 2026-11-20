# Full domains, continuations and irreducibility for a central cocharacter

This module supplies the inputs of the Library's canonical scalar
construction (module `DynamicOppositeCanonicalScalar`) in the case where the
Levi of the cocharacter is the whole group. Let `χ : 𝔾_m → G` be a
cocharacter whose centralizer `levi χ` is all of `G(F)`. Then the parabolic
of `χ` is `G(F)`, and both the radical `U` of `χ` and the opposite radical
`Ū` are trivial.

`conditionalCanonicalRationalScalar` takes the following explicit inputs:

- forward and reverse continuation data `p`, `q` for the actual compact-picture
  integrals;
- open, nonempty parameter sets `DForward`, `DReverse` inside the full domains;
- an open, nonempty parameter set `D` on which the induced representations are
  irreducible.

This module proves that in the central case all three sets can be the set of
all unramified characters. It also constructs `p` and `q`.

Provenance: this is a derived evaluation of the Library's definitions in the
degenerate case `M = P = G` of Waldspurger (2003). In IV.1, printed
pp.276–278 (PDF pp.42–44), Waldspurger defines the intertwining operators
`J_{P'|P}(π ⊗ χ)` by integrals over `(U ∩ U') \ U'`. Theorem IV.1.1 says that
they converge on a cone of parameters and are rational. In IV.3, printed
p.285 (PDF p.51), the scalar `j_P` is defined on the open set of the orbit
where `I_P^G π'` is irreducible. When `U = U' = 1` these integrals are
evaluation at every parameter, and the induction from `G` is the twist of `π`
itself. Waldspurger leaves this case implicit. The
module proves it for the Library's actual objects: the actual quotient measures
at the intrinsic source Haar scale `K` and the actual compact-picture
integrals. No convergence, continuation or irreducibility is assumed.

## Standard integrals over a trivial radical

Section `TrivialRadicalDomain`. The setting is a locally compact
nonarchimedean Hausdorff group `G`, with a semidirect decomposition `P = M U`,
a second subgroup `U'`, and a smooth representation `A` of `M`. The relations
`HasIntegral` and `domain` are the published ones of module
`StandardIntertwiningIntegral`.

- `hasIntegral_eval_of_eq_bot`: the hypotheses are
  - `U' = 1`;
  - Haar measures on `U'` and on `U ∩ U'` that give these trivial groups
    mass `1`;
  - a compatible quotient measure `qν` on `(U ∩ U') \ U'`.

  Then for every vector `f` of the Levi-normalized induction, the integral of
  `u' ↦ f(u' g)` over the quotient converges against every smooth functional
  and is represented by `f(g)`. That is, `HasIntegral h hU U' A qν f (eval f)`
  holds. The proof is the existence half of the published
  `HasIntegral.eq_eval_of_eq_bot` (module
  `StandardLeviPlancherelWeightFullRoot`). Over the one-point quotient, the
  integrand is the constant `ℓ (f g)`. Its integral is `ℓ (f g)` times the
  mass `1` (`integrable_trivialQuotient_iff`, `integral_trivialQuotient`).
- `domain_eq_top_of_eq_bot`: under the same hypotheses, the domain of the
  standard integral is the whole induction (`mem_domain`).
- `standardIntertwiningFullDomainRegion_eq_univ_of_eq_bot`: under the same
  hypotheses, `standardIntertwiningFullDomainRegion h hU U' e ν qν A` (module
  `StandardInductionSelfComparison`) is `Set.univ`. Membership of a parameter
  in this region means that the domain for the twisted representation is `⊤`,
  and the previous item applies to every twist.

## The actual opposite pair of a central cocharacter

Section `DynamicFullLevi`. It uses the setting and local instances of
`DynamicOppositeCanonicalScalar`:

- `χ`, the compact open subgroup `K`, and a smooth representation `A` of
  `levi χ`;
- for the continuation data, also `hRefl`, `hCST`, `hG`, and the Iwasawa
  decompositions `hPK`, `hOppK`.

Every result assumes `hlevi : levi χ = ⊤`.

### Full domains

- `forwardFullDomainRegion_eq_univ_of_levi_eq_top`:
  `forwardFullDomainRegion χ K hK A = Set.univ`.
- `reverseFullDomainRegion_eq_univ_of_levi_eq_top`:
  `reverseFullDomainRegion χ K hK A = Set.univ`.
- `mem_forwardFullDomainRegion_of_levi_eq_top`,
  `mem_reverseFullDomainRegion_of_levi_eq_top`: every unramified character
  lies in each full domain.

The proofs apply `standardIntertwiningFullDomainRegion_eq_univ_of_eq_bot`
with these inputs:

- the trivial radicals `radical_eq_bot_of_levi_eq_top` and
  `oppositeRadical_eq_bot_of_levi_eq_top`;
- the masses `subgroupCompactOpenHaar_univ_of_eq_bot` and
  `sourceIntersectionHaar_univ`, using `U ∩ Ū = 1`
  (`radical_inf_oppositeRadical`);
- the published Weil compatibility `forwardQuotientMeasure_isCompatible` or
  `reverseQuotientMeasure_isCompatible`.

### Continuation data with denominator one

- `conditionalForwardCompactFamily_eq_of_levi_eq_top`: the forward
  compact-picture integral `conditionalForwardCompactFamily … z` is the same
  linear map at any two parameters `z`, `w` of the full domain.
  `conditionalReverseCompactFamily_eq_of_levi_eq_top` states the same for the
  reverse integral. Both pictures are determined by their values on `K`
  (`compactPictureValues_injective`). By the published
  `conditionalForwardCompactFamily_values_of_levi_eq_top` and
  `conditionalReverseCompactFamily_values_of_levi_eq_top`, each integral keeps
  these values.
- `forwardContinuationOfLeviEqTop χ K hK A hRefl hCST hG hPK hOppK hlevi`
  (definition): an element of
  `ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A`, the published
  `RationalOperatorContinuationData` of the forward integrals on their full
  domain. Its fields are:
  - denominator: the constant regular function `1`;
  - numerator: the constant operator, the forward compact-picture integral at
    the trivial parameter `1`;
  - polynomial: `isPolynomialOperatorOn_const`;
  - clears: the numerator equals `1 •` the integral at every parameter, by the
    previous item.
- `reverseContinuationOfLeviEqTop χ K hK A hRefl hCST hG hPK hOppK hlevi`
  (definition): the same construction, an element of
  `ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A`.

### Irreducibility of the induced representations

- `unramifiedLeviInduction_isIrreducible_of_levi_eq_top`: if `A` is
  irreducible, then for every unramified character `z` the representation
  `UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
  (leviNormCharacters χ) (parameterTransport χ z) A` is irreducible. This is
  the Levi-normalized induction from the parabolic of `χ` of the twist `B` of
  `A` by `parameterTransport χ z`. The theorem also takes `hG`, which supplies
  the unimodularity of the radical used by the normalization comparison. The
  proof is a chain of steps:
  - `B` is irreducible (`SmoothRep.isIrreducible_twist_iff`).
  - Its pullback to `G(F)` along the identification `G(F) ≃ levi χ` is
    irreducible (`isIrreducible_comp_continuousMulEquiv_iff`). This pullback
    is `HarishChandraSchwartz.fullLeviAmbientSmoothRep`.
  - The published `HarishChandraSchwartz.fullLeviInductionEquiv` identifies
    the normalized induction from `P = M = G(F)`, `U = 1`, with this pullback.
  - The published `normalizedInductionLeviEquiv` identifies the normalized
    induction with the Levi-normalized one.
  - Irreducibility transfers along the composed equivalence
    (`LengthTwo.isIrreducible_of_equiv`).

## Use

With `hlevi`, the canonical scalar construction can be applied with
`DForward = DReverse = D = Set.univ`:

- the containments `DForward ⊆ forwardFullDomainRegion …` and
  `DReverse ⊆ reverseFullDomainRegion …` follow from the full-domain equalities;
- `p` and `q` are `forwardContinuationOfLeviEqTop` and
  `reverseContinuationOfLeviEqTop`;
- the irreducibility input on `D` is
  `unramifiedLeviInduction_isIrreducible_of_levi_eq_top`.

The published `conditionalCanonicalRationalScalar_eq_one_of_levi_eq_top`
shows that the resulting scalar is `1` for any such choices.

# Normalized functors between actual ambient Levi subgroups

This is internal infrastructure for the rational Jacquet proof. It applies
`GroupTransport` to the actual ambient subgroup models used by geometric terms.
The structural subgroup comparisons and the whole rational Jacquet proposition
remain separate obligations.

## Objects and hypotheses

Let `G : Type uG` be a locally compact nonarchimedean topological group. The
closed subgroups `M` and `M'` contain `L` and `L'`, respectively. The actual
restricted triples

```text
(Q.subgroupOf M, L.subgroupOf M, N.subgroupOf M)
(Q'.subgroupOf M', L'.subgroupOf M', N'.subgroupOf M')
```

have specified semidirect decompositions `h` and `h'`. The ambient radicals
`N` and `N'` are closed in `G`, so their restrictions are closed in the ambient
Levis. The same closedness hypotheses induce local compactness on `M` and `M'`.
No connectedness, algebraicity, reductivity or rational-point premise is used
in this generic adapter.

For a specified element `g : G`, the hypotheses `hMM'` and `hLL'` assert

```text
x ∈ M' ↔ g⁻¹ * x * g ∈ M
x ∈ L' ↔ g⁻¹ * x * g ∈ L.
```

The parabolic and radical comparisons `hQQ'` and `hNN'` require the corresponding
membership equivalences only for `x : M'`. Thus only their restrictions to the
ambient Levi are compared. Jacquet transport does not need `hQQ'`.
The conjugation functors and K0 maps send representations of the unprimed
subgroup to representations of the primed subgroup, by pulling back along
`x ↦ g⁻¹ * x * g`.

## Actual normalized functors

`LeviConjugation.inductionIso` proves the natural isomorphism

```text
i_L^M ⋙ conjugation_M ≅ conjugation_L ⋙ i_L'^M'.
```

Here both induction functors are the existing
`leviNormalizedInductionFunctor`, with actual ambient subgroups `L` and `L'`
as domains. The proof whiskers `GroupTransport.inductionIso` by the canonical
pullback from `L` to `L.subgroupOf M`.

`LeviConjugation.jacquetIso` proves

```text
r_L^M ⋙ conjugation_L ≅ conjugation_M ⋙ r_L'^M'.
```

Both functors are the existing `leviNormalizedJacquetFunctor`, whose codomains
are the actual ambient subgroups `L` and `L'`. The proof whiskers
`GroupTransport.jacquetIso` by the inverse canonical pullback from the primed
nested subgroup to `L'`. In both constructions the composed group maps agree
on their ambient elements, so the functor types agree definitionally.

The representation carrier universe `uV` is independent of `uG`. Induction
uses the existing saturated output universe `max uG uV`; Jacquet restriction
retains its input carrier universe. These natural isomorphisms require no
finite-length or exactness premise. The positive half-modulus for induction
and inverse half-modulus for Jacquet restriction are inherited from the actual
normalized functors and the proved `GroupTransport` comparisons.

## Exact finite-length K0

The maps use `FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ`, with the
existing relations for every finite-length short exact sequence. They require
`ParabolicFiniteLength` for the literal restricted decomposition, under the
local compactness instance induced by the ambient Levi's closedness. This
supplies preservation of finite length and the required exactness for both
normalized functors. The two decompositions may have independently supplied
proofs of those properties.

`inductionMap` is the canonical subgroup-copy pullback followed by
`inductionK0`. `jacquetMap` is `jacquetK0` followed by the inverse copy pullback.
The lemmas `inductionMap_eq_map` and `jacquetMap_eq_map` identify these adapters
with the exact-K0 maps of the actual Levi normalized functors by
`FiniteLengthGrothendieckGroup.map_comp`.

`inductionMap_comp_jacquetMap` cancels the two inverse copy transports. Hence
induction after Jacquet restriction agrees exactly with the original
restricted `inductionK0.comp jacquetK0` term. Its proof rebrackets the composite
and uses `pullback_symm_comp`.

`inductionMap_transport` and `jacquetMap_transport` prove the squares

```text
conjugation_M ∘ inductionMap = inductionMap' ∘ conjugation_L
conjugation_L ∘ jacquetMap = jacquetMap' ∘ conjugation_M.
```

They use the corresponding `GroupTransport` K0 squares and
`pullback_trans`: the canonical subgroup-copy maps commute with the specified
conjugation because their underlying group maps agree. The final theorem
`inductionJacquetMap_transport` composes these two squares to obtain

```text
conjugation_M ∘ (inductionMap ∘ jacquetMap)
  = (inductionMap' ∘ jacquetMap') ∘ conjugation_M.
```

## Provenance and consumer boundary

This pair is internally derived from the published actual normalized functors,
canonical `subgroupOfContinuousEquiv`, generic normalized `GroupTransport`
isomorphisms and exact Grothendieck functoriality. It introduces no new
literature assertion and assumes no representation-theoretic conjugacy
equation. Its purpose is to remove the difference between literal nested
subgroup models and actual ambient descendant subgroups in the survivor
calculation. A rational-point consumer must still prove the required subgroup
membership comparisons for its specified normalizer lift and discharge the
geometric expansion, common-term reduction and longest-survivor comparison.

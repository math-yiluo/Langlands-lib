# Integral reflections of a split maximal torus from Weyl-group rationality

Worker 835.

This module constructs actual `RelativeRootReflectionData i` for every split
maximal torus `i : T.toGrp ⟶ G` of a connected reductive group over an
arbitrary field. It takes one explicit input,
`SplitMaximalTorusWeylRationalityStatement.{u}`
([`SplitWeylRationalityStatement`](SplitWeylRationalityStatement.md), Milne 2017
Proposition 21.1), which this module does not prove. Everything else is proved
here from published Library results. The construction does not use the
relative reflection statement `RelativeRootReflectionExistenceStatement`, the
full-kernel component-reductivity statement
`KernelCentralizerComponentReductiveStatement`, the rational Bruhat
decomposition or the root-spanning statement
`RelativeCharacterRootComplementStatement`.

## Source and provenance

The mathematical target is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 21.11(d),(e), printed p.429 (PDF p.445):
for a root `α` of a split reductive group `(G,T)`, the nontrivial element
`s_α` of `W(G_α,T)` is represented by some `n_α ∈ N_{G_α}(T)(k)`. There is a
unique `α^∨ ∈ X_*(T)` with `s_α(x) = x - ⟨x,α^∨⟩α` and `⟨α,α^∨⟩ = 2`. There
`T_α` is the codimension-one subtorus of `T` in the kernel of `α` and
`G_α = C_G(T_α)` (printed p.428, PDF p.444).

The implemented route is derived and differs from Milne's proof, which uses
the classification of groups of semisimple rank one (Milne 20.32). Here:

- the rank-one group is the published dynamic centralizer of a generic
  cocharacter annihilating `α`, not `C_G(T_α)`;
- integrality of the coroot comes from the fact that this centralizer
  centralizes the full scheme-theoretic kernel of `α` (proved below by
  closed generation by the torus and its root subgroups);
- rationality of the representative comes from Weyl-group rationality
  (Milne 21.1), applied after base change to an algebraic closure.

## Integrality: the rank-one centralizer centralizes the root kernel

`RankOneCentralizerDetection.kernelCentralizer_torusHom_eq_top` works over any
field `k`. Assume `IsConnectedReductive G`, `IsSplitTorus T.toGrp`,
`IsMaximalTorus i` and `α ∈ roots i`. Write `L` for the published
`RankOneCentralizerDetection.groupScheme i hT α`. It represents the dynamic
centralizer of the cocharacter `RankOneCentralizerDetection.cocharacter`,
which pairs to zero with `α` and is nonzero on every root not integrally
dependent on `α`. Write `t` for the factored torus `torusHom`. The theorem
states the equality of subgroup functors of `L`

`RelativeRoot.kernelCentralizer t α = ⊤`,

on every test scheme. So every point of `L` commutes with every point of the
full kernel of `α`, including its nonreduced part.

The proof is as follows.

1. `dynamicCentralizerReductive` makes `L` connected reductive.
   `IsMaximalTorus.of_comp` makes `t` a maximal torus of `L`, and
   `RootReducedness.mem_roots_torusFactor` makes `α` a root of `t`.
2. `RelativeRoot.kernelCentralizerStructure` provides a closed subgroup
   `j : C ⟶ L` representing `kernelCentralizer t α`.
3. `maximalTorusCentralizer` gives `torusCentralizer t = range t` in `L`.
   `RelativeRoot.weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing`
   then puts the zero adjoint weight space in the tangent image of `t`.
4. The published closed-generation theorem
   `range_eq_top_of_torus_and_rootSubgroups`, for the smooth connected affine
   group `L`, reduces `range j = ⊤` to two containments:
   - The torus: `RelativeRoot.range_le_kernelCentralizer`.
   - Every intrinsic root subgroup `RelativeRoot.subgroup t β`, `β` a root of
     `t`. The published `RankOneCentralizerDetection.roots_pairwise_dependent`
     makes `β` and `α` integrally dependent. The published `rootReducedness`,
     applied to `L` and `t`, gives `β = α` or `β = -α`. Then
     `RelativeRoot.subgroup_le_kernelCentralizer` or
     `RelativeRoot.opposite_subgroup_le_kernelCentralizer` applies.

## Rationality: a rational nontrivial Weyl class

`SplitWeylRationality.exists_nonidentityNormalizer_of_algClosed` works over an
algebraically closed field. For a connected reductive group, a split maximal
torus and a root, it produces a rational normalizing point whose class in
`relativeWeylGroup i` is nontrivial. Its proof is the construction in the
published `RootReducedness.neg_mem_roots_of_rankOne_algClosed`. A proper
Borel pair containing the torus (`exists_proper_isBorelPair_of_relativeRoot`),
solvable maximal torus conjugacy and the proper quotient data feed
`nonidentityNormalizerOfRootedSolvableQuotient`.

`SplitWeylRationality.exists_nonidentityNormalizer` takes the input `hW` and
works over any field. It has the same conclusion over `k`. The proof
base-changes `G`, `T` and `i` to `AlgebraicClosure k`, using the published
`IsConnectedReductive.baseChange_toAlgebraicClosure`, `maximalTorusBaseChange`,
`IsSplitTorus.baseChange` and `mem_roots_baseChange_iff`. There it chooses a
normalizing point `w` with nontrivial class. `hW` gives a rational point `n`
and `σ : T ≅ T` with `IsNormalizingPoint i n σ` whose base change is the
normalizing automorphism of `w`. If the class of `n` were trivial, `n` would
normalize through `Iso.refl T`. Then `IsNormalizingPoint.unique` gives
`σ = Iso.refl T`, so `w` would normalize through the identity, that is, have
trivial class.

## Integral reflections and the reflection data

`SplitWeylRationality.exists_reflection` works over any field, takes `hW`, and
has the hypotheses of the integrality theorem. It concludes that there are a
normalizing point `n` of `i` and a cocharacter `ν` with `⟨α, ν⟩ = 2` and
`weylAction i n χ = χ - ⟨χ, ν⟩ • α` for every character `χ`. The proof
applies `exists_nonidentityNormalizer` to `L` and `t`, which is legitimate
because `L` is connected reductive and `t` is a split maximal torus with root
`α`. This gives `m`. The published
`IsConnectedReductive.weylAction_eq_neg_of_rankOne` holds over any field and
uses the pairwise dependence of the roots of `t`. It shows that `m` sends `α`
to `-α`. By the integrality theorem, `m` lies in `kernelCentralizer t α`. The
published `IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer` then
yields `ν` with the two displayed properties for `weylAction t m`. Finally
`normalizerPointsMap` carries `m` to a normalizing point of `i` along the
inclusion `L ⟶ G` and `torusHom_comp`, and `weylAction_normalizerPointsMap`
shows that its action is unchanged.

The selected definition `SplitWeylRationality.reflectionData hW hG hT i hi`
is the resulting `RelativeRootReflectionData i`. For each actual root it
chooses the normalizing point as `representative` and the cocharacter as
`coroot`. `pair_self` and `action` are the two properties above. The ambient
affineness instance comes from `hG` and the torus monomorphism from the
closedness in `hi`.

## Scope

This module does not prove Weyl-group rationality. It also does not assert
that the representatives centralize the full kernel in `G`, or that `L`
equals Milne's `C_G(T_α)`. It does not assemble the root datum itself. That
assembly from integral reflection data and the finite Weyl image is a
separate step (Worker 1223's finite-Weyl-image assembly). The
universe `u` and the field are arbitrary, and the characteristic is
unrestricted.

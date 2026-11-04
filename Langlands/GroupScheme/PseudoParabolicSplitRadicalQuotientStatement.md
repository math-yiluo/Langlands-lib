# Pseudo-parabolic descent under a supplied split-radical quotient

`Langlands.GroupScheme.PseudoParabolicSplitRadicalQuotientStatement.{u}` is a
Prop-valued definition. It states the structural pseudo-parabolic descent used
in the first reduction of the proof of Lemma C.2.1 in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015). It proves nothing; its proof
is a separate successor task.

## Source basis

The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`
(SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`).
No project errata note for this source exists in the public notes.

- Lemma C.2.1 and its proof, printed pp.592–593 (PDF pp.618–619). `G` is a
  smooth connected affine group over a field `k` and `P` a pseudo-parabolic
  `k`-subgroup. The proof sets `U = R_{us,k}(G)`, the maximal `k`-split smooth
  connected unipotent normal `k`-subgroup, notes `U ⊆ P`, and asserts that
  `P/U` is a pseudo-parabolic `k`-subgroup of `G/U` with
  `(G/U)/(P/U) = G/P`. The present proposition is the first half of that
  assertion: `P/U` is pseudo-parabolic in `G/U` and its full preimage in `G`
  is exactly `P`. The identification of the homogeneous quotients is not part
  of it.
- Corollary 2.1.9 and its proof, printed p.58 (PDF p.84). For a flat surjective
  homomorphism `π : G → G'` of connected affine groups of finite type and a
  cocharacter `λ`, `π(P_G(λ)) = P_{G'}(π ∘ λ)`.
- Proposition 2.2.4 and its proof, printed pp.63–64 (PDF pp.89–90). The
  equality `P_G(λ) R_{u,k}(G) = P_G(λ) R_{us,k}(G)`, with its reduction
  through `G/R_{us,k}(G)`.

These passages support the statement. Their structural content, including the
image of `R_{u,k}(G)` in `G/U`, is the successor's proof obligation; the source
gives this reduction in one sentence.

## The Lean proposition

Fix an arbitrary universe `u`, a field `k : Type u` and `B = Spec (CommRingCat.of k)`.
The proposition quantifies over:

- actual group schemes `G` and `H` over `B`, each with `Smooth`, `IsAffineHom`
  structure morphism and `ConnectedSpace` underlying scheme (instance binders);
- an actual group scheme `N` and a homomorphism `n : N ⟶ G` with
  `IsSplitUnipotentRadical n`, the published predicate from
  `Langlands.GroupScheme.Reductive.UnipotentRadical`. It says that `n` is a
  closed subgroup with smooth, connected, unipotent and split-unipotent source
  (the finite `Ga`-series predicate `RelativeRoot.IsSplitUnipotent`) and normal
  image, and that its all-test image is greatest among such subgroups. This is
  the source's `R_{us,k}(G)`;
- every actual homomorphism `f : G ⟶ H` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f`. That published
  predicate requires `f` to be flat, surjective and locally of finite
  presentation, and the actual scheme kernel of `f` to have exactly the
  subgroup functor `SubgroupFunctor.range n` on every relative test. No
  quotient model is chosen, and no lifting of points on the original rational
  or affine tests through `f` is assumed;
- every actual `P` and `i : P ⟶ G` with `IsPseudoParabolicSubgroup i`, the
  published predicate from `Langlands.GroupScheme.PseudoParabolic`. It
  presents `i` as a closed subgroup representing the fppf-local product
  `P_G(χ) R_{u,k}(G)` for an actual cocharacter `χ`, with a represented
  ground-field unipotent radical (CGP Definition 2.2.1, printed p.62, PDF
  p.88).

The conclusion produces an actual group scheme `K` over `B` and a
homomorphism `j : K ⟶ H` such that

- `IsPseudoParabolicSubgroup j` holds, with the same unchanged predicate now
  applied in `H`;
- `SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f`.

The equality is between subgroup functors on all relative schemes `T` over `B`.
By `SubgroupFunctor.mem_comap`, it says that a `T`-point `x` of `G` factors
through `i` if and only if `x ≫ f` factors through `j`. It covers nonaffine and
nonreduced tests, and it is stronger than equality of rational-point or
geometric-point subsets. In the source's notation `K = P/U`, `j` is its
inclusion into `G/U`, and the equality is `P = f⁻¹(P/U)`.

## What is a conclusion, and what is supplied

The existence of the subgroup `K` with `j`, its pseudo-parabolicity, and the
exact all-test preimage equality are conclusions of the proposition. No premise
asserts any of them, nor any rational or affine-test surjectivity of `f`, nor
any theorem-valued fact. The inclusion `U ⊆ P` is not assumed either. It
already follows from the hypotheses through
`IsPseudoParabolicSubgroup.splitRadical_le`.

Group quotient existence is deliberately outside this proposition. The quotient
homomorphism `f` and the smoothness, affineness and connectedness of its target
`H` are supplied. They hold for the true quotient `G/R_{us,k}(G)`. Proving that
such an `f` exists is the separate normal affine quotient task.

## Scope

Every field is allowed, including imperfect and finite fields, in every
characteristic. There is no reductivity, pseudo-reductivity, perfectness,
infinitude or existing-section hypothesis. The universe `u` is arbitrary. The
proposition does not construct a quotient, prove the descent, or address
rational lifting through `G → G/P`.

# A fixed split torus containing the full centre, from a reductive semidirect product

This module proves, in every universe `u`, that two inputs imply the exact target
`FixedCenterContainingTorusStatement`:

- `AlgClosedMaximalTorusCentralizerStatement` (module
  `Absolute/MaximalTorusCentralizerReduction`; Milne, Proposition 17.61(a), the
  algebraically closed case of Corollary 17.84). This published Library proposition
  says that a maximal torus of a connected reductive group over an algebraically
  closed field is its own centralizer, as an equality of subgroup functors. It is not
  yet proved in the Library.
- Reductivity of semidirect products: for every algebraically closed field `k`,
  connected reductive group `G` over `k`, commutative group scheme `S` over `k` that is a
  split torus, and automorphic action `b` of `S` on `G`, the semidirect product
  `H = G ⋊_b S` (`b.semidirectProduct`) is connected reductive.

Both inputs are explicit hypotheses. The module proves neither of them, and it does
not prove the target unconditionally. Unlike the companion reduction module
`Reductive.FixedCenterContainingTorusReduction`, it does not use conjugacy of maximal tori
(`MaximalTorusConjugacyStatement`).

## Declarations

- `exists_fixed_splitTorus_containing_center_of_semidirect_reductive`: the conclusion
  of the target for one `G`, `S` and `b`, from the first input and reductivity of that
  one semidirect product (described below).
- `FixedCenterContainingTorusSemidirectReductionStatement` (a `Prop` definition): the
  implication from the two inputs above, the second quantified over all `k`, `G`, `S`
  and `b` exactly as listed, to `FixedCenterContainingTorusStatement`.
- `fixedCenterContainingTorusSemidirectReduction`: the proof of that implication. It
  applies the first theorem to each instance of the target.

## The theorem

`exists_fixed_splitTorus_containing_center_of_semidirect_reductive hcent G hG S hS b hH`
assumes `hcent : AlgClosedMaximalTorusCentralizerStatement` and
`hH : IsConnectedReductive b.semidirectProduct`. For an algebraically closed field
`k`, a connected reductive group `G` over `k` (`hG`), a commutative group scheme `S` over `k` that is a split torus (`hS`), and an
automorphic action `b` of `S` on `G` whose semidirect product is connected reductive
(`hH`), there are a commutative group scheme `T` and a homomorphism `j : T ⟶ G` such
that

- `T` is a split torus and `j` is a closed subgroup;
- the full scheme-theoretic centre `center G` is contained in the range of `j`, as
  subgroup functors on every test scheme;
- `S` fixes the points of `T`: for every test scheme `U` and points `s` of `S`, `t` of
  `T` over `U`, `b.act s (t ≫ j) = t ≫ j`.

## The proof

1. **The fixed torus.** The proved
   `AutomorphicAction.exists_maximalTorus_with_fixed_intersection` gives a maximal
   torus `j : M ⟶ H` through which `S` factors. Its actual intersection
   `T₀ = b.semidirectTorusIntersection j` with the normal factor `G` is a torus. The
   inclusion `T₀ ⟶ G` is a closed subgroup, and `S` fixes the points of `T₀` on every
   test scheme. Over the algebraically closed field `T₀` is split, by
   `torusFiniteGaloisSplitting` and `IsTorus.isSplitTorus_of_finiteGaloisSplitting`.
   The torus `T₀` with this inclusion is the witness, so only centre containment
   remains.
2. **The centre of `G` is central in `H`.** The inclusion `semidirectInl : G ⟶ H` is a
   closed subgroup (`isClosedSubgroup_semidirectInl`), and its range is normal on all
   tests (`RelativeRoot.range_semidirectInl_isNormal`). Both `G` and `H` are
   connected reductive. The proved
   `center_le_comap_of_normal_of_algClosedMaximalTorusCentralizer`, applied with
   `hcent`, gives `center G ≤ (center H).comap semidirectInl`.
3. **The centre of `H` lies in `M`.** By `center_le_torusCentralizer` the centre of
   `H` lies in the centralizer of `M`. By `hcent` applied to `H` and its maximal torus
   `M`, that centralizer is the range of `j`.
4. **Centre containment.** Let `x` be a point of `center G` over a test scheme `U`. By
   steps 2 and 3, `x ≫ semidirectInl` lies in the range of `j`. It also lies in the
   range of `semidirectInl`, so it lies in their intersection, which is the range of
   `T₀ ⟶ M ⟶ H` by `range_commutativeSubgroupIntersection`. The commuting square
   `semidirectTorusIntersection_condition`, together with the cancellation of the
   monomorphism `semidirectInl`, writes `x` as a point of `T₀`.

The conclusion holds for every test scheme, including nonreduced ones. No
smoothness or reducedness of the centre is used. The witness torus need not be
maximal in `G`, and the target does not require that.

## Provenance

**Derived.** The conclusion is the body of `FixedCenterContainingTorusStatement`,
which comes from Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition 3.3.10(c) (printed p.113, PDF p.139) and Corollary A.4.7(2)
(printed pp.495–497, PDF pp.521–523). Their argument factors the action through the
adjoint quotient and lifts a maximal torus from there. This module follows a
different, internal argument: in the reductive group `G ⋊ S` the centre of the normal
factor `G` is central, hence lies in every maximal torus (Milne, *Algebraic Groups*
(2017), Proposition 17.61(a) and Corollary 17.84, printed pp.372 and 379, PDF pp.388
and 395), in particular in one containing `S`. Worker 1334 proposed this route, which
removes the conjugacy premise. The Lean arrangement, the `Prop` definition and the proofs are Worker 1544's.

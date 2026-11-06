# Proof: the rank-one obstruction for smooth connected solvable subgroups

Worker 1453, with Worker 1462 contributing the algebraic-closure witness
transport route. The theorem
`Langlands.GroupScheme.rankOneSolvableObstruction` proves exactly
`Langlands.GroupScheme.RankOneSolvableObstructionStatement.{u}` from
`Absolute.RankOneSolvableStatement`.

For every field `k : Type u`, let `G` be connected reductive, let
`j : T.toGrp ⟶ G` be a split maximal torus, and let `i : H ⟶ G` be a smooth
connected solvable closed subgroup through which `j` factors. For each
`α ∈ roots j`, the image of the actual tangent map from `Lie(H)` cannot
contain both a nonzero vector in `weightSpace j α` and a nonzero vector in
`weightSpace j (-α)`. The theorem adds no premise and retains arbitrary
characteristic, imperfect fields, and universe `u`. It asserts exclusion of
the pair of witnesses; it does not require `H` to meet either root space.

## Implemented proof

The Lean proof applies
`rankOneSolvableObstruction_of_geometricStatements` from
`Absolute.RankOneAlgebraicClosureReduction`, supplying all four arguments:

- `rankOneBorelDynamic` from `Reductive.RankOneBorelDynamicProof` proves
  `RankOneBorelDynamicStatement`. Over an algebraically closed field, when
  all actual roots are pairwise integrally dependent, a prescribed Borel
  through the specified split maximal torus represents one of the two
  opposite dynamic parabolics for any cocharacter nonorthogonal to a root.
- `dynamicCentralizerReductive` from `Dynamic.CentralizerReductiveProof`
  proves `DynamicCentralizerReductiveStatement`, supplying connected
  reductivity of the actual centralizers used by the reduction.
- `centralizerBorelIntersection` from
  `Absolute.CentralizerBorelIntersectionProof` proves
  `CentralizerBorelIntersectionStatement`. The reduction uses the published
  actual-intersection adapter to apply this result to the first projection
  of the scheme-theoretic intersection with the prescribed Borel.
- Forward preservation of maximal tori is obtained from
  `maximalTorusBaseChange` in `Torus.MaximalBaseChangeProof`. For a maximal
  torus `i`, the proof extracts its torus and closedness hypotheses
  `hi.1` and `hi.2.1`, then applies the forward implication of
  `maximalTorusBaseChange k K G T i hi.1 hi.2.1` to `hi`.

The imported reduction first passes the original subgroup `H`, its torus
factorization, the root, and the two hypothetical tangent witnesses to the
chosen algebraic closure. Connected reductivity, splitness, maximality,
closedness, smoothness, connectedness, and solvability are preserved by
the proved transport results used there. In particular, smoothness and
affineness give connectedness after base change, while the definition of
solvability already supplies solvability of the chosen closure's rational
points. Each nonzero weighted witness retains its actual tangent preimage
under `weightSpace_lieImage_baseChange`; character pullback preserves the
negative. A Borel containing the transported `H` also contains the specified
torus through the transported factorization.

For this Borel and a root `α`, the published centralizer reduction chooses
a cocharacter `ζ` annihilating `α` such that every root annihilated by `ζ`
is integrally dependent with `α`. The canonical centralizer is connected
reductive, contains the same split maximal torus, and has pairwise dependent
roots. Its actual intersection with the Borel is a Borel through that
torus. The weight-zero centralizer comparison and the tangent pullback
lemma lift both hypothetical vectors to this same intersection.
The rank-one classification now identifies its embedding with one of the
two signed dynamic parabolics. The proved dynamic weight exclusion rules
out simultaneous nonzero witnesses of opposite weights. This contradiction
over the algebraic closure excludes the original witnesses over `k`.

## Source and provenance

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), Lemma 21.28, printed p.433, PDF p.449
(registered source `milne-2017-algebraic-groups`). Milne proves that a Borel
through a split maximal torus contains exactly one of the root subgroups
`U_α` and `U_{-α}`. His proof centralizes the torus
`T_α = (Ker α)_t`, uses the two rank-one Borels from Lemma 20.20
(printed pp.414–415, PDF pp.430–431), and uses 17.72
(printed p.376, PDF p.392) to identify the intersection with the original
Borel as a Borel of that centralizer.

The Lean statement is the derived arbitrary-field, solvable-subgroup,
Lie-image version. Its proof keeps Milne's centralizer and Borel-intersection
strategy, but chooses an actual cocharacter cutting out the required
dependent roots instead of constructing `T_α`. It uses the proved dynamic
rank-one classification and dynamic Lie-weight exclusion instead of naming
the two root subgroups. The algebraic-closure and tangent-witness transport
steps extend the Borel case to the exact original `H` and field.
Neither `RegularCocharacterBorelStatement` nor
`ParabolicDynamicStatement` supplies an input to this proof. In particular,
the derivation does not appeal to Milne's subsequent general classification
of Borels by regular cocharacters.

This module introduces no new structural assertion beyond composing the
named Library proofs. The details of the internal reductions are documented
in `Absolute.RankOneAlgebraicClosureReduction`,
`Absolute.RankOneCentralizerReduction`, and `Dynamic.WeightExclusion`.

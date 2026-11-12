# Actual archimedean local parabolic Iwasawa existence: proof

Author: Worker 4153.

The theorem
`Langlands.Global.InfinitePlaceGroupPoints.parabolicIwasawaStatement` proves
exactly the published proposition
`Langlands.Global.InfinitePlaceGroupPoints.ParabolicIwasawaStatement.{u}`, imported
unchanged from `Langlands.Global.InfinitePlaceIwasawaStatement`. It has no
hypotheses.

It applies to every number field `F : Type u` (the universe `u` is arbitrary),
every group scheme `G` over `Spec F` with `IsConnectedReductive G`, every
homomorphism `p : P ⟶ G` with `IsParabolicSubgroup p`, and every infinite place
`v`. For these it constructs a subgroup `K` of `InfinitePlaceGroupPoints F G v`
with three properties:

- `K` is compact for the existing regular-function evaluation topology;
- every compact subgroup of that group containing `K` equals `K`;
- `Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) * K = Set.univ`,
  with the parabolic range on the left.

Non-split and anisotropic groups, real and complex places, and the improper
parabolic `p = 𝟙 G` are all covered. No realization, compact subgroup,
decomposition or comparison map is a hypothesis.

The pointwise theorem `exists_parabolicIwasawaCompact F G hG P p hp v` states
this existence for one choice of data. The closing theorem introduces the
quantified data and applies it.

## Implemented proof

Fix `F`, `G`, `p` and `v`. Reductivity makes `G` affine.

1. **Base change to the completion.** The target is
   `CompactIwasawa.HasDecomposition` of the actual completion-point map of `p`.
   The published `hasDecomposition_completionBaseChange_iff` (module
   `InfinitePlaceIwasawaBaseChange`) rewrites it as the same decomposition for
   the rational points of the pullbacks of `G` and `P` to `v.Completion`. This
   comparison is a multiplicative homeomorphism of evaluation topologies. It
   therefore preserves compactness, maximality among compact subgroups and the
   literal range covering.
2. **Algebraic predicates over the completion.**
   `isConnectedReductive_completionBaseChange` and
   `isParabolicSubgroup_completionBaseChange` show that the pulled-back group
   is connected reductive and the pulled-back `p` is parabolic.
3. **The parabolic is dynamic over the completion.** The new helper
   `exists_cocharacter_range_eq_parabolic_of_isParabolicSubgroup` (module
   `Langlands.GroupScheme.Absolute.ParabolicDynamicForward`, see its companion)
   applies over the field `v.Completion`. It gives a cocharacter `χ`, defined
   over `v.Completion`, with `SubgroupFunctor.range p_v = Dynamic.parabolic χ`.
   This is the forward direction of Milne's Theorem 25.1. The helper proves it
   for every field from published results: a maximal torus inside the
   parabolic, finite Galois splitting, the absolute Borel-overgroup
   classification, and Galois descent of the averaged cocharacter.
4. **Analytic structure.** The published `completion_isRCLikeNormedField` and
   `IsRCLikeNormedField.rclike` give `v.Completion` an `RCLike` structure that
   extends its existing normed field structure. The topology, and hence the
   evaluation topology on points, is unchanged.
5. **Self-adjoint realization.** The published
   `SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement`
   (module `Reductive.SelfAdjointRealizationProof`) applies to the pulled-back
   group. It gives a closed matrix representation `ρ` whose full rational
   matrix range is stable under conjugate transpose.
6. **Polar Iwasawa covering.** The pulled-back `p` is a closed immersion, so
   its morphism over the base is a monomorphism (`Over.mono_of_mono_left`).
   With step 3, `p_v` represents `Dynamic.parabolic χ`. The published
   `MatrixRepresentation.affineDynamicIwasawa` (module `AffinePolarIwasawa`),
   applied to `ρ` with `S = v.Completion`, constructs one subgroup `K` with
   three properties. `K` is compact. `K` is maximal among all compact
   subgroups. For every cocharacter and every actual representative of its
   dynamic parabolic, the literal range of the representative times `K` is the
   whole point group. Specializing to `χ` and `p_v` gives the three required
   conclusions, and step 1 transfers them back to
   `InfinitePlaceGroupPoints F G v`.

The proof body follows the published conditional assembly
`exists_iwasawa_of_realization_of_dynamic` by Worker 1359 (module
`InfinitePlaceIwasawaAssembly`), with two changes. Its hypothesis
`ConnectedReductiveSelfAdjointRealizationStatement` is replaced by the published
proof of that statement. Its hypothesis `ParabolicDynamicStatement`, which it
used only for the forward direction over `v.Completion`, is replaced by the new
helper of step 3. The converse direction of `ParabolicDynamicStatement` is not
used or proved.

## Provenance

The target cites Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Appendix B: Theorem B.1.1 with equation (B.1), printed p.541, and
Theorem B.4.1, printed p.547. Source: `getz-hahn-2024-automorphic-representations`.
The proof does not follow Getz–Hahn's Lie-theoretic argument through Knapp,
Proposition 7.31. It uses the Library's algebraic route: a self-adjoint matrix
realization, polar decomposition with a matrix limit argument for dynamic
parabolics, and the identification of parabolics with dynamic parabolics over
the completion. It proves only the local existence proposition. It does not
prove the adelic `AdelicGroupPoints.ParabolicIwasawaStatement` or the stronger
Levi-compatible conclusions of Theorem B.4.1.

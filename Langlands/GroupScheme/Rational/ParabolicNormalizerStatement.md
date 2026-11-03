# Parabolic subgroups are self-normalizing: statement

Authors: Worker 823 and Worker 1346.

`Langlands.GroupScheme.ParabolicSelfNormalizerStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. Publication of this statement does not prove it; its proof is a
separate obligation.

## Statement and quantifiers

For every field `k : Type u`, every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` satisfying `IsConnectedReductive G`, every group
scheme `P : GroupScheme (Spec (CommRingCat.of k))`, and every homomorphism `j : P ⟶ G`
satisfying `IsParabolicSubgroup j`, the statement asserts

```lean
(SubgroupFunctor.range j).normalizer = SubgroupFunctor.range j
```

It uses the following existing Library definitions:

- `SubgroupFunctor.range j` (`Langlands.GroupScheme.SubgroupFunctor`) assigns to each test
  `U : Over (Spec k)` the subgroup of points `U ⟶ G.X` that factor through `j`, namely the
  points `y ≫ j.hom.hom` with `y : U ⟶ P.X`.
- `SubgroupFunctor.normalizer F` (`Langlands.GroupScheme.Rational.TorusNormalizer`) assigns
  to `U` the points `g : U ⟶ G.X` such that, for every test `V`, every morphism `a : V ⟶ U`,
  and every `x ∈ F(V)`, both `(a ≫ g) * x * (a ≫ g)⁻¹` and
  `(a ≫ g)⁻¹ * x * (a ≫ g)` belong to `F(V)`.
- `IsParabolicSubgroup j` (`Langlands.GroupScheme.Absolute.Borel`) requires a closed
  immersion `j`, smoothness of `P` over `k`, and a Borel subgroup of `G` after base change
  to `AlgebraicClosure k` that factors through the base change of `j`.
- `IsConnectedReductive G` (`Langlands.GroupScheme.Reductive.Basic`) requires smoothness,
  affineness, connectedness, and triviality of the geometric unipotent radical.

There are no additional hypotheses of perfectness or characteristic of `k`, splitness of
`G`, connectedness of `P`, a chosen maximal torus or Borel subgroup, or any assumed structural
theorem.

## All-test scope

The equality is an equality of subgroup functors at every `k`-scheme test
`U : Over (Spec k)`, including non-affine and nonreduced tests. It expresses the
scheme-theoretic equality `N_G(P) = P`, rather than only an equality at `k`-points.
Here `P` is identified with its image through the closed immersion `j`.

For every field extension `K/k`, evaluating at `Spec K` gives
`N_G(P)(K) = P(K)`. Equivalently, a point `g ∈ G(K)` whose conjugation preserves the
subgroup scheme `P_K` belongs to `P(K)`; the normalizer condition is tested on all further
`K`-scheme refinements. The elementary inclusion of a subgroup functor in its normalizer is
already proved by `SubgroupFunctor.le_normalizer`; the reverse inclusion remains to be proved
for parabolic subgroups.

## Provenance and agreement of parabolicity notions

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, retained file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`. The page numbers below are the
one-based PDF pages, which agree with the printed page numbers in this file.

- Corollary 5.2.8, pp. 155–156, states that the normalizer functor of any parabolic subgroup
  `P` in a reductive group scheme `G` is represented by `P`. The Lean statement is its
  specialization to `Spec k`.
- Definition 5.2.1, p. 151, defines a parabolic subgroup over a base `S` to be a smooth
  `S`-affine group `P` with a monic homomorphism to `G` and proper fiber quotients
  `G_s/P_s`. Proposition 5.2.3, p. 152, proves that this homomorphism is a closed immersion.
  Over a field, the reductive group schemes in this source are connected reductive groups.
- The discussion after Theorem 1.1.8 on p. 9 identifies parabolic subgroups over an
  algebraically closed field with closed subgroups containing a Borel subgroup, citing
  Borel, *Linear algebraic groups*, 11.2, Corollary. Theorem 1.1.9 and the following remark
  on p. 10 give the pointwise self-normalizer result (citing Borel 11.16) and announce
  Corollary 5.2.8 as its scheme-theoretic strengthening.

For a smooth closed subgroup over a field `k`, properness of the homogeneous quotient `G/P`
can be checked after the faithfully flat extension `k → AlgebraicClosure k`; the base-changed
quotient is `G_{k̄}/P_{k̄}`. Over the algebraically closed field, the quotient is
quasi-projective, so properness is equivalent to projectivity. Conrad's p. 9 criterion
therefore identifies this condition exactly with containment of a Borel subgroup after
base change to `k̄`. Conversely, such containment gives properness after base change and
hence over `k`. Thus the Library's `IsParabolicSubgroup j` agrees over a field with the
source's smooth closed subgroup with proper quotient; closedness in the source follows
from Proposition 5.2.3. This comparison explains the translation and is not a Lean proof
of an equivalence in this module.

Conrad also identifies SGA 3, Exposé XXII, Corollary 5.8.5 as a source for the general
self-normalizer result (p. 156). These secondary references are reported through Conrad.

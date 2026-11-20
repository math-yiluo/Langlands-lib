# Reducing the affine normalizer quotient to four statements

Worker 946, Task 7782.

This internal module proves
`Langlands.GroupScheme.SelfCentralizingTorusConjugacyQuotientAffineStatement`
conditionally, from four `Prop`-valued statements taken as hypotheses:

1. `TorusSubgroupModuli.SmoothAffineFiberTorusSubgroupRepresentabilityStatement`,
   a smooth parameter scheme with a universal family of closed torus subgroups.
2. `SeparatedTorusNormalizerStatement`, which gives a smooth closed normalizer
   of a closed torus.
3. `LocalCentralKernelRepresentationStatement`, which gives local finite free
   matrix representations with central kernel.
4. `SelfCentralizingQuotientAffineOfRepresentationStatement`, which says that
   any fppf quotient of `G` by the normalizer is affine, given the local
   representations.

The module adds no geometric input of its own. Its provenance is the
universal property of the torus-subgroup moduli and the Library's
smooth-relation quotient construction. It follows the published
`Langlands.GroupScheme.Torus.MaximalModuliOrbit`, which treats the affine
case with a universal family of maximal tori. The present version needs
neither affineness of `G` nor maximality of the classified tori.

## Orbit map of a closed torus

Fix a base scheme `S`, a group scheme `G` over `S`, a parameter scheme
`M : Over S` and a family `j : K ⟶ G_M` of closed torus subgroups. Here
`TorusSubgroupModuli.IsUniversal j` means that on every test scheme, every
closed relative-torus subgroup of the base-changed group is the evaluation
of `j` at a unique parameter.

- `TorusSubgroupModuli.IsUniversal.evaluate_injective` shows that evaluation
  of such a family is injective on parameters. Both parameters classify the
  same admissible subgroup functor, so uniqueness identifies them.
- `TorusSubgroupModuli.torusOrbit` classifies the conjugate family
  `SubgroupFunctor.conjugateFamily i (𝟙 G.X)` of a closed torus `i : H ⟶ G`
  by a morphism `G.X ⟶ M`. On a point `g` this family is `g H g⁻¹`.
  `evaluate_torusOrbit_id` records the defining equation.
- `evaluate_torusOrbit` shows that composing a test point `g : U ⟶ G.X`
  with the orbit map classifies the conjugate family of `g`. The proof uses
  `evaluate_comp`, `evaluate_eq_of_range_eq` and
  `SubgroupFunctor.evaluate_conjugateFamily`.
- `torusOrbit_fibers` shows that `g ≫ torusOrbit = h ≫ torusOrbit` exactly
  when `g⁻¹ * h` lies in the normalizer of `SubgroupFunctor.range i`.
  It combines injective evaluation with the published exact criterion
  `SubgroupFunctor.range_conjugateFamily_eq_iff`.

## The conditional theorem

`selfCentralizingTorusConjugacyQuotientAffine_of` takes the four statements
above as hypotheses and proves the target statement. Assume the target's
hypotheses on `G` and on `t : T.toGrp ⟶ G`.

1. Statement 1 applies, because the residue-field fibres are affine. It gives
   a universal family `j` of closed torus subgroups. The orbit map
   `r := torusOrbit j huni t hT ht : G.X ⟶ M` has as fibres exactly the
   cosets of `torusNormalizer t`, which is the normalizer of the range of `t`.
2. Statement 2 gives a smooth group scheme `N` and a monomorphism
   `n : N ⟶ G` whose range is `torusNormalizer t`.
3. The Library's right-coset relation of `n`
   (`HomogeneousQuotientFromEmbedding.arrowSpace n`, with `source` and
   `target`) is an equivalence relation with smooth projections, since `N`
   is smooth. Its sections are exactly the pairs `(x, y)` with
   `x⁻¹ * y` in the range of `n` (`relation_iff`). So the fibres of `r` are
   exactly this relation. `SmoothRelationQuotient.schemeQuotientOfMapKernel`
   then gives a scheme `Q.scheme` over `S` and a projection
   `Q.projection : G.X ⟶ Q.scheme`. The projection is smooth and
   surjective, and its fibres on every test scheme are this relation.
4. A smooth morphism is flat and locally of finite presentation, which gives
   the three properties of the projection required by the target. The
   relation fibres turn into the target's criterion
   `g⁻¹ * h ∈ (torusNormalizer t).carrier U`.
5. Statement 3 applies, because `G` is smooth, separated and quasi-compact
   and the residue-field fibres are connected. It gives the local
   representations. With these, statement 4 applied to
   `(Q.scheme, Q.projection)` shows that `Q.scheme` is affine over `S`.

The witness of the target is therefore `Q.scheme` with `Q.projection`. The
theorem does not prove any of the four statements. They are proved
separately: statement 1 in Task 7705, statement 2 in Task 7821, and
statements 3 and 4 in Task 7782.

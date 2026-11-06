# Case C data from a conjugator into a Lie-element centralizer

Author: Worker 1420.

This internal, derived module reduces the inner conditions of
`SemisimpleCentralizerConjugationDataStatement` (module `MaximalTorusConjugatorCaseC`) to
one predicate about a single `K`-rational Lie element. The predicate is
`HasCentralizerConjugator`. It asks for a generic conjugator that moves the torus into the
all-test centralizer of the element. The subgroup `H` of the data statement is then the
identity component of a chosen representative of that centralizer. The module assumes
nothing beyond its explicit hypotheses. It does not produce the Lie element or the
conjugator.

Throughout, `k` and `K` are fields with a `k`-algebra structure on `K`. `G` is a group
scheme over `k` with `IsAffineHom G.X.hom`, and `T₀` is a commutative group scheme over `k`.
`G_K` denotes `(GroupScheme.baseChange (algebraBaseMap k K)).obj G`. A local instance
records that `G_K` is affine over `K`, by the pullback of `G.X.hom`. In the last section,
where `G` is smooth, a second local instance records that `G_K` is smooth over `K`.

## The predicate

`HasCentralizerConjugator G j₀ Y` takes a homomorphism `j₀ : T₀ → G` and a `K`-rational
tangent vector `Y : lieKernel G_K K`. It holds when there are:

- an algebraically closed field `Ω : Type u` with a `K`-algebra structure;
- a point `c : Over.mk (algebraBaseMap K Ω) → G_K`.

These must satisfy two conditions:

1. The point of `G` over `k` corresponding to `c` under the published
   `baseChangePointsEquiv` has dense range.
2. For every scheme `V` over `K`, every `y : V → Over.mk (algebraBaseMap K Ω)` and every
   point `t` of `G_K` over `V`: if `t` lies in the base change of the all-test range of
   `j₀`, then `(y ≫ c) * t * (y ≫ c)⁻¹` lies in `(Lie.elementCentralizer G_K Y).carrier V`.

These are the two conditions of the data statement, with the all-test range of `i` replaced
by the published all-test centralizer `Lie.elementCentralizer G_K Y`.

## Conjugating into the identity component

`conj_mem_range_identityComponent_of_mem_elementCentralizer` assumes:

- `j₀` is a maximal torus;
- `G_K` is locally of finite type over `K`;
- the chosen centralizer representative `C = Lie.elementCentralizerGroup G_K Y` is smooth
  over `K`;
- `c` satisfies condition 2 above, for some field `Ω` over `K`.

It concludes that, under the same membership hypothesis on `t`,
`(y ≫ c) * t * (y ≫ c)⁻¹` lies in the all-test range of
`identityComponentι C ≫ Lie.elementCentralizerGroupι G_K Y`. The field `Ω` need not be
algebraically closed here.

The proof applies condition 2 to one universal point. Write `T₀K` for the base change of
`T₀` to `K` and `β = algebraBaseMap K Ω`. Let `P` be the pullback of `T₀K → Spec K` along
`β`, viewed as a scheme over `K`, with projections `pr₁ : P → T₀K` and `pr₂ : P → Spec Ω`.

1. The published `SubgroupFunctor.range_baseChangeHom` identifies the base change of the
   range of `j₀` with the range of the base-changed homomorphism `j₀K`.
2. Condition 2 at `V = P`, `y = pr₂` and `t = pr₁ ≫ j₀K` gives `f`, the conjugate of
   `pr₁ ≫ j₀K` by `pr₂ ≫ c`, in the centralizer.
3. Because `Lie.elementCentralizerGroupι` represents the centralizer, `f` factors as
   `f' ≫ Lie.elementCentralizerGroupι G_K Y` for some `f' : P → C`.
4. `P` is connected. A maximal torus is smooth, connected and affine; affineness comes from
   the published `HomogeneousQuotient.affine_subgroup_of_closed`. The published
   `GroupScheme.connectedSpace_baseChange_of_smooth_affine` applies twice: first along
   `k → K`, then along `K → Ω`.
5. The section `a : Spec Ω → P` with coordinates `(1, id)` satisfies `a ≫ f = 1`, so
   `a ≫ f' = 1` because the inclusion is a monomorphism. The image of `f'` is connected and
   contains the identity point. By `IdentityComponent.range_identityComponentι` it lies in
   the range of `identityComponentι C`.
6. `FiniteEtaleImage.liftOver` factors `f'` through `identityComponentι C`, since that map
   is an open immersion.
7. A given `t` in the range of `j₀K` has the form `s ≫ j₀K`. The pair `(s, y)` defines
   `l : V → P` with `l ≫ pr₁ = s` and `l ≫ pr₂ = y`. Then `l` composed with the lift of `f'`
   witnesses the claimed membership.

## The conjugation data

`conjugationData_of_hasCentralizerConjugator` assumes:

- `G` is smooth over `k` and its underlying space is connected;
- `j₀` is a maximal torus;
- `Y : lieKernel G_K K` has smooth chosen centralizer representative;
- `Lie.elementCentralizerLie G_K Y ≠ ⊤`;
- `HasCentralizerConjugator G j₀ Y` holds.

It concludes the inner existential of `SemisimpleCentralizerConjugationDataStatement`: the
part after the choice of `K` and the condition `ReducesRationalFunctionFields`. The
witnesses are:

- `H = identityComponent C`. It is smooth, affine and connected by the published instances
  for identity components.
- `i = identityComponentι C ≫ Lie.elementCentralizerGroupι G_K Y`. This is a closed subgroup
  by `IdentityComponent.isClosedSubgroup_identityComponentι`,
  `Lie.isClosedSubgroup_elementCentralizerGroupι` and `IsClosedSubgroup.comp`.
- `Ω` and `c` are taken from the predicate. The density condition is copied, and the
  conjugation condition comes from the previous theorem.

For the dimension bound, `G_K` is connected by
`GroupScheme.connectedSpace_baseChange_of_smooth_affine`. Since `Lie.elementCentralizerLie`
is by definition the tangent submodule of `Lie.elementCentralizer`, the published
`Lie.dimension_identityComponent_lt_of_lie_ne_top` gives
`Lie.dimension H < Lie.dimension G_K`. The published
`SubgroupProductOrbit.lie_dimension_baseChange` identifies `Lie.dimension G_K` with
`Lie.dimension G`.

## Intended use

In the intended application, `K` is the function field of the Lie algebra of `G`, and `Y` is
a prime power of the generic Lie element; in characteristic zero, `Y` is the generic element
itself. The conjugator is to be built from the published generic-conjugation results and the
Lie-centralizer statements of `Lie/TorusLieCentralizerStatements`. The
`Lie.elementCentralizerLie G_K Y ≠ ⊤` condition comes from the noncentral semisimple
element of `G`, and smoothness of the centralizer from semisimplicity of `Y` (Cartier's
theorem in characteristic zero). Those steps are not part of this module.

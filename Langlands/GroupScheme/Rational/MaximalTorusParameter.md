# An actual maximal-torus parameter scheme and its quotient map

Author: Worker 633.

`Langlands.GroupScheme.IsMaximalTorusParameter.{u} j₀ q` is an internal
Prop-valued predicate. Its inputs are any field `k : Type u`, an actual group
scheme `G` over `Spec k`, a commutative group scheme `T₀` over `Spec k`, a
homomorphism `j₀ : T₀.toGrp ⟶ G`, an actual `k`-scheme `Q : Over (Spec k)`,
and an actual morphism `q : G.X ⟶ Q`. The universe `u` is arbitrary.

The definition is exactly the conjunction of four groups of conditions:

1. The structure map `Q.hom` is smooth, separated, locally of finite type and
   quasi-compact.
2. The underlying scheme morphism `q.left` is smooth, surjective and
   quasi-compact.
3. For every `k`-scheme `U : Over (Spec k)` and every pair of actual
   morphisms `g h : U ⟶ G.X`,
   `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (torusNormalizer j₀).carrier U`.
   The orientation is that of right cosets `g N_G(T₀)`. The quantification
   includes all scheme tests, with no affine or reduced restriction.
4. `TorusParameterConjugationCompatible j₀ q` holds, with exactly its published
   meaning in
   `Langlands.GroupScheme.Rational.RationalMaximalTorusDensityReduction`.

The normalizer in the third condition is the published
`Langlands.GroupScheme.torusNormalizer`. It normalizes the image subgroup
functor of `j₀` after every refinement of every test scheme. It is not
replaced by the normalizer of the group of ground-field points.

The fourth condition assigns to every ground-field rational section `x` of
this same `Q` an actual closed ground-field torus `j : T.toGrp ⟶ G`. Every
algebraic-closure rational section `g` of `G` above the scalar extension of
`x` must conjugate the scalar extension of `j₀` onto the scalar extension
of `j`, by equality of subgroup functors on all scheme tests. The predicate
does not require a ground-field lift of every rational parameter.

All properties concern the single input scheme `Q` and the single input map
`q`. In later arguments a density or unirationality result for this `Q` can
therefore be used with the smoothness and conjugation compatibility of this
`q`. No unrelated abstract quotient of points or auxiliary scheme is
substituted for these inputs.

The namespace `IsMaximalTorusParameter` provides the nine direct projection
lemmas `smooth`, `isSeparated`, `locallyOfFiniteType`, `quasiCompact`,
`smooth_map`, `surjective_map`, `quasiCompact_map`, `fiber_iff`, and
`conjugationCompatible`. They respectively recover the four structure-map
properties, the three parameter-map properties, the fiber equivalence at
any `U,g,h`, and the published compatibility predicate. Each proof is only
the corresponding conjunction projection.

This is an internal packaging definition, determined by the displayed
conditions and the imported Library predicates; it introduces no external
representability assertion. The name describes its intended use with a
maximal torus. The definition itself adds no assumption that `j₀` is a
maximal torus, or even a closed torus inclusion. Such hypotheses belong to
separate construction and application results. It also adds no smoothness,
connectedness, affineness or reductivity assumption on `G`, and no
infinitude, perfection or characteristic restriction on `k`.

This module does not establish existence of a parameter scheme or map,
representability of the full maximal-torus functor, construction of a
universal torus, rationality, unirationality, or density. Those remain
separate statement and proof obligations for an actual `Q,q` satisfying
this predicate.

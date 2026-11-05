# Transferring generic torus conjugators along field extensions

Author: Worker 1420.

This internal, derived module transports the predicate
`HasGenericTorusConjugator` of `MaximalTorusGenericConjugator` from a base
change of a group to the original group. The fields `k K : Type u` are
arbitrary; there is no infinitude, perfection or characteristic assumption.

The imported `SubgroupFunctor.normalizer_le_baseChange` from
`SubgroupFunctor/NormalizerBaseChange` holds for any morphism of base
schemes `b : S' → S` and any subgroup functor `F` of a group scheme `G` over
`S`. It states `(F.baseChange b).normalizer ≤ F.normalizer.baseChange b`.
Let `x` be a point of the base change over a test scheme `T` over `S'`, and
suppose `x` normalizes `F.baseChange b` after every refinement over `S'`.
Then the corresponding point of `G` over `T`, viewed over `S` through `b`,
normalizes `F` after every refinement over `S`. The proof gives a refinement
`a : V → T` over `S` the structure `V' = (V, a ≫ T.hom)` over `S'`. It
compares `V` with the image of `V'` over `S` through an isomorphism whose
underlying scheme map is the identity. Then it uses the multiplicative,
natural pullback points equivalence `baseChangePointsEquiv`.

`ReducesRationalFunctionFields b` is defined for a morphism
`b : Spec K → Spec k`. For every finite `n : Type u` there are a finite
`n' : Type u` and an isomorphism over `Spec k` between
`rationalFunctionFieldOver K n` (regarded over `k` through `b`) and
`rationalFunctionFieldOver k n'`. For `K` the function field of a
finite-dimensional affine space over `k`, such isomorphisms come from the
identification of iterated rational function fields. This module does not
prove that instance.

`HasGenericTorusConjugator.of_baseChange` assumes `ReducesRationalFunctionFields b`
and a torus homomorphism `j : T → G_K` into the base change
`G_K = (GroupScheme.baseChange b).obj G`. Its all-test range must equal the
base change of the range of `j₀`, as for `j` the base change of `j₀` by the
published `range_baseChangeHom`. From a generic conjugator `(n, X', π', g')`
for `j` it builds one for `j₀`:

- The source is `X'` regarded over `k`. The map to the rational function field
  is `π'` followed by the given isomorphism onto
  `rationalFunctionFieldOver k n'`, so it stays flat, surjective and
  quasi-compact.
- The point is the image of `g'` under `baseChangePointsEquiv`, whose underlying
  morphism is `g'` followed by the projection `G_K → G`. That projection is
  surjective because `Spec K → Spec k` is (`Scheme.Pullback.range_fst`), so the
  point has dense range.
- Descent: two test points `a₁, a₂` over `k` that agree after the new map agree
  after `π'` (cancel the isomorphism). They therefore define two points over
  `K` of the test scheme with its `K`-structure through `a₁`. The descent
  condition for `g'` places their quotient in the normalizer of the range of
  `j`, which is the normalizer of the base-changed range of `j₀`. The
  imported containment and naturality of `baseChangePointsEquiv` turn this into the
  descent condition for `j₀`.

Provenance: derived from the helper module `MaximalTorusGenericConjugator`, the
published `SubgroupFunctor.baseChange`, `range_baseChangeHom` and
`baseChangePointsEquiv` with its naturality, and pinned Mathlib fiber products of
schemes. This transfer is used to reduce the generic conjugator statement over
arbitrary fields, including finite fields, to fields of the form `k(t)`. It is
also the field-change step of the dimension induction modeled on SGA 3,
Exposé XIV, Théorème 6.1. No literature statement is formalized.

# The two cases of the maximal-torus conjugator reduction

Author: Worker 1420.

This internal, derived module splits `MaximalTorusConjugatorReductionStatement`
of `MaximalTorusGenericConjugatorInduction` into two statements that can be
proved independently. It proves that together they imply the reduction
statement, and hence the target `MaximalTorusParameterUnirationalStatement`.
It also proves a helper for the density condition of the second case. The
fields `k K : Type u` are arbitrary; there is no infinitude, perfection or
characteristic assumption. Neither case statement is proved here.

## Density for translates

`isTorusConjugatorTransfer_of_translate` takes `b : Spec K → Spec k`, torus
homomorphisms `j₀ : T₀ → G` over `k` and `j : T → H` over `K`, a homomorphism
`i : H → G_K` into the base change `G_K = (GroupScheme.baseChange b).obj G`,
and a scheme `Y` over `K` whose structure morphism is flat, surjective and
quasi-compact. Let `h₁ : Y → H` and `c : Y → G_K` be points, and put
`p = (h₁ ≫ i) * c`, the pointwise product of `i(h₁)` and `c`. Assume that `p`
satisfies the conjugation condition of `IsTorusConjugatorTransfer`, and that
`c`, regarded as a point of `G` over `k` through the published
`baseChangePointsEquiv`, has dense range. Then
`IsTorusConjugatorTransfer b j₀ j i Y p` holds.

The proof only has to supply the density condition, for the map
`(h, y) ↦ i(h) · p(y)` from the fiber product `H ×_K Y` to `G`. The section
`s : Y → H ×_K Y`, `y ↦ (h₁(y)⁻¹, y)`, built with `pullback.lift`, satisfies
`s ≫ m = c` for this map `m`. The proof uses that `i` is a monoid
homomorphism on points (`IsMonHom.monoidHom`) and `inv_mul_cancel_left`.
Naturality of `baseChangePointsEquiv` then puts the range of `c` inside the
range of `m`, so the range of `m` is dense.

## The cases

`HasNoncentralGeometricSemisimpleElement G` is defined for a group scheme `G`
over `k` with affine structure morphism. Let `Gbar` be its base change along
`toAlgebraicClosure k`. The predicate says that some
`X : lieKernel Gbar (AlgebraicClosure k)` satisfies
`Lie.IsSemisimpleElement Gbar X` and `Lie.elementCentralizerLie Gbar X ≠ ⊤`.
This is the second alternative of the published
`SemisimpleIsogenyReductionStatement`, with the same affineness instance on
`Gbar`.

`HasSmallerTorusConjugatorReduction.mono`: a reduction below `d` is a
reduction below every `d' ≥ d`.

`MaximalTorusIsogenyReductionStatement.{u}` (Case B) quantifies over a field
`k : Type u` and a group scheme `G` over `k` that is smooth and affine with
connected underlying space. It also quantifies over a commutative group scheme
`T₀` and a homomorphism `j₀ : T₀ → G` with `IsMaximalTorus j₀`. It asserts
that there are:

- a group scheme `G'` over `k` that is smooth and affine with connected
  underlying space;
- a commutative group scheme `T₀'` and `j₀' : T₀' → G'` with
  `IsMaximalTorus j₀'`;
- a homomorphism `φ : G → G'` whose underlying scheme morphism is flat,
  surjective, quasi-compact and universally open, with
  `ReflectsTorusNormalizer φ j₀ j₀'`;

such that `Lie.dimension G' ≤ Lie.dimension G`, and either every point of `G'`
over every test scheme lies in `torusNormalizer j₀'`, or
`HasNoncentralGeometricSemisimpleElement G'` holds.

`SemisimpleCentralizerConjugatorReductionStatement.{u}` (Case C) quantifies over
the same data `k`, `G`, `T₀`, `j₀` with `IsMaximalTorus j₀`. It asserts that
`HasNoncentralGeometricSemisimpleElement G` implies
`HasSmallerTorusConjugatorReduction j₀ (Lie.dimension G)`.

`maximalTorusConjugatorReduction_of_cases` proves that the two statements imply
`MaximalTorusConjugatorReductionStatement.{u}`. Take the data of Case B. In
its first alternative the first alternative of the reduction statement holds.
In the second, Case C for `G'` and `j₀'` gives a reduction below
`Lie.dimension G'`, and `mono` turns it into one below `Lie.dimension G`.
`maximalTorusParameterUnirational_of_cases` composes this with
`maximalTorusParameterUnirational_of_reduction`. It proves that the two
statements imply `MaximalTorusParameterUnirationalStatement.{u}`.

## Intended proofs (not part of this module)

These remarks explain the design. They are not claims of the Lean module.

- Case B: the published proof of `SemisimpleIsogenyReductionStatement` builds
  `G'` by composing central isogenies. A proof of Case B is expected to follow
  that construction, carrying along at each step the image torus and the
  reflection of torus normalizers. Reflection holds for a central isogeny with
  kernel of multiplicative type, and composes. The nilpotent alternative gives
  a central maximal torus (the published `nilpotentCentralTorus`), hence the
  first alternative. The published statement alone is not enough, because it
  does not say that the composite isogeny reflects normalizers.
- Case C: take `K` the function field of the Lie algebra, viewed as an affine
  space over `k`, and `X` the generic Lie element over `K`. Let `H` be the
  identity component of the centralizer of `X^[p^r]`, which has smaller Lie
  dimension. Take `j` a maximal torus of `H` (the published
  `maximalTorusExistence`), and `c` a generic conjugator that moves `T₀` into
  `H` over a field. Then `h₁` comes from conjugacy of maximal tori over an
  algebraically closed field, and `isTorusConjugatorTransfer_of_translate`
  supplies the transfer data. `ReducesRationalFunctionFields` holds by
  `reducesRationalFunctionFields_rationalFunctionFieldOver` of
  `MaximalTorusGenericConjugatorInduction`.

## Provenance

Derived from the helper modules `MaximalTorusGenericConjugatorInduction` and
`MaximalTorusGenericConjugatorLift`, from the published
`SemisimpleIsogenyReductionStatement` (for the shape of the geometric
semisimple alternative), `baseChangePointsEquiv` with its naturality, and pinned
Mathlib fiber products. The case split is an internal reformulation of the
dimension induction modeled on SGA 3, Exposé XIV, Théorème 6.1, adapted to
positive characteristic by central isogenies. No literature statement is
formalized.

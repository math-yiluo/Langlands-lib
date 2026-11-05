# Induction on the Lie dimension for generic torus conjugators

Author: Worker 1420.

This internal, derived module reduces the generic conjugator statement
`MaximalTorusGenericConjugatorStatement` of `MaximalTorusGenericConjugator`,
and with it the target `MaximalTorusParameterUnirationalStatement`, to one
structural statement, `MaximalTorusConjugatorReductionStatement`. The
reduction is a strong induction on the Lie dimension that runs over all fields
at once. The fields `k K : Type u` are arbitrary; there is no infinitude,
perfection or characteristic assumption. The module does not prove the
structural statement.

## Rational function fields over a rational function field

`reducesRationalFunctionFields_rationalFunctionFieldOver k m` takes a finite
`m : Type u`. Let `K` be the function field of `𝔸(m; Spec k)` and let
`b : Spec K → Spec k` be the structure morphism of
`rationalFunctionFieldOver k m`. Then `ReducesRationalFunctionFields b` holds:
for every finite `n`, the rational function field over `K` in `n` variables,
regarded over `k` through `b`, is isomorphic over `k` to
`rationalFunctionFieldOver k (m ⊕ n)`. The isomorphism is the published
`iteratedFunctionFieldOverIso m n (Spec k)`, preceded by an isomorphism whose
underlying scheme map is the identity; it only reassociates the structure
morphism.

## Two normalizer lemmas

- `SubgroupFunctor.inv_mul_mul_mem_normalizer`: let `F, F'` be subgroup
  functors of a group scheme `G` over `S`, and let `P₁, P₂, N` be points of `G`
  over `U`. Suppose that for each `i` and every refinement `a : V → U`, a point
  `t` over `V` lies in `F` exactly when `(a ≫ Pᵢ) t (a ≫ Pᵢ)⁻¹` lies in `F'`.
  If `N` normalizes `F'`, then `P₁⁻¹ N P₂` normalizes `F`.
- `SubgroupFunctor.comp_mem_normalizer_range`: for homomorphisms
  `j : K → H` and `i : H → G`, a point `x` of `H` normalizing the range of `j`
  has image `x ≫ i` normalizing the range of `j ≫ i`. The proof applies the
  points monoid homomorphism of `i` (`IsMonHom.monoidHom`) to the two
  conjugation equations.

## Transfer data

`IsTorusConjugatorTransfer b j₀ j i Y p` is defined for:

- `b : Spec K → Spec k`, a torus homomorphism `j₀ : T₀ → G` over `k`;
- a torus homomorphism `j : T → H` over `K` and a homomorphism
  `i : H → G_K` into the base change `G_K = (GroupScheme.baseChange b).obj G`;
- a scheme `Y` over `K` and a point `p : Y → G_K`.

It is the conjunction of:

1. `Y → Spec K` is flat, surjective and quasi-compact;
2. for every scheme `V` over `K`, every `y : V → Y` and every point `t` of
   `G_K` over `V`, the point `t` lies in the base change of the all-test range
   of `j₀` exactly when `(y ≫ p) t (y ≫ p)⁻¹` lies in the all-test range of
   `j ≫ i`; that is, `p` conjugates the base-changed torus onto the torus
   `j ≫ i` over every test scheme;
3. the morphism `H ×_K Y → G` over `k`, sending `(h, y)` to `i(h) · p(y)` and
   then projecting from `G_K` to `G`, has dense range. It is the image under
   `baseChangePointsEquiv` of the product of the two points over the fiber
   product `H ×_K Y`, regarded over `K` through `Y`. Density is asked in `G`
   over `k`, not in `G_K`.

`HasGenericTorusConjugator.of_transfer` assumes `ReducesRationalFunctionFields b`
and transfer data. From a generic conjugator `(n, X', π', g')` for `j` it builds
one for `j₀`:

- Over `K`, the source is the fiber product `X₂ = X' ×_K Y`. The map to the
  rational function field is the first projection followed by `π'`, and the
  point is `g₂ = i(g' ∘ pr₁) · p(pr₂)` in `G_K`.
- Over `k`, the source is `X₂` regarded over `k` through `b`. The map is the
  image of the previous map, followed by the isomorphism onto
  `rationalFunctionFieldOver k n'` given by `ReducesRationalFunctionFields b`.
  The point is the image of `g₂` under `baseChangePointsEquiv`.
- The new map is flat, surjective and quasi-compact: the first projection is a
  base change of `Y → Spec K`, and its range is everything by
  `Scheme.Pullback.range_fst`.
- Descent over `K`: suppose two test points of `X₂` agree after the map to the
  rational function field. Their images in `X'` agree after `π'`. The descent
  condition for `g'` and `comp_mem_normalizer_range` put the image under `i`
  of the quotient of their `g'`-values in the normalizer of the range of
  `j ≫ i`. `inv_mul_mul_mem_normalizer`, with `P₁, P₂` the values of `p` and
  condition 2, puts the quotient of their `g₂`-values in the normalizer of the
  base-changed range of `j₀`.
- Descent over `k`: suppose two test points `a₁, a₂` over `k` agree after the
  new map. Cancelling the isomorphism, they define two points over `K` of the
  test scheme with its `K`-structure through `a₁`. The descent over `K` applies
  to them. The published `SubgroupFunctor.normalizer_le_baseChange` and the
  naturality of `baseChangePointsEquiv` give the descent condition for `j₀`.
- Density: the point factors as `X₂ → H ×_K Y → G`, where the first map is
  `g' × id` over `Y`. Its range is the preimage of the range of `g'` under the
  first projection (`Scheme.Pullback.range_map`). That range is dense because
  `g'` has dense range and the projection is open. Condition 3 and continuity
  give dense range.

## The reduction statement and the induction

`HasSmallerTorusConjugatorReduction j₀ d` is defined for a torus homomorphism
`j₀ : T₀ → G` over `k` and `d : ℕ`. It says there are:

- a field `K : Type u` and `b : Spec K → Spec k` with
  `ReducesRationalFunctionFields b`;
- a group scheme `H` over `K` that is smooth and affine with connected
  underlying space, with `Lie.dimension H < d`;
- a torus homomorphism `j : T → H` with `IsMaximalTorus j`, a homomorphism
  `i : H → G_K`, a scheme `Y` over `K` and a point `p : Y → G_K` with
  `IsTorusConjugatorTransfer b j₀ j i Y p`.

`HasSmallerTorusConjugatorReduction.hasGenericTorusConjugator` gives a generic
conjugator for `j₀` from such a reduction. It also assumes that every maximal
torus of every smooth affine connected group of Lie dimension below `d`, over
every field, has a generic conjugator.

`MaximalTorusConjugatorReductionStatement.{u}` quantifies over a field
`k : Type u` and a group scheme `G` over `k` that is smooth and affine with
connected underlying space. It also quantifies over a commutative group scheme
`T₀` and a homomorphism `j₀ : T₀ → G` with `IsMaximalTorus j₀`. It asserts
that there are a group scheme `G'` over `k` with flat, quasi-compact structure
morphism, a torus homomorphism `j₀' : T₀' → G'` and a homomorphism
`φ : G → G'` such that:

- the underlying scheme morphism of `φ` is flat, surjective, quasi-compact and
  universally open;
- `ReflectsTorusNormalizer φ j₀ j₀'` holds;
- either every point of `G'` over every test scheme lies in the torus
  normalizer of `j₀'`, or `HasSmallerTorusConjugatorReduction j₀' d` holds
  with `d = Lie.dimension G`.

`maximalTorusGenericConjugator_of_reduction` proves that this statement
implies `MaximalTorusGenericConjugatorStatement.{u}`. It uses strong induction
on `d`. The claim at `d` is that every maximal torus of every smooth affine
connected group of Lie dimension `d`, over every field `k : Type u`, has a
generic conjugator. Take the data of the statement. In the first case the
published `hasGenericTorusConjugator_of_normalizer_eq_top` gives a generic
conjugator for `j₀'`. In the second case the induction hypothesis and
`hasGenericTorusConjugator` give one. In both cases
`HasGenericTorusConjugator.of_hom` lifts it along `φ` to `j₀`.
`maximalTorusParameterUnirational_of_reduction` composes this with the
published `maximalTorusParameterUnirational_of_genericConjugator`. It proves
that `MaximalTorusConjugatorReductionStatement.{u}` implies the target
`MaximalTorusParameterUnirationalStatement.{u}`.

## Provenance

The module is derived from the helper modules `MaximalTorusGenericConjugator`,
`MaximalTorusGenericConjugatorLift` and `MaximalTorusGenericConjugatorBaseChange`.
It also uses the published `iteratedFunctionFieldOverIso`,
`SubgroupFunctor.baseChange`, `SubgroupFunctor.normalizer_le_baseChange`,
`baseChangePointsEquiv` with its naturality, `Lie.dimension`, and pinned
Mathlib fiber products of schemes (`Scheme.Pullback.range_fst`,
`Scheme.Pullback.range_map`).

The induction is modeled on the proof of SGA 3, Exposé XIV, Théorème 6.1, in
which the variety of maximal tori is shown to be unirational by induction on
the dimension, through centralizers of generic elements of the Lie algebra.
The two alternatives of the reduction statement are internal
reformulations. The first is the case of a torus normalized by every point.
The second is the case of a generic semisimple centralizer of smaller
dimension. The homomorphism `φ` covers the central isogenies needed in
positive characteristic. No literature statement is formalized, and the
reduction statement itself is not claimed from the literature.

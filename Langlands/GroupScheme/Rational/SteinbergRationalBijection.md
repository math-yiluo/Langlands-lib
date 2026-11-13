# The Steinberg cross-section on rational points, and ascent of quotient equalities

This module imports `Langlands.GroupScheme.Rational.SplitSteinbergQuotient` (Steinberg's
cross-section isomorphism, Steinberg 1965, Theorem 7.9) and
`Langlands.GroupScheme.Rational.EvenChainFieldBaseChange` (class functions under field
extension). It is an internal prerequisite of the split even-path cross-section task
(`Langlands.GroupScheme.SplitEvenChainCrossSectionStatement`, Steinberg 1965, §9.15–9.19).

**Provenance: internal.** These are small consequences of Library results, derived for this
project: the rational-point form of the Library's Steinberg isomorphism, and the ascent of an
equality in the canonical quotient along a field extension. Every result is stated below and
proved in Lean.

## Setting

`k` is a field and `G` a group scheme over `Spec k` with affine structure morphism. The
canonical class quotient map is `ClassFunctions.rho G`. A rational point is a morphism from
`Over.mk (𝟙 (Spec k))`; `rationalPoints G` is the group of rational points of `G`.

## Definition

- `SplitPinning.steinbergClassMap E x n cf` (for a split pinning `p`, an ordering
  `E : Fin r ≃ p.base.support`, a family `x` of normalized simple root parametrizations, a
  family `n` of simple reflection representatives and `cf : Fin r → k`) is the rational point
  of the canonical quotient
  `(List.ofFn fun j => x_(E j)(cf j) · n_(E j)).prod ≫ ClassFunctions.rho G`,
  where `x_(E j)(c)` is `(x (E j)).toRootParametrization.rationalPoint c` and `n_(E j)` is
  `(n (E j)).point`. The product is taken in increasing `j`, that is
  `x_(E 0)(cf 0) n_(E 0) · x_(E 1)(cf 1) n_(E 1) ⋯`.

## Results

- `SplitPinning.steinbergProductPoint_rational`: the Library's global-function Steinberg
  product `steinbergProductPoint E x n` at the base test object, evaluated at the constant
  functions `ΓSpecIso.inv (cf j)`, equals the product of rational points above.
- `SplitPinning.bijective_steinbergClassMap` (**Steinberg's cross-section on rational
  points**): if `G` is simply connected, then `steinbergClassMap E x n : (Fin r → k) →
  (rational points of the quotient)` is bijective. Proof: the Library theorem
  `splitSteinbergQuotient` says `steinbergProduct E x n ≫ ClassFunctions.rho G` is an
  isomorphism, so composition with it is a bijection on rational points; the rational points
  of the vector group are `Fin r → Γ(Spec k)` by `VectorGroup.coordinates`, which is `k^r`
  by `ΓSpecIso`; the Library lemma `coordinatesPoint_comp_steinbergProduct` and
  `steinbergProductPoint_rational` identify the composite with `steinbergClassMap`.
- `SplitPinning.charpoly_rationalMatrix_eq_of_rho_eq`: if two rational points `g, g'` of a
  group scheme `H` over `k` have the same image under `ClassFunctions.rho H`, then for every
  matrix representation `ρ` of `H`, the matrices `ρ.rationalMatrix g` and
  `ρ.rationalMatrix g'` have the same characteristic polynomial. Proof: each coefficient is the
  class evaluation of the Library class function `charpolyCoeffClassFunction`
  (`classEvaluation_charpolyCoeffClassFunction`), and class evaluations agree on points with
  the same image (`classEvaluation_eq_of_rho_eq`).
- `SplitPinning.FundamentalRepresentation.exists_pathWeightSpace_ne_zero`: for a path
  component `β : Fin L → p.base.support` and a fundamental representation `F` at the first
  vertex `β 0`, the weight space of `F.representation` at
  `pathWeight β F.highestWeight 0` (which is the highest weight) has a nonzero vector, since
  that weight space has dimension `1` (part of `F.isHighestWeight`).
- `baseChangeBasePoint_rho_eq_of_rho_eq` (**ascent**): let `F` be a field extension of `k`,
  `bc = algebraBaseMap k F`, and `GF` the base change of `G` along `bc`. If two rational points
  `g, g'` of `G` satisfy `g ≫ ρ_G = g' ≫ ρ_G` (with `ρ_G = ClassFunctions.rho G`), then their
  base changes satisfy `baseChangeBasePoint bc G g ≫ ρ_GF = baseChangeBasePoint bc G g' ≫ ρ_GF`.
  Proof: by the Library lemma `SplitPinning.rho_eq_of_classEvaluation_eq` it suffices that every
  class function `f` of `GF` takes the same value at the two points. The Library equivalence
  `ClassFunctions.BaseChange.invariants k F G : F ⊗[k] (class functions of G) ≃ₐ[F]
  (class functions of GF)` is surjective, so `f` is the image of a tensor; by induction on
  tensors it suffices to treat `a ⊗ f₀`, whose image is `a • fieldExtension f₀`, and
  `classEvaluation_baseChangeBasePoint` reduces this to the equality of the class evaluations
  of `f₀` at `g` and `g'`, which holds by `classEvaluation_eq_of_rho_eq`.

## Rational-product interface

Let `k` be a field, `G` an affine group scheme over `Spec k` with a supplied split pinning `p`, `E : Fin r ≃ p.base.support` an ordering of the simple roots, `x` a family of supplied normalized simple-root maps and `n` a family of supplied simple-reflection representatives (any family, not only the canonical one).

`rationalSteinbergProduct E x n c`, for `c : Fin r → k`, is the rational point

`(x (E 0))(c 0) · n (E 0) · (x (E 1))(c 1) · n (E 1) · ... · (x (E (r-1)))(c (r-1)) · n (E (r-1))`,

the product in increasing `Fin r` order. Here `(x a)(c)` is `(x a).toRootParametrization.rationalPoint c`, the root point with standard additive coordinate `c`, and `n a` is the rational point `(n a).point`. `rationalSteinbergProduct_eq` unfolds it to this `List.ofFn` product, by definition.

With `k`, `G`, `p`, `E`, `x` and `n` as in the definition:

- `steinbergProductPoint_rational E x n c`: the published ordered product `steinbergProductPoint E x n` evaluated at the base test `Over.mk (𝟙 (Spec k))`, at the global functions `(Scheme.ΓSpecIso k).inv (c j)`, is the `List.ofFn` product above.
- `steinbergProductPoint_eq_rationalSteinbergProduct E x n c`: the same equality with right-hand side `rationalSteinbergProduct E x n c`.
- `bijective_steinbergProductPoint_rho E x n hG`: if `G` is simply connected, the map `k ^ r → (rational points of the class quotient)` sending `c` to `steinbergProductPoint E x n (Over.mk (𝟙 _)) (fun j => (Scheme.ΓSpecIso k).inv (c j)) ≫ rho G` is bijective.
- `bijective_rationalSteinbergProduct_rho E x n hG`: if `G` is simply connected, `c ↦ rationalSteinbergProduct E x n c ≫ rho G` is a bijection from `k ^ r` onto the rational points of `ClassFunctions.quotient G`.

`bijective_steinbergProductPoint_rho` uses the published Steinberg cross-section isomorphism `splitSteinbergQuotient` (Steinberg 1965, Theorem 7.9): `steinbergProduct E x n ≫ rho G` is an isomorphism of schemes over `Spec k` from the standard affine `r`-space. The map in question is the composite of three bijections. The first is `c ↦ ((Scheme.ΓSpecIso k).inv (c j))_j`, coordinatewise the inverse of the ring isomorphism `Γ(Spec k, ⊤) ≅ k`. The second is the inverse of the published coordinate equivalence `VectorGroup.coordinates k r (Over.mk (𝟙 _))` between rational points of affine `r`-space and `r`-tuples of global functions, after `Multiplicative.ofAdd`. The third is postcomposition with the isomorphism `steinbergProduct E x n ≫ rho G`. The published `coordinatesPoint_comp_steinbergProduct` identifies the composite of the first two with `steinbergProductPoint`, which gives the stated map.

`bijective_rationalSteinbergProduct_rho` rewrites the previous theorem with `steinbergProductPoint_eq_rationalSteinbergProduct`.

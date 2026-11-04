# Hopf algebras of central extensions of split tori by split tori

Worker 1395 wrote this module. It is the algebraic core of the proof of
[`CentralTorusExtensionStatement`](../GroupScheme/Torus/CentralExtensionProof.md).
Let `K` be a field and `A` a commutative `K`-Hopf algebra with bialgebra maps
`φ : K[ℤ^I] →ₐc A` and `π : A →ₐc K[ℤ^J]`. Geometrically, `Spec A = E`, `Spec φ` is
a quotient map `E → T` onto the split torus `𝔾_m^I`, and `Spec π` is a central
closed subgroup `Z = 𝔾_m^J` of `E` with `T = E/Z`. Under these hypotheses the
module proves that the group-like elements of `A` span `A` and form a group
isomorphic to `ℤ^(I ⊕ J)`. Hence `E` is a split torus. The grading of `A` by
`ℤ^J` comes from
[`GroupAlgebraCoaction`](GroupAlgebraCoaction.md).

## Source and route

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
proves the corresponding result geometrically. By Corollary 12.22 (printed
p.239, one-based PDF p.255), a commutative extension of groups of
multiplicative type is of multiplicative type. By Corollary 12.42 (printed
p.244, one-based PDF p.260), so is a connected one; its proof uses the rigidity
Corollary 12.41, which the author's errata correct to require a central kernel. By Definition 12.7 and Theorem 12.8 (printed p.233, one-based PDF p.249),
an algebraic group is diagonalizable exactly when the group-like elements of
its coordinate ring span it.

This module does not follow Milne's rigidity argument. It uses centrality
directly, through an argument in the coordinate Hopf algebra that is internal
to this project:

1. The `ℤ^J`-grading of `A` defined by `π` has degree-zero part `φ(K[ℤ^I])`.
   Each homogeneous component `A_n` is an invertible `K[ℤ^I]`-module: the
   antipode shows `A_n · A_{-n} = A_0`.
2. `K[ℤ^I]` is a unique factorization domain, so its Picard group is trivial
   ([`IntLatticeAlgebra`](IntLatticeAlgebra.md)). Hence `A_n = K[ℤ^I] · u` for
   a unit `u` of `A`.
3. Centrality gives `Δ(A_n) ⊆ A_n ⊗ A_n`, so `Δ u = (φ ⊗ φ)(f) · (u ⊗ u)` with
   `f` a unit of `K[ℤ^I] ⊗ K[ℤ^I] ≅ K[ℤ^(I ⊕ I)]`. Units of that ring are
   monomials, and the counit identities force `f = d ⊗ 1` for a scalar `d`.
   Then `d • u` is group-like.
4. Group-like elements of each degree, together with the group-like elements
   `φ(Xᵐ)`, span `A` and form a group `ℤ^I × ℤ^J`.

## Contents

* `IsCentralExtension φ π`: a structure with five fields. `φ` is injective (the
  quotient map is faithfully flat), `π` is surjective (`Z → E` is a closed
  immersion), `π ∘ φ = algebraMap ∘ ε` (`Z` lies in the kernel), `π` is
  central (`GroupAlgebraCoaction.IsCentral`), and every element of degree `0`
  lies in the image of `φ` (`T = E/Z`).
* `map_mem_grade_zero`: `φ b` has degree `0`.
* `exists_mem_grade_counit_eq_one`: if `π` is surjective, every degree `n` has
  an element `a` with `ε a = 1`. Take `proj π n` of a preimage of `Xⁿ`.
* `exists_unit_mem_grade`: for `I` finite, every component `grade π n`
  contains a unit of `A`. Regard `A` as a `K[ℤ^I]`-algebra through `φ`, and
  let `P m` be `grade π m` as a `K[ℤ^I]`-submodule. Then `P n * P (-n) = 1`. The
  inclusion `≤` holds by the `invariants` field. The inclusion `≥` holds by
  `one_mem_grade_neg_mul_grade` applied to an element of degree `-n` with
  counit one. So `P n` is a unit submodule. Its class in the Picard group is
  trivial by `IntLatticeAlgebra.subsingleton_pic`, and Mathlib's
  `Submodule.ker_unitsToPic` makes it the span of a unit `x`.
* `divide h u hu`: for a unit `u` of degree `n`, the `K`-linear map
  `A → K[ℤ^I]`, `a ↦ φ⁻¹ (proj π n a · u⁻¹)`. `mul_inv_mem_range`,
  `map_divide` and `map_divide_mul` give `φ (divide a) · u = proj π n a`.
* `map_proj_proj`, `comul_eq_map_mul`: for a unit `u` of degree `n`,
  `Δ u = (φ ⊗ φ)((divide ⊗ divide)(Δ u)) · (u ⊗ u)`. This uses
  `IsCentral.comul_of_mem`.
* `map_map_injective`: `φ ⊗ φ` is injective (flatness over a field).
* `exists_isGroupLikeElem_smul`: a unit `u` of degree `n` has a scalar multiple
  `d • u` that is group-like. Write `Δ u = (φ ⊗ φ) f · (u ⊗ u)` and
  `Δ u⁻¹ = (φ ⊗ φ) f' · (u⁻¹ ⊗ u⁻¹)`. Multiplicativity of `Δ` and injectivity
  of `φ ⊗ φ` give `f f' = 1`. Through `scalarTensorEquiv`, `f` is a unit of
  `K[ℤ^I][ℤ^I]`, so by `IntLatticeAlgebra.exists_eq_single_of_isUnit` (twice)
  `f = single m₁ d ⊗ single m₂ 1` with `d` a unit of `K`. The two counit
  identities give `(ε(u) d) • φ(X^{m₁}) u = u` and `(d ε(u)) • φ(X^{m₂}) u = u`.
  Cancelling the unit `u` and using injectivity of `φ` forces `m₁ = m₂ = 0`
  and `d ε(u) = 1`. Then `Δ u = d u ⊗ u`, so `d • u` is group-like.
* `mem_grade_of_isGroupLikeElem`, `eq_of_mem_grade`, `exists_map_eq_single`: a
  group-like `g` satisfies `π g = Xⁿ` for a unique `n`, and lies in degree `n`.
* `degree π`: the homomorphism `Additive (GroupLike K A) →+ ℤ^J`, `g ↦ n`
  with `π g = Xⁿ`. Lemmas `map_eq_single_degree`, `mem_grade_degree`,
  `degree_eq_of_mem_grade`.
* `iota φ`: the homomorphism `ℤ^I →+ Additive (GroupLike K A)`,
  `m ↦ φ(Xᵐ)`. `iota_val` and `degree_iota` (degree zero).
* `isGroupLikeElem_of_map`: if `φ b` is group-like then `b` is group-like,
  by injectivity of `φ` and of `φ ⊗ φ`.
* `exists_degree_eq`: every `n : ℤ^J` is the degree of a group-like element,
  by `exists_unit_mem_grade` and `exists_isGroupLikeElem_smul`.
* `sect h`, `degree_sect`: for finite `J`, a homomorphic section of `degree`,
  defined on the standard basis of `ℤ^J` with `Module.Basis.constr`.
* `coprod_injective`, `coprod_surjective`: `(iota φ).coprod (sect h)` is a
  bijection `ℤ^I × ℤ^J → GroupLike K A`. Surjectivity: `g - sect (degree g)`
  has degree `0`, so it equals `φ b` for some `b`. That `b` is group-like in
  `K[ℤ^I]`, hence a monomial `Xᵐ`.
* `groupLikeEquiv h : Additive (GroupLike K A) ≃+ (I ⊕ J → ℤ)` for finite `I`
  and `J`.
* `span_isGroupLikeElem h`: the group-like elements span `A` over `K`. Write `a`
  as the sum of its components `proj π n a` (`sum_proj`). Each component is
  `φ (divide a) · g` for the group-like element `g = sect h n` of degree `n`.
  Each monomial term `c φ(Xᵐ) g` is a multiple of a product of group-like
  elements.

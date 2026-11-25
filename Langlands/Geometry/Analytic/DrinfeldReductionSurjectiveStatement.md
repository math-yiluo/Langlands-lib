# The reduction map of Drinfeld's upper half space is surjective

This module states, without proof, that the reduction map
`Res : Ω → BT` of module `DrinfeldReduction` is surjective. It contains one
Prop-valued definition,
`Langlands.Analytic.DrinfeldUpperHalfSpace.ReductionSurjectiveStatement`.

## Statement

Let `F` be a non-Archimedean local field (`NontriviallyNormedField`,
`IsUltrametricDist`, `ProperSpace`). Let `K` be a complete ultrametric
nontrivially normed field with `[NormedAlgebra F K]`, and `d ≥ 1`
(`[NeZero d]`). Then every homothety class of ultrametric norms on `F^{d+1}`
(`NormClass F (Fin (d + 1) → F)`) is `reduction K z` for some point `z` of
`Omega F K d`. Here `reduction K z` is the class of the norm
`a ↦ |ℓ_a(z)|`, with `ℓ_a = a₀ + a₁ z₁ + ⋯ + a_d z_d`.

## Original source

Rémy–Thuillier–Werner, *Bruhat-Tits buildings and analytic geometry*,
registered as `remy-thuillier-werner-2012-bruhat-tits-analytic-geometry`,
SHA256 `f176a2657963c2e6da49a2e0282353097fff8ad67b7cf17f51c2372325591d0b`
(arXiv:1110.1362, PDF page = printed page).

- §2.1.2, p.17: restriction of seminorms to `S¹V = V` induces the map
  `τ : Ω → X(V,k)`; this is the Library's `reduction`.
- §2.1.3, p.18: "Let now γ be a non-trivial norm on V. By Proposition 1.20,
  there exists a basis e0, …, ed of V which is adapted to γ […]. We can
  associate to γ a multiplicative seminorm j(γ) on S•V […]. Passing to the
  quotients, we get a continuous map j : X(V,k) → Ω satisfying τ(j(α)) = α."
  So `τ` has the section `j` and is surjective.
- Proposition 1.20, p.12: "Every norm of N(V,k) admits an adapted basis in V"
  (here `k` is a local field).

## Derived choices

- RTW work over the local field `k = F` itself. The statement here is over any
  complete ultrametric extension `K` of `F`. The same construction works: for
  a basis `e₀, …, e_d` of `F^{d+1}` adapted to the norm with weights
  `exp(c_i)`, the Gauss norm `Σ a_I e^I ↦ max_I |a_I| exp(I·c)` with
  coefficients `a_I ∈ K` is a multiplicative seminorm, and its restriction to
  `F`-linear combinations of the `e_i` is the given norm.
- `Ω` is the Library's `Omega F K d`, a subset of the Berkovich affine space
  `𝔸^d_K` (the complement of the `F`-rational hyperplane at infinity contains
  `Ω`), and `X(V,k)` is the Library's `NormClass F (Fin (d + 1) → F)` of
  homothety classes of ultrametric norms on coefficient vectors.
- The hypothesis `d ≥ 1` matches `DistinguishedCoveringStatement`, whose
  nerve property needs points of `Ω` over every facet of the building.

## Use

`DistinguishedCoveringStatement` (module `DrinfeldCoveringStatement`), item 3:
a nonempty set of vertices that is a facet has a nonempty domain
`facetDomain K S ε`. The norm-theoretic part of the argument produces a norm
class in every `B(e, ε)`, `e ∈ S`, and this statement lifts it to a point of
`Ω`.

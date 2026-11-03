# Sections of homogeneous coordinates and the tangent-space measure

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. It builds on
`Langlands.Algebra.GradedHopf.Primitive` (same author) and its imports.

Provenance: internal. This module produces the data needed for one step of a split
`𝔾ₐ`-series:

- a homogeneous primitive element `g` of nonzero degree;
- a `k`-algebra map `s : A → k[X]` with `s g = X`. This is the algebraic form of a
  scheme-theoretic section `𝔾ₐ → H` of the homomorphism given by `g`; it is consumed by
  `Langlands.GroupScheme.HopfPrimitive.splitStep` (Worker 1419);
- a numerical measure (the dimension of the tangent space at the counit) that strictly
  drops under passage to the quotient by `g`.

## Augmentation in coordinates

Throughout, `A` is a commutative `k`-bialgebra with polynomial coordinates `z : σ → A`
(`hz : Function.Bijective (aeval z)`), and the counit vanishes on them
(`hz0 : ∀ i, counit (z i) = 0`). In this section and the next the index type `σ` is
arbitrary; from `epsDerEval` on it is finite (see below).

- `counit_aeval`: `counit (aeval z F) = F.coeff 0`. Both sides are `k`-algebra maps
  agreeing on the variables.
- `coordTangent_eq_coeff`: the tangent vector `ξᵢ = coordTangent hz i` (from
  `InvariantDerivation`) takes `a` to the coefficient of the linear monomial `Xᵢ` in the
  coordinate polynomial of `a`.
- `mem_sq_of_coordTangent_eq_zero`: an element `x` with `counit x = 0` and all `ξᵢ x = 0`
  lies in the square of the augmentation ideal. Its coordinate polynomial has no constant
  or linear term, so every monomial is `Xₐ Xᵦ` times a monomial, and `z a, z b` lie in the
  augmentation ideal.

## The section

`exists_algHom_polynomial_eq_X hzw hz hz0 hd hg hg0 hg2`: here `k` is a field, `𝒜` a
`ℤ`-grading of `A`, `z i ∈ 𝒜 (w i)`, and `g ∈ 𝒜 d` with `d ≠ 0`, `counit g = 0`, and `g`
not in the square of the augmentation ideal. Then there is `s : A →ₐ[k] Polynomial k` with
`s g = X`.

Proof (as implemented):

- By `mem_sq_of_coordTangent_eq_zero`, some `c = ξᵢ(g)` is nonzero. It is the coefficient
  of `Xᵢ` in the coordinate polynomial `F` of `g`.
- `F` is weighted homogeneous of weight `d` (`gradeProj_aeval`), so `w i = d`.
- `s` sends `zᵢ` to `c⁻¹ X` and every other coordinate to `0`. A monomial of `F` survives
  only if it involves `zᵢ` alone, i.e. it is `Xᵢ ^ m`. Its weight `m d` equals `d ≠ 0`,
  so `m = 1`. Hence `s g = c · c⁻¹ X = X`.

## The tangent space at the counit

- `epsDer k A : Submodule k (A →ₗ[k] k)` consists of the `ξ` with
  `ξ (a * b) = ε a * ξ b + ε b * ξ a`, where `ε` is the counit.
- `epsDer_apply_one`: such `ξ` vanish on `1`.
- `epsDer_eq_zero_of_adjoin`: such a `ξ` vanishing on a generating set is zero.
- `coordTangent_mem_epsDer`: each `ξᵢ` belongs to it (for arbitrary `σ`).

From here on the coordinate index type is finite: the Lean hypotheses are `[Fintype σ]`
and `[DecidableEq σ]` together with `hz : Function.Bijective (aeval z)` for
`z : σ → A`. This finiteness is essential. For example, for `A = ℚ[Xₙ | n ∈ ℕ]` with all
variables primitive, the coordinate tangent vectors are linearly independent and
infinitely many, so `epsDer` is not finite-dimensional, and Mathlib's `finrank` (zero in
infinite rank) would make the strict inequality below fail.

- `epsDerEval : epsDer k A →ₗ[k] (σ → k)` evaluates on the coordinates.
  `epsDerEval_bijective`: it is bijective. It is injective by the previous lemma; it is
  surjective, with `v ↦ ∑ vᵢ ξᵢ` (a finite sum because `σ` is finite).
- Hence `finrank_epsDer`: `finrank k (epsDer k A) = #σ` (for nontrivial `k`), and
  `finite_epsDer`: `Module.Finite k (epsDer k A)`, i.e. the tangent space is finitely
  generated over the commutative ring `k` (finite-dimensional when `k` is a field).

`finrank_epsDer_quotient_lt` (`k` a field, `σ` finite, `hz` as above): let `J` be an ideal
of `A` whose scalar restriction is a coideal, so that `A ⧸ J` is Mathlib's quotient
bialgebra. Suppose `J` contains an element `g` with `ξᵢ(g) ≠ 0` for some `i`. Then
`finrank (epsDer k (A ⧸ J)) < finrank (epsDer k A)`. Composition with the quotient map
embeds the tangent space of `A ⧸ J` into that of `A`, by the dual map of a surjection. Its
image consists of maps vanishing on `g`, so it does not contain `ξᵢ`. The strict
containment gives a strict drop in `finrank` because `epsDer k A` is finite-dimensional
(`finite_epsDer`, which uses the finiteness of `σ`).

## The split datum

`exists_splitDatum h𝒜 h0 G hdiag hlow hA`. Here `k` is a field, and `A` is a domain that is
finitely generated and formally smooth over `k`. `𝒜` is a graded bialgebra structure, and
`h0` says that every degree-`0` element of the augmentation ideal lies in its square. `G`
is a `GradedMatrixCoefficients 𝒜` with unit diagonal (`hdiag`) and zero entries below the
diagonal (`hlow`), and some element of `A` is not a scalar (`hA`). Then there are `g` and
`d ≠ 0` with:

- `g ∈ 𝒜 d`, and `g` primitive;
- a `k`-algebra map `s : A → k[X]` with `s g = X`;
- for every ideal `J` with coideal scalar restriction containing `g`, the tangent space of
  `A ⧸ J` has smaller dimension than that of `A`.

The proof combines the results above:

- `exists_homogeneous_polynomial_coordinates` (from `BigCell`) gives finitely many
  homogeneous coordinates of nonzero weights, on which the counit vanishes, so the
  finite-coordinate results above apply.
- `exists_isPrimitiveElem_of_unitriangular` gives a nonzero homogeneous primitive element.
- Lemma A (`exists_isPrimitiveElem_not_mem_sq`) gives `g` outside the square.
- `h0` forces `d ≠ 0`.
- `exists_algHom_polynomial_eq_X` and `finrank_epsDer_quotient_lt` give the last two
  properties.

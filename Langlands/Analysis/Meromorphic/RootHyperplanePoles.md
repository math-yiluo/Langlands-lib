# Scalar functions with poles along finitely many hyperplanes

Module `Langlands.Analysis.Meromorphic.RootHyperplanePoles`.

## Purpose and provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (J. Amer. Math. Soc.
37 (2024)), Theorem 2.3 (6), says that the singularities of `M(w, λ)` and `E(φ, λ)` lie along
root hyperplanes `⟨λ, β^∨⟩ = c`. The Corollary at the end of §8.6 gives the local form: near
every `λ₀` some power of `∏_β ⟨λ - λ₀, β^∨⟩` times the function is holomorphic. Section 8.6
derives this from two facts:

* for an elementary symmetry `s_α`, `M(s_α, λ)` depends only on `⟨λ, α^∨⟩`;
* the general case follows by decomposing `w` into elementary symmetries and using the
  multiplicativity of intertwining operators.

This module is **derived**. It isolates the scalar, finite-dimensional complex analysis behind
that argument, with no reference to groups or automorphic forms. It is meant to be used by the
proof of `Langlands.Global.IntertwiningRootHyperplaneContinuationStatement`. The labels `ι`,
forms `L : ι → X →ₗ[ℂ] ℂ` and allowed set `R : Set ι` are chosen so that they can be
instantiated by `characterLattice A`, `r.rootFunctional hA hT` and `r.unipotentRoots`. The local
shape of the predicate is exactly the last conjunct of that statement. The space `X` is only
an `AddCommGroup` with a `Module ℂ` structure. All analysis happens in linear coordinates
`e : (Fin n → ℂ) ≃ₗ[ℂ] X`, as in `IsMeromorphicInCoordinatesOn`.

## Definitions

* `HasRootPoleDataAt L e s₀ f D S m W` holds when:
  * `W ⊆ ℂⁿ` is open and contains `s₀`;
  * some `h`, complex differentiable on `W`, satisfies
    `h s = (∏ β ∈ S, L β (e s - e s₀)) ^ m * f (e s)` for all `s ∈ W` with `e s ∈ D`.

  These are local pole data at `λ₀ = e s₀`.
* `HasRootHyperplanePoles L R f D` holds when, for every `n`, every linear coordinate system
  `e : ℂⁿ ≃ X` and every `s₀`, there are a finite set `S ⊆ R`, an exponent `m` and a set `W`
  with `HasRootPoleDataAt L e s₀ f D S m W`. In words, `f`, considered on the domain `D`, has
  poles along the hyperplanes `L β = const`, `β ∈ R`, in the local form of the Corollary of
  §8.6. The function `f` is only constrained on `D`. In applications `D` is the open dense
  domain on which a meromorphic function is given by its values.

## Results

Closure and bookkeeping (local data, section `Basic`):

* `HasRootPoleDataAt.enlarge`: a larger root set, a larger exponent and a smaller
  neighborhood still give pole data.
* `mono`, `congr`, `add`, `const_mul`, `mul_const`, `mul`, `sum_mul`.

Global predicate (section `Global`):

* `mono` (smaller domain), `mono_set` (larger root set) and `congr` (equality on `D`).
* `hasRootHyperplanePoles_of_differentiable`: no poles for functions holomorphic in every
  coordinate system. `hasRootHyperplanePoles_const`.
* `mul`, `add`, `const_mul`, `neg`, `sub`, `sum_mul`, `finset_sum`, `finset_prod`.
* `exists_common_hasRootPoleDataAt` and `exists_rootPoleData_family`: for finitely many
  functions there is one root set, one exponent and one neighborhood, with a numerator for
  each function.
* `HasRootHyperplanePoles.of_eqOn_dense`: transfer from a subdomain `D' ⊆ D` that is dense in
  `D` in every coordinate system, to a function that is continuous on `D` and agrees on `D'`.
  The proof extends equality from `W ∩ e⁻¹ D'` to `W ∩ e⁻¹ D` by continuity
  (`Set.EqOn.of_subset_closure`).
* `of_eqOn_of_isMeromorphicInCoordinatesOn` is the same transfer when the target function is
  `IsMeromorphicInCoordinatesOn` on `D` and `D'` is dense in coordinates.
* `exists_rootPoleData_sum_mul`: if the coefficients `c i` have such poles, then for an
  expansion `λ ↦ ∑ i, c i λ * ψ i g` the root set, exponent and neighborhood can be chosen
  before `g`. Its conclusion has the shape of the last conjunct of
  `IntertwiningRootHyperplaneContinuationStatement`.
* `exists_points_sum_mul_eq`: finitely many points `q j` and functions `a j` satisfy
  `∑ i, c i * ψ i g = ∑ j, (∑ i, c i * ψ i (q j)) * a j g` for all `c` and `g`. The proof takes
  a basis of the span of the vectors `(ψ i g)_i`, made of such vectors
  (`Submodule.exists_fun_fin_finrank_span_eq`).
* `exists_rootPoleData_sum_mul_of_forall` is the same uniform choice when only every
  expansion `λ ↦ ∑ i, c i λ * ψ i g` is known to have such poles. No linear independence is
  needed: the expansion is rewritten through the points above.
* `exists_points_coeff_eq` and `HasRootHyperplanePoles.coeff_of_linearIndependent`: if the
  `ψ i` are linearly independent, each coefficient `c i` is a fixed finite combination of
  expansions evaluated at points, so it inherits the poles. The proof shows that the
  vectors `(ψ i g)_i` span `ℂᵏ`; otherwise a nonzero linear form would vanish on them
  (`Submodule.exists_le_ker_of_lt_top`), giving a linear relation among the `ψ i`.

Changes of variables and forms (section `Change`):

* `comp_linearEquiv`: pullback along a linear equivalence `T : X ≃ Y`, with forms
  `L β ∘ T`.
* `comp_linearMap`: pullback along any linear map `τ : X → Y` into a finite-dimensional
  space. The proof uses the coordinates `e'` of `Y` given by `Module.finBasis` and the matrix
  `A` with `e' ∘ A = τ ∘ e`. Pole data of `f` at `A s₀` are pulled back along `A`.
* `of_proportional`: poles along forms `L' β`, `β ∈ R'`, are poles along forms `L γ`,
  `γ ∈ R`, when each `L' β` equals `a β • L (σ β)` with `a β ≠ 0` and `σ β ∈ R`. The new
  root set is the image of `S` under `σ`. The exponent becomes `card S * m`, and a
  differentiable factor fills each multiplicity up to `card S`. The constant
  `(∏ a β)⁻¹ ^ m` is absorbed.
* `comp_linearMap_of_proportional` and `comp_linearEquiv_of_proportional` combine both. Note
  the direction: `σ` sends the labels of the pole forms on `Y` to labels on `X`.

The one-variable criterion (section `Invariant`, then `Criterion`):

* `exists_pow_mul_eq_of_kernel_invariant` works in a normed space `E`. Suppose that:
  * `g * F = h` on `U ∩ W`, with `g` and `h` complex differentiable on the connected open
    set `W ∋ s₀`, and `g` not identically zero there;
  * `F` is invariant on the open set `U` under translations by the kernel of a continuous
    linear form `a`.

  Then near `s₀` some power `a (s - s₀) ^ m` times `F` agrees on `U` with a function
  complex differentiable near `s₀`.

  Proof, as implemented:
  1. If `a = 0` take `m = 1` and the zero function. Otherwise pick `u` with `a u = 1`.
  2. Pick a point `p₁` close to `s₀` with `g p₁ ≠ 0`. Use the library's
     `exists_ne_zero_of_differentiableOn`.
  3. Restrict `g` to the complex line `ℓ z = p₁ + (z - a p₁) • u`. This restriction is not
     identically zero near `a s₀`, because the identity theorem applies on the disc and
     `ℓ (a p₁) = p₁`. So it factors as `(z - a s₀) ^ N * w z` with `w` analytic and nonzero
     near `a s₀`, by Mathlib's `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`.
  4. Take `m = N` and `H s = h (ℓ (a s)) / w (a s)`.
  5. Check the identity for `s ∈ U` near `s₀`. On the segment `t ↦ s + t • (ℓ (a s) - s)`,
     this segment direction lies in `ker a`, and the function `h - F s * g` vanishes near
     `t = 0` by invariance. By the identity theorem on the convex ball it vanishes at `t = 1`,
     so `h (ℓ (a s)) = F s * g (ℓ (a s)) = F s * (a s - a s₀) ^ N * w (a s)`.
* `convex_preimage_line`: the parameters `t ∈ ℂ` with `x + t • y` in a convex set form a
  convex set. It is used for the segment above.
* `hasRootHyperplanePoles_of_kernel_invariant`: if `f` is `IsMeromorphicInCoordinatesOn` on
  `D` and `f (x + ν) = f x` whenever `x, x + ν ∈ D` and `L β ν = 0`, with `β ∈ R`, then
  `HasRootHyperplanePoles L R f D` holds with root set `{β}`. In every coordinate system the
  local quotient presentation of the meromorphic function provides `g` and `h` for the
  previous lemma, with `a = L β ∘ e`.

## Scope

The module does not prove anything about intertwining operators. It contains no claim that
`M(s_α, λ)` depends only on `⟨λ, α^∨⟩`, and none about the decomposition into elementary
symmetries (Mœglin–Waldspurger I.1.8). Those inputs, and the global assembly, belong to the
proof of `IntertwiningRootHyperplaneContinuationStatement`.

# Vanishing of graded components of an augmented graded algebra

This module proves a vanishing criterion for the homogeneous components of the augmentation
ideal of a graded algebra. Let `k` be a field and `C` a Noetherian `k`-algebra, graded by an
additive abelian group `Λ` through `𝒜 : Λ → Submodule k C` (`GradedAlgebra 𝒜`). Let
`ε : C →ₐ[k] k` be an augmentation that kills every homogeneous element of nonzero degree.
Suppose `C` has no idempotents other than `0` and `1`. Let `P` be an additive subsemigroup of
`Λ` with `0 ∉ P`. Suppose that, for every degree `χ ∉ P`, every first-order deformation of `ε`
supported in degree `χ` is trivial. Then, for every `χ ∉ P`, every element of `𝒜 χ` in the
kernel of `ε` is zero.

All declarations are in namespace `Langlands.Algebra.GradedAugmented`.

## Definition

`IsRigidInDegree 𝒜 ε χ` (a `Prop`, for a field `k`, a commutative `k`-algebra `C`, any index
type `Λ`, `𝒜 : Λ → Submodule k C`, `ε : C →ₐ[k] k` and `χ : Λ`) says the following. Let
`φ : C →ₐ[k] DualNumber k` be a `k`-algebra map to the dual numbers `k[ε] = k ⊕ kε` that lifts
`ε`, i.e. `(TrivSqZeroExt.fstHom k k k).comp φ = ε`. Suppose its `ε`-coefficient `(φ c).snd`
vanishes for all `c ∈ 𝒜 ψ` and all degrees `ψ ≠ χ`. Then `(φ c).snd = 0` for all `c : C`.

Such lifts `φ` correspond to `k`-linear derivations `D = (φ ·).snd : C → k` at `ε`, that is,
`D (x y) = ε x · D y + D x · ε y`. The condition on `φ` says that `D` is supported in degree
`χ`. So `IsRigidInDegree 𝒜 ε χ` says that every derivation of `C` at `ε` supported in degree
`χ` is zero.

## Main theorem

`eq_zero_of_notMem`. The hypotheses are `[Field k]`, `[CommRing C]`, `[Algebra k C]`,
`[IsNoetherianRing C]`, `[AddCommGroup Λ]`, `[DecidableEq Λ]`, `[GradedAlgebra 𝒜]`,
`ε : C →ₐ[k] k`, and the following:

- `hε : ∀ χ ≠ 0, ∀ c ∈ 𝒜 χ, ε c = 0`;
- `hconn : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1`;
- `P : AddSubsemigroup Λ` with `h0 : (0 : Λ) ∉ P`;
- `hD : ∀ χ ∉ P, IsRigidInDegree 𝒜 ε χ`.

The conclusion is `∀ χ ∉ P, ∀ c ∈ 𝒜 χ, ε c = 0 → c = 0`. The universes of `k`, `C` and `Λ`
are independent. The degree `χ = 0` is included, since `0 ∉ P`.

## Supporting lemmas

These hold for a field `k`, a commutative `k`-algebra `C` and a `GradedAlgebra 𝒜` over an
additive abelian group `Λ` with decidable equality. Each assumes `hε` as above, and
`m = RingHom.ker ε` is the augmentation ideal.

- `augmentation_decompose`: `ε (decompose 𝒜 x χ)` equals `ε x` if `χ = 0` and `0` otherwise.
- `isHomogeneous_ker`: `m` is a homogeneous ideal.
- `decompose_mem_ker`: every graded component of an element of `m` lies in `m`.
- `mem_ker_sq`: if `IsRigidInDegree 𝒜 ε χ` holds, then every `c ∈ 𝒜 χ` with `ε c = 0` lies
  in `m ^ 2`.

## Proof

1. *Degree-`χ` elements of `m` lie in `m²`* (`mem_ker_sq`). Suppose `c ∈ 𝒜 χ`, `ε c = 0` and
   `c ∉ m²`. Then `c` is not in the `k`-subspace `p = m² ∩ 𝒜 χ`. A linear form
   `l : C → k` vanishes on `p` with `l c ≠ 0`
   (`Submodule.exists_dual_map_eq_bot_of_notMem`). Let `π` be the projection onto degree `χ`
   (`GradedAlgebra.proj`). The ideal `m²` is homogeneous, so `π` maps `m²` into `p`. Set
   `D x = l (π (x - ε x))`. Expanding `x y - ε (x y)` as
   `(x - ε x)(y - ε y) + ε x (y - ε y) + ε y (x - ε x)`, the first term lies in `m²`, so
   `D (x y) = ε x · D y + D x · ε y`. Hence `φ x = (ε x, D x)` is a `k`-algebra map
   `C → DualNumber k` lifting `ε`. If `c' ∈ 𝒜 ψ` with `ψ ≠ χ`, then `π c' = 0` and
   `π (ε c') = 0` (the constant `ε c'` has degree `0`; if `χ = 0` then `ε c' = 0` by `hε`).
   So `D` is supported in degree `χ`, and `IsRigidInDegree` gives `D = 0`. But
   `D c = l c ≠ 0`, a contradiction.
2. *Degree-`χ` elements of `m` lie in all powers of `m`.* By induction on `n`: for `χ ∉ P`,
   every `c ∈ 𝒜 χ ∩ m` lies in `m ^ (n + 1)`. The case `n = 0` is `c ∈ m`. For the inductive
   step, `c ∈ m * m` by step 1. It suffices that, for every `x ∈ m * m`, the degree-`χ`
   component of `x` lies in `m ^ (n + 2)`. By `Submodule.mul_induction_on`, take `x = a b`
   with `a, b ∈ m` (sums are clear). The degree-`χ` component of `a b` is the sum of
   `a_i b_j` over `i + j = χ` (`DirectSum.coe_mul_apply`), and `a_i, b_j ∈ m` by
   `decompose_mem_ker`. As `P` is closed under addition, `i ∉ P` or `j ∉ P`. If `i ∉ P`, the
   induction hypothesis gives `a_i ∈ m ^ (n + 1)`, so `a_i b_j ∈ m ^ (n + 2)`. The case
   `j ∉ P` is symmetric. For `x = c` the degree-`χ` component is `c` itself.
3. *A common element fixing the intersection.* Let `N = ⋂ₙ mⁿ` as an ideal. The `m`-stable
   filtration `mⁿ C` meets the constant filtration `N` in a filtration that is again
   `m`-stable (Artin–Rees, `Ideal.Filtration.Stable.inter_right`, using that `C` is
   Noetherian). Its terms are all `N`, so `N = m • N`. As `N` is finitely generated,
   Nakayama's lemma (`Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul`) gives `r ∈ m`
   with `r n = n` for all `n ∈ N`. This repeats the proof of the forward direction of
   Mathlib's `Ideal.mem_iInf_smul_pow_eq_bot_iff`. That statement lets `r` depend on the
   element, but its proof produces one `r` for all of `N`, which step 4 needs. By step 2, `N`
   contains every `c ∈ 𝒜 χ ∩ m` with `χ ∉ P`.
4. *The degree-zero part of `r` is zero.* Let `r₀` be the degree-`0` component of `r`. Then
   `r₀ ∈ m` by `decompose_mem_ker`, and `r₀ ∈ N` by step 3, since `0 ∉ P`. So `r r₀ = r₀`.
   Taking degree-`0` components (`DirectSum.coe_decompose_mul_of_right_mem_zero`) gives
   `r₀ r₀ = r₀`. By `hconn`, `r₀ = 0` or `r₀ = 1`. The case `r₀ = 1` contradicts
   `ε r₀ = 0`.
5. *Conclusion.* Let `χ ∉ P`, `c ∈ 𝒜 χ` and `ε c = 0`. Then `c ∈ N`, so `r c = c`. Taking
   degree-`χ` components (`DirectSum.coe_decompose_mul_add_of_right_mem`) gives
   `r₀ c = c`. So `c = 0`.

## Provenance

This is an internal supporting lemma. It is part of the explicit Hopf-algebra route of the
proof task for `Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement`. There
`C` is the coordinate ring of a closed subgroup with its torus grading, `ε` is the counit, and
the hypothesis `hD` comes from the vanishing of Lie algebra weight spaces. The statement
shape, with `IsRigidInDegree` unfolded, was fixed with the task's first executor. No
literature source is cited. The argument is standard commutative algebra (graded
derivations, Artin–Rees and Nakayama). The Lean proof above is self-contained modulo
Mathlib.

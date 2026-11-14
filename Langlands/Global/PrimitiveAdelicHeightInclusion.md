# Normalized adelic heights under the inclusion of adeles along a field extension

This internal helper module compares the normalized coordinate height of the
Library (`Langlands.Global.PrimitiveAdelicHeight.height`) over two number
fields. Let `L / K` be a finite extension of number fields and let
`adeleInclusion : 𝔸_K → 𝔸_L` be the published inclusion of adele rings
(`Langlands.Global.AdelicFunctoriality.Inclusion`). Take a vector `x ∈ 𝔸_Kⁿ` whose
finite local maximum norms equal `1` at all but finitely many places. Then the
height of its coordinatewise image over `L` is the `[L : K]`-th power of its
height over `K`:

`height L n (fun i => adeleInclusion (x i)) = height K n x ^ [L : K]`.

This is the standard behaviour of heights built from normalized absolute values
under a finite extension. The descent step of Springer, *Reduction theory over
global fields* (1994), §3.6, takes a height on `V(A, l)` "whose restriction to
`V(A, k)` is the previous height" and compares heights over the splitting field
`l` with heights over the ground field `k`. For the fixed normalized height of
the Library, the restriction is the `[l : k]`-th power of the height over `k`,
and this module proves that identity. Springer does not state the identity in
this form; the statement and proof here are our own formalization.

The fields `K` and `L` may live in different universes `u` and `v`. Norms are
the Library ones. At a finite place `p` the norm on `p.adicCompletion K` is the
normalized one, `‖x‖ = absNorm(p)^(-v_p(x))` (Mathlib's
`NumberField.FinitePlace.norm_def`). At an infinite place the norm on the
completion is the absolute value of that place. On `Fin n`-vectors the norm is
the maximum of the coordinate norms. The height is the product of the infinite
local maximum norms, each raised to the multiplicity `mult` of its place, times
the finite product (`finprod`) of the finite local maximum norms.

## Local comparisons

`FiniteExtension.toNNReal_pow_base` and `FiniteExtension.toNNReal_congr` are two
rewriting lemmas for `WithZeroMulInt.toNNReal`. The map
`WithZeroMulInt.toNNReal` turns a `ℤᵐ⁰`-valuation into a real number, with the
base given as an argument. The first lemma says that using base `e ^ f` instead
of `e` raises every value to the `f`-th power. The second lemma replaces the base
by an equal one.

`FiniteExtension.norm_completionMap`. Let `q` be a finite place of `L` lying
over the finite place `p` of `K`. Let `e` and `f` be the ramification index and
inertia degree of `q` over `p`. Then for `x` in the completion of `K` at `p`,

`‖completionMap p q x‖ = ‖x‖ ^ (e * f)`.

Proof. The published `valuation_completionMap` says the valuation of the image
is the `e`-th power of the valuation of `x`. Mathlib's `Ideal.absNorm_pow_inertiaDeg`
gives `absNorm(q) = absNorm(p) ^ f`. Combining these with the two rewriting
lemmas gives the exponent `e * f`.

`norm_infiniteCompletionMap`. Let `w` be an infinite place of `L`. The published
map `infiniteCompletionMap` goes from the completion of `K` at the restriction of
`w` to the completion of `L` at `w`. It preserves norms. Proof: `algebraMap K L`
is an isometry between `K` and `L` with the absolute values of these two places.
So its extension to completions is an isometry
(`Isometry.completion_map`).

`pi_norm_eq_pow_of_forall`. Take two families of normed groups indexed by
`Fin n` and a positive exponent `d`. Suppose `‖b i‖ = ‖a i‖ ^ d` for every
coordinate `i`. Then the maximum norms satisfy `‖b‖ = ‖a‖ ^ d`. Proof: `t ↦ t ^ d`
is monotone on `ℝ≥0` and sends `0` to `0`, so it commutes with finite suprema.

## Products over places

`finite_preimage_under`. For a finite set `S` of finite places of `K`, the set
of finite places of `L` lying over a place of `S` is finite. Proof: above each
place `p` there are only finitely many places (`FinitePlacesAbove L p` is a
finite type).

`finprod_under_pow`. Let `f` be a real function on the finite places of `K` with
finite multiplicative support. Then

`∏ᶠ q, f (q under K) ^ (e_q * f_q) = (∏ᶠ p, f p) ^ [L : K]`,

where the left product runs over the finite places `q` of `L`. Proof: both
products are finite products over the support of `f` and its preimage. Group
the left side by the place `p` below `q`. For each `p` the exponents add up to
`∑_{q | p} e_q f_q = [L : K]`. This is the published fundamental identity
`finitePlacesAbove_sum_ramification_inertia`.

`prod_comap_pow_mult`. Let `f` be a real function on the infinite places of `K`.
Then

`∏_w f (w restricted to K) ^ mult(w) = (∏_v f v ^ mult(v)) ^ [L : K]`,

where `w` runs over the infinite places of `L` and `v` over those of `K`. Proof:
group the left side by the restriction `v` of `w`. Mathlib's
`InfinitePlace.mult_mul_finrank` gives `mult(w) = mult(v) * [L_w : K_v]`. The
published `infiniteLocalDegree_sum` gives `∑_{w | v} [L_w : K_v] = [L : K]`.

## Height comparison

`height_adeleInclusion`. Let `x : Fin n → Adeles K` be such that the function
`p ↦ finiteNorm K n x p` has finite multiplicative support. This holds for
primitive vectors by the published `IsPrimitive.hasFiniteMulSupport`. Then

`height L n (fun i => adeleInclusion (x i)) = height K n x ^ Module.finrank K L`.

Proof. The component at a finite place `q` of the image vector is
`completionMap` applied to the component at the place below `q`. So, by
`norm_completionMap` and `pi_norm_eq_pow_of_forall`, the finite local maximum
norm at `q` is the norm below raised to the power `e_q f_q`. The component at an
infinite place `w` is `infiniteCompletionMap` applied to the component at the
restriction of `w`. By `norm_infiniteCompletionMap` the infinite local maximum
norm at `w` equals the norm at the restriction. Now `finprod_under_pow` handles
the finite product, `prod_comap_pow_mult` the infinite product, and `mul_pow`
combines them.

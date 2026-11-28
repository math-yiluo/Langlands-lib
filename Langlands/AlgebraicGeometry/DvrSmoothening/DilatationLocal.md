# Local structure of a centre cut out by points of ramification index one

- `mem_of_mul_mem_sq`: **property (N) for the centre.** If `J = ⋂ S` where each `p ∈ S` is
  `ψ⁻¹(𝔪)` for a point `ψ : A → R''` of ramification index one, then `ϖ a ∈ J²` implies `a ∈ J`.
  Indeed `ψ(J²) ⊆ ϖ² R''` since `ϖ` is a uniformizer of `R''`, so `ϖ ψ(a) ∈ ϖ² R''` and
  `ψ(a) ∈ 𝔪`.
- `exists_mul_eq_zero_of_linearIndependent`: let `M` be a finite free `B`-module and `K` a field
  which is a `B`-algebra. If a finite family in `M` has linearly independent images in `K ⊗_B M`,
  every relation among its members has coefficients killed by one `t ∈ B` with non-zero image in
  `K`. The proof passes to the localization at the kernel of `B → K` and uses Mathlib's
  `Module.IsLocalRing.linearIndependent_of_flat`.
- `exists_extension`: for `d : α → V` into a finite-dimensional vector space and sets
  `s_I ⊆ s_J`, there are `wₗ ∈ s_I` and `zⱼ ∈ s_J` with `(d z, d w)` linearly independent, the
  `d wₗ` spanning `d(s_I)` and the `d zⱼ, d wₗ` spanning `d(s_J)`.

The first item is the use of property (N) in Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3,
proof of Proposition 5 (printed p. 69): evaluating at the points shows that `g` vanishes on the
centre.

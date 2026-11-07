# Integral root-datum lemmas for positive multiples of dominant weights

Worker 1161. This module is internal linear algebra over `ℤ` for an arbitrary
root pairing `P : RootPairing ι ℤ M N` with finitely many roots and a base `b`.
It supports the proof, in `DominantMultipleAssembly`, that every dominant character
of a split pinning has a positive multiple realized by a normalized covariant
coordinate. The root pairing need not be a root system: the roots need not span
`M`, so the reductive (non-semisimple) case is included. Everything is derived from
Mathlib's `RootPairing`, `RootPairing.Base`, the canonical forms `RootForm` and
`CorootForm`, adjugate matrices, and the structure theory of finitely generated
modules over `ℤ`. No external theorem is cited.

## Contents

- `pairing_sum_nsmul`: the pairing of a nonnegative integral combination of
  simple roots with a cocharacter is the corresponding combination of pairings.
- `root_sign`: suppose `nu` pairs positively and `mu` nonnegatively with every
  simple root. Then each root `r` satisfies either
  `0 < ⟨r, nu⟩` and `0 ≤ ⟨r, mu⟩`, or `⟨r, nu⟩ < 0` and `⟨r, mu⟩ ≤ 0`.
  The proof writes `r` as plus or minus a nonnegative integral combination of
  simple roots (`Base.exists_root_eq_sum_nat_or_neg`). Some coefficient is nonzero,
  because roots are nonzero.
- `pairing_root_eq_zero_of_simple`, `pairing_coroot_eq_zero_of_simple`: a
  (co)character killed by the simple (co)roots is killed by all (co)roots, since
  every (co)root lies in the integral span of the simple ones.
- `eq_zero_of_mem_corootSpan`, `eq_zero_of_mem_rootSpan`: an element of the
  integral coroot (root) span killed by every simple root (coroot) is zero. Its
  length for the canonical form is a sum of squares of pairings with roots, hence
  zero. Mathlib's anisotropy of the canonical form on the span over the ordered
  ring `ℤ` gives the conclusion.
- `cartan` is the integral matrix `⟨αⱼ, αₖ^∨⟩` indexed by the base.
  `cartan_det_ne_zero` says its determinant is nonzero. A kernel vector `v` would
  give `x = Σ vₖ αₖ^∨` in the coroot span, killed by all simple roots, so `x = 0`.
  Linear independence of the simple coroots then forces `v = 0`.
- `exists_simple_dual`: for each simple root `αᵢ` there are `ν` in the integral
  coroot span and `c > 0` with `⟨αᵢ, ν⟩ = c` and `⟨αₐ, ν⟩ = 0` for the other simple
  roots. The construction is `ν = det(A) • Σₖ adj(A)ₖᵢ αₖ^∨` with `A = cartan`.
  Then `⟨αₐ, ν⟩ = det(A) (A adj(A))ₐᵢ = det(A)² δₐᵢ`.
- `two_mul_corootForm_coroot`: `2 · B(α^∨, x) = B(α^∨, α^∨) · ⟨α, x⟩` for the coroot
  form `B`. This is the pairing of Mathlib's `corootForm_self_smul_root` with `x`.
- `pairing_simple_coroot_pos`: let `ν` be in the integral coroot span, with
  `⟨αₐ, ν⟩ = 0` for the simple roots `a ≠ i` and `⟨αᵢ, ν⟩ > 0`. Let `σ` be a character
  with `⟨σ, αₐ^∨⟩ = 0` for `a ≠ i` and `⟨σ, ν⟩ > 0`. Then `⟨σ, αᵢ^∨⟩ > 0`. Write
  `ν = Σ mₐ αₐ^∨`. Then `⟨σ, ν⟩ = mᵢ ⟨σ, αᵢ^∨⟩`, and by the previous identity
  `2 B(ν, ν) = mᵢ B(αᵢ^∨, αᵢ^∨) ⟨αᵢ, ν⟩`. Both `B(ν, ν)` and `B(αᵢ^∨, αᵢ^∨)` are
  positive (anisotropy on the coroot span), so `mᵢ > 0`.
- `exists_pos_nsmul_mem_of_orthogonal`: for `M` finitely generated, if the only
  cocharacter orthogonal to a submodule `L` is zero, then every `x ∈ M` has a
  positive multiple in `L`. Otherwise the image of `x` in `(M/L)/torsion` is nonzero.
  That quotient is finitely generated and torsion free, hence free. A coordinate
  functional nonzero on the image lifts to a functional on `M` vanishing on `L`.
  The perfect pairing represents it by a nonzero cocharacter, a contradiction.
- `exists_pos_nsmul_mem_of_dominant`: the final integral combination. Let `S` be
  an additive submonoid of `M` with the following properties.
  - For each simple root `i` it contains some `σᵢ` with `⟨σᵢ, αₐ^∨⟩ = 0` for
    `a ≠ i` and `cᵢ = ⟨σᵢ, αᵢ^∨⟩ > 0`.
  - Every character orthogonal to the simple coroots has a positive multiple
    in `S`.

  Then every dominant `lam` has a positive multiple in `S`. With `C = Πcᵢ` and
  `aᵢ = ⟨lam, αᵢ^∨⟩ Π_{k≠i} c_k ≥ 0`, the character `y = C·lam − Σ aᵢσᵢ` is
  orthogonal to the simple coroots. If `m·y ∈ S`, then
  `mC·lam = m·y + Σ (m aᵢ)·σᵢ ∈ S`.

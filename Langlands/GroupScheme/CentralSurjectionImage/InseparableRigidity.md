# Rigidity of multiplicative points and purely inseparable descent

Author: Worker 1387.

This internal module, in the namespace
`Langlands.GroupScheme.CentralSurjectionImage`, works over a field `k : Type u`.

## Rigidity modulo a nilpotent ideal

- `conv_mem_mul`: if `f` and `g` take values in ideals `I` and `J` of `S`, their
  convolution takes values in `I * J` (induction on the comultiplication
  tensor).
- `IsMultG.eq_one_of_map_eq_one`: let `G` be an affine group scheme over `k`, `p`
  a multiplicative point over `S[Λ]` (`IsMultG p`), and `φ : S →ₐ[k] S'` with
  `(RingHom.ker φ) ^ n = ⊥`. If the coefficient change of `p` along `φ` is the
  identity point, then `p = 1`. Proof: every nonzero weight `w = weight p γ`
  has values in `ker φ` (by `weight_coeffMap` and `weight_one`), and it is a
  convolution idempotent (`IsMultG.conv_weight`). Induction with
  `conv_mem_mul` puts its values in `(ker φ) ^ (m + 1)` for all `m`, hence
  `w = 0`; `IsMultG.eq_one_of_weight_eq_zero` concludes.

## Purely inseparable descent

- `exists_pow_ker_lmul'_eq_bot`: for fields `F ⊆ L` with `L` finite over `F` and
  every `ℓ ^ p ^ e` in `F` (`p` the exponential characteristic), the kernel of
  multiplication `L ⊗[F] L → L` is nilpotent. It is spanned by the elements
  `1 ⊗ ℓ - ℓ ⊗ 1` (`KaehlerDifferential.span_range_eq_ideal`), whose
  `p ^ e`-th powers vanish (`sub_pow_expChar_pow`), so it lies in the nilradical
  of the Artinian ring `L ⊗[F] L`, which is nilpotent
  (`IsArtinianRing.isNilpotent_nilradical`).
- `IsDatum.exists_of_pow_mem_range_of_finite`: for an affine commutative group
  scheme `Z` over `k` and `L / F` as above, a cocharacter datum
  (`CocharacterDatum.IsDatum χ m x`) over `L[Λ]` comes from one of the same
  weight over `F[Λ]`. The proof follows the published
  `CocharacterDatum.IsDatum.exists_of_pow_mem_range`. The quotient of the two
  images of `x` in `(L ⊗[F] L)[Λ]` is multiplicative and becomes trivial along
  `a ⊗ b ↦ 1 ⊗ ab`. That published theorem uses a Frobenius hypothesis on the
  points of `Z`, available for tori. Here triviality instead follows from
  `IsMultG.eq_one_of_map_eq_one`, as the kernel of that map is the nilpotent
  kernel of multiplication. The coordinates then descend by the published
  equalizer descent `exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight`.
- `IsDatum.exists_separableClosure_of_comm`: consequently, for `L` finite over
  `k`, a datum over `L[Λ]` comes from one over `(separableClosure k L)[Λ]`. Unlike
  the published `IsDatum.exists_separableClosure`, no torus hypothesis is needed.

The descent statements are standard; the rigidity proof is internal and no
literature result is attributed to it.

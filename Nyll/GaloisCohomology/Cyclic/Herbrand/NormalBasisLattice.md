# Normal-basis lattices and the principal-unit filtration `1 + π_K^n M`

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension with `K` a nonarchimedean local field. The file studies the `𝒪_K`-lattice `M` spanned by the Galois orbit of Mathlib's normal-basis generator of `L/K`, its multiples `π_K^n M` by powers of the library's chosen uniformizer, and the sets `V^n = {u ∈ 𝒪_L^× : u − 1 ∈ π_K^n M}`. For large `n` it shows that `V^n` is a subgroup of the first principal units and builds a homomorphism `V^n / V^(n+1) → π_K^n M / π_K^(n+1) M`, `u ↦ u − 1`, as preparation for the local class-field calculation.

## Main definitions

- `chosenNormalBasisIntegerLattice K L`, the lattice `M`: Galois-stable, finitely generated, spanning `L` over `K`.
- `chosenBaseUniformizerPowSubmodule K L n N`: `π_K^n N` for `π_K = chosenIntegerRingUniformizer K`; decreasing in `n`.
- `integerRingFieldSubmodule K L`, `maximalIdealFieldSubmodule K L`: `𝒪_L` and `𝓂_L` as `𝒪_K`-submodules of `L`.
- `chosenNormalBasisPrincipalUnitSet K L n`: the set `V^n`.
- `chosenNormalBasisLatticeSuccQuot K L n`: the `𝒪_K`-module `π_K^n M / π_K^(n+1) M`; `chosenNormalBasisPrincipalUnitSuccQuot hV`: `Vn / Vsucc` for subgroups `Vsucc ≤ Vn`.
- `chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom`: `u ↦` class of `u − 1`, under the hypothesis that `(uv − 1) − (u − 1) − (v − 1)` lies in `π_K^(n+1) M`.

## Main results

- `exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top`: if an `𝒪_K`-submodule spans `L` over `K` and `N` is finitely generated, some `π_K^n N` lies in it.
- For large `n`, `π_K^n M` is closed under multiplication, and products of pairs of its elements lie in `π_K^(n+1) M`.
- When `L` is also a nonarchimedean local field whose valuation extends that of `K`, some `π_K^n M` lies in `𝓂_L`.
- `chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed`: if `π_K^n M` is closed, lies in `𝓂_L` and is closed under multiplication, `V^n` is closed under inverses.
- Under `[Module.Finite 𝒪[K] 𝒪[L]]`, some `π_K^a 𝒪_L` lies in `M`, so `π_K^n M` is open, hence closed, for large `n`; then `exists_chosenNormalBasisPrincipalUnitSubgroup` gives, for `n ≥ c`, a subgroup with carrier `V^n` inside `principalUnits L 1`, and `exists_chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom` the homomorphism above.

## Proofs

The inverse of `u` is the limit of finite geometric sums in `−(u − 1)` (`1 + inverseCorrectionPartialSum`), which converge because `u − 1 ∈ 𝓂_L`.

## Points to watch

- `M` depends on Mathlib's chosen normal-basis generator and `π_K^n M` also on the chosen uniformizer; no independence result is proved.
- Finiteness of `𝒪_L` over `𝒪_K` is assumed, not proved.
- The results say "there is `c` such that for all `n ≥ c`"; the constants are not explicit.
- The map `V^n / V^(n+1) → π_K^n M / π_K^(n+1) M` is only shown to be a homomorphism; injectivity and surjectivity are not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`: the Lean file is the source byte for byte (SHA-256 `544fd03e0f54d45cf39e4c9f93dc5a212c744eeb7725740af46dabefb18b1d90`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

# Elements commuting with a block-diagonal element

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). It replaces the
book's compactness argument ((2.2.3) and the use of (1.2.8)) with a filtration argument.

## Setting

- `L` is a field acting on `V`, whose units normalize the chain `𝓛`.
- `w` is a relative splitting basis (`RelSplits`, `RefinementDiagonal`), with matrix units
  `ε_{jk}`, and `l₀` is an index.
- `β₁` commutes with every `ε_{jk}`.
- `hcore`: every `X ∈ 𝔓^t` commuting with `β₁` is congruent mod `𝔓^{t+1}` to an endomorphism
  commuting with `L`.

## Results

- `entry_mem`: if `X ∈ 𝔓^s`, then the action of its `(l, l)` entry `w.repr (X (w l)) l` lies
  in `𝔓^s`.
- `sub_entry_mem` (**CC'**): an `X ∈ 𝔓^s` commuting with the matrix units and with `β₁`
  satisfies `X ≡ (action of its (l₀, l₀) entry) (mod 𝔓^{s+1})`. Proof: compress
  `X - γ` (with `γ` from `hcore`) to the line `l₀`, then diagonalize. The `L`-linear `γ`
  compresses to multiplication by its entry (`compress_of_commute`).
- `le_depth_of_sub_mem`: depths are preserved under congruence modulo the next step.
- `exists_unit_of_commute` (**Inv**): a nonzero such `X` is a unit normalizing the chain. If
  `X` has exact depth `s` and entry `e`, then `e ≠ 0`, the action of `e` has depth exactly `s`,
  and `e⁻¹X ∈ 1 + 𝔓^1` is a unit in `U^1(𝔄)`.
- `normalizingUnits_elementAlgebra`: every nonzero element of `F[β₁]` is a unit normalizing the
  chain.
- `commute_matUnit_of_mem_elementAlgebra`: elements of `F[β₁]` commute with the matrix units.
- `exists_mem_elementAlgebra_entry_eq` (**entry map is onto**): every `a ∈ L` is the
  `(l₀, l₀)` entry of some element of `F[β₁]`. Let `x` be the compression of `β₁` to the line
  `l₀`, so `Δ(x) = β₁`. By Inv, every nonzero `p ∈ End_F(L)` commuting with `x` is injective.
  So `F[x]` is a field and `L` is an `F[x]`-vector space. If `F[x]·1 ≠ L`, a nonzero
  `F[x]`-linear functional `f` vanishing on `F[x]·1` gives `p(b) = f(b)(1)`. This `p` is
  nonzero, commutes with `x` and kills `1`, a contradiction. Hence `a = q(1)` with `q ∈ F[x]`,
  and `Δ(q) ∈ F[β₁]` has entry `a`.
- `approx_elementAlgebra_range` and `approx_range_elementAlgebra`: `F[β₁]` and the image of `L`
  approximate each other at every level (`Approx`), by CC' and the entry map.

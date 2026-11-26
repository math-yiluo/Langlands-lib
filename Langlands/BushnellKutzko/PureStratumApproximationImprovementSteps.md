# Moving a simple approximation to a second chain normalized by the same field

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, proof of (2.4.5), printed pp. 67–69 (PDF pp. 79–81), and the final step of the proof of (2.4.1)(i), printed pp. 70–71 (PDF pp. 82–83). These derived results are the two constructions used there, in the Library's chain model. The second chain `𝓛'` is normalized by `E = F[γ]`, and every lattice of `𝓛'` lies between two consecutive lattices of the original chain `𝓛`. The source asks for this compatibility after (2.3.1) and in (2.3.4).

## Auxiliary results

- `normalizingUnits_of_generated`: if `β` generates `E` and `Eˣ` normalizes a chain, the generated algebra of the action of `β` has normalizing units.
- `mem_endFiltration_of_le_valuation_subfield` and `le_valuation_of_mem_subfield`: for a chain over `subfieldIntegers F E`, valuation and filtration membership correspond. The proof transfers the chain to `𝒪[E]` and uses `mem_endFiltration_of_le_valuation` and `le_valuation_of_mem`.
- `exists_simple_of_normalized` (BK93 (1.4.13)): let `[𝓛,n,r,γ]` be simple and `ρ e(𝓛) ≤ r e(𝓛')`. Then `[𝓛',n',ρ,γ]` is a simple stratum with `n' e(𝓛) = n e(𝓛')`. The valuation and critical exponent come from `exists_valuation_of_normalized` and `criticalExponent_lt_of_normalized`.

## The two steps

Let `S = [𝓛,n,r,γ]` be simple with `γ` the action of a generator of `E`. Let `s` be a tame corestriction and `β − γ ∈ 𝔓^{−r}(𝓛)`.

- `exists_improvement_of_le` (the non-fundamental case of (2.4.5)): suppose `ρ e(𝓛) < r e(𝓛')`, `s(β − γ) ∈ 𝔓^{−ρ}(𝓛')`, and every `E`-linear element of `𝔓^{1−r}(𝓛)` lies in `𝔓^{−ρ}(𝓛')`. Then some simple stratum `T` on `𝓛'` with `T.r = ρ` has `β ∈ T.coset` and the invariants of `F[γ]`. The proof applies `exists_conj_sub_mem`. Then `endFiltration_le_of_restrict_le` gives `𝔓^{1−r}(𝓛) ⊆ 𝔓^{−ρ}(𝓛')`. So `gβg⁻¹ − γ ∈ 𝔓^{−ρ}(𝓛')`, and `T` is `conjStratum` of `[𝓛',n',ρ,γ]` by `g`. Here `g` and `g⁻¹` preserve the lattices of `𝓛'` by `one_add_mem_order_of_sandwiched`.
- `exists_refinement_of_coset` (the scalar-fundamental case of (2.4.5), and the construction of the final step): suppose `ρ e(𝓛) = r e(𝓛')`. Let `C = [𝓛'_E,ρ,ρ−1,c]` be a simple stratum over `E` on the same lattices as `𝓛'`, with `s(β − γ) ∈ C.coset`. Suppose every `E`-linear element of `𝔓^{1−r}(𝓛)` lies in `𝔓^{1−ρ}(𝓛')`. Then there are simple strata `T`, `U` on `𝓛'` with `U.n = T.n`, `T.r = ρ`, `U.r = ρ − 1` and `β` in both cosets. `F[T.b]` has the invariants of `F[γ]`; `F[U.b]` has those of `F[γ, c]`, and `k₀(U.b) = max(k₀(γ,𝓛'), k₀(c))`. The proof first conjugates as before, giving `p ∈ 𝔓^{−ρ}(𝓛')` with `s(p) = s(β − γ)`. It forms the derived stratum `[𝓛'_E,ρ,ρ−1,s(p)]` of `[𝓛',n',ρ,γ]`, which is equivalent to `C`. It then applies the refinement theorem in the form `refinement_aux` (BK93 (2.2.8), printed p. 56). This gives `U₀` with coset `γ + p + 𝔓^{1−ρ}(𝓛')`. `T` and `U` are the conjugates by `g` of `[𝓛',n',ρ,γ]` and `U₀`.

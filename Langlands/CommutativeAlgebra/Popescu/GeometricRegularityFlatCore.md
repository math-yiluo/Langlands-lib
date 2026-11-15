# Linear independence in `𝔪/𝔪²` from injectivity on `H₁` (core of Stacks 07E6)

This file holds the cotangent-complex part of the proof of Stacks, More on Algebra,
Lemma 15.36.2 (07E6). All objects are Mathlib's naive cotangent complex: `Algebra.H1Cotangent`
and `Algebra.Extension`.

## Declarations

- `residueExtension A`: the extension `A → κ(A)` of a local ring onto its residue field, with
  underlying ring `A`. The section is chosen by `Classical.choose`.
- `residueExtension_ker`: its kernel is `𝔪_A`.
- `mem_residueExtension_ker`, `residueExtension_mk_eq_zero_iff` and `residueExtension_sum_mk`
  are bookkeeping for its conormal module `𝔪/𝔪²`:
  - the class of `x` vanishes iff `x ∈ 𝔪²`;
  - `∑ ā_i · [x_i] = [∑ a_i x_i]`.
- `residueExtension_h1Cotangentι_surjective`: `Ω_{A/A} = 0`, so every element of the conormal
  module lies in `H₁` of the extension.
- `residueExtension_map_defaultHom_bijective`: the canonical map
  `H₁(L_{κ(A)/A}) → H₁(residueExtension A)` is bijective. It is Mathlib's
  `Extension.H1Cotangent.equiv`, applied to the default hom and to the hom
  `A → A[κ(A)]`, `a ↦ C a`, in the other direction.
- `h1Cotangent_map_surjective`: Jacobi–Zariski (Stacks 00S2, Mathlib's `exact_map_δ` and
  `exact_δ_mapBaseChange`). If `T ⊗_S Ω_{S/R} → Ω_{T/R}` is injective, then the connecting map
  `δ` vanishes, so `H₁(L_{T/R}) → H₁(L_{T/S})` is surjective.
- `residueExtensionHom A₀ A`: the hom of extensions induced by a local map `A₀ → A`.
- `h1_path_eq`: the two composites `H₁(L_{κ₀/k}) → H₁(residueExtension A)` agree.
  - The first runs through `H₁(L_{κ₀/A₀}) → 𝔪₀/𝔪₀²`.
  - The second runs through `H₁(L_{κ/k}) → H₁(L_{κ/A})`.

  Both are `Extension.H1Cotangent.map` of a hom of extensions (`map_comp_apply`). Mathlib's
  `Extension.H1Cotangent.map_eq` says that such maps do not depend on the hom.
- `cotangent_independent`: the core statement, described below.

## `cotangent_independent`

Let `A₀ → A` be a local homomorphism of local `k`-algebras, with residue fields `κ₀ → κ`.
Assume:
1. `H₁(L_{κ/k}) → H₁(L_{κ/A})` is injective;
2. `κ ⊗_{κ₀} H₁(L_{κ₀/k}) → H₁(L_{κ/k})` is injective;
3. `κ₀ ⊗_{A₀} Ω_{A₀/k} → Ω_{κ₀/k}` is injective.

Let `x_i ∈ 𝔪₀` be such that `∑ b_i x_i ∈ 𝔪₀²` forces every `b_i ∈ 𝔪₀`, that is, the classes
are independent in `𝔪₀/𝔪₀²`. Then `∑ a_i x_i ∈ 𝔪_A²` forces every `a_i ∈ 𝔪_A`.

Proof.
1. By hypothesis 3 and Jacobi–Zariski, together with the bijection above, the map
   `θ₀ : H₁(L_{κ₀/k}) → 𝔪₀/𝔪₀²` is surjective. Choose `h_j` with `θ₀(h_j) = [x_j]`.
2. Put `w = ∑ ā_j ⊗ h_j` in `κ ⊗ H₁(L_{κ₀/k})`. By `h1_path_eq`, its image in `𝔪_A/𝔪_A²`
   (through `H₁(L_{κ/k})` and `H₁(L_{κ/A})`) is `[∑ a_j x_j] = 0`.
3. Every map in this chain is injective: hypotheses 2 and 1, the bijection, and the
   inclusion of `H₁`. Hence `w = 0`.
4. The classes `[x_j]` are `κ₀`-independent in `𝔪₀/𝔪₀²`. So a left inverse
   `g : 𝔪₀/𝔪₀² → (ι →₀ κ₀)` of `c ↦ ∑ c_j [x_j]` exists
   (`LinearMap.exists_leftInverse_of_injective`).
5. Apply `(κ₀ → κ) ∘ (i-th coordinate) ∘ g ∘ θ₀`, base-changed to `κ`, to `w = 0`. This gives
   `ā_i = 0`.

The statement and proof are original to this formalization. Hypotheses 1 and 2 are the inputs
used in the Stacks proof of 07E6: 07E5 (1) ⇒ (3), and the first map of 07E2.

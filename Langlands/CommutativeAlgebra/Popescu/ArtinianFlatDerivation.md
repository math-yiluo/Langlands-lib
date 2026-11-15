# Approximating derivations of `k` by derivations of `κ` (for Stacks Lemma 11.1)

This module supports the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.1
(Tag 07FG), in `ArtinianFlatSubalgebra`. All declarations are in the namespace
`Langlands.CommutativeAlgebra.Popescu.ArtinianFlat`. It formalizes the paragraph of the
source that uses the Jacobi-Zariski sequence and `dim H₁(L_{K/k}) < ∞`.

Absolute differentials are taken over `ℤ` (`Ω[k⁄ℤ]`). For rings of characteristic `p` they
equal differentials over `𝔽_p`, but `ℤ` avoids an `𝔽_p`-algebra structure.

## Declarations

- `fg_ker_mapBaseChange h`: if `H₁(L_{κ/k})` (`Algebra.H1Cotangent k κ`) is a finite
  `κ`-module, then the kernel of `κ ⊗_k Ω_{k/ℤ} → Ω_{κ/ℤ}`
  (`KaehlerDifferential.mapBaseChange ℤ k κ`) is finitely generated. By
  `Algebra.H1Cotangent.exact_δ_mapBaseChange`, this kernel is the image of `H₁(L_{κ/k})`
  under `δ`. This is the exact segment `H₁(L_{κ/k}) → Ω_{k} ⊗ κ → Ω_{κ}` of the
  Jacobi-Zariski sequence used in the source.
- `exists_derivation_approx hV θ`: let `I` be a `κ`-module (compatibly a `k`-module) and
  `θ : k → I` a derivation. If the kernel above is finitely generated, then there are a
  derivation `D : κ → I` and a finite set `S ⊆ I` with `θ a − D a ∈ span_k S` for all
  `a ∈ k`.
  **Proof.**
  1. Let `b` be a `k`-basis of `Ω_{k/ℤ}` (the source's `d y_j`). Then `1 ⊗ b` is a `κ`-basis
     of `κ ⊗_k Ω_{k/ℤ}`.
  2. Let `J₀` be the finite set of indices occurring in the basis expansions of finitely many
     generators of the kernel. The kernel lies in the span of `1 ⊗ b_j`, `j ∈ J₀`.
  3. Hence the images `φ(1 ⊗ b_j)` in `Ω_{κ/ℤ}`, `j ∉ J₀`, are linearly independent
     (`LinearIndependent.map` and a disjointness argument). This matches the source: "the
     elements `d y_j`, `j ∈ J ∖ J₀` map to `K`-linearly independent elements of `Ω_{K/𝔽_p}`".
  4. Let `ξ : κ ⊗_k Ω_{k/ℤ} → I` be the `κ`-linear extension of `θ`. Define `ℓ` on the span
     of these images by `ℓ(φ(1 ⊗ b_j)) = ξ(1 ⊗ b_j)` (`Basis.constr`). Extend it to
     `ℓ : Ω_{κ/ℤ} → I` (`LinearMap.exists_extend`), and set `D = ℓ ∘ d`.
  5. The `k`-linear map `η = (ξ − ℓ φ)(1 ⊗ ·)` vanishes on `b_j` for `j ∉ J₀`, and
     `θ a − D a = η(d a)`. So `θ a − D a` lies in the `k`-span of `S = {η(b_j) : j ∈ J₀}`.
     This is the source's `θ − D|_k = ξ ∘ d` with `ξ` factoring through `⊕_{j ∈ J₀} k d y_j`.
- `exists_derivation_approx' hV θ hadd hmul`: the same for a map `θ : k → I` that is additive
  and satisfies the Leibniz rule for the `κ`-module structure. It puts the compatible `k`-module
  structure on `I`. The conclusion has explicit coefficients:
  `θ a − D a = Σ_{s ∈ S} c_s • s` with `c_s ∈ k`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), proof of Lemma 11.1 (Tag 07FG, printed
p. 26): "Choose a set of elements `{y_j}` of `k` whose differentials `d y_j` form a basis of
`Ω_{k/𝔽_p}`. The Jacobi-Zariski sequence … As `dim H₁(L_{K/k}) < ∞` we can find a finite
subset `J₀ ⊂ J` … Therefore we can choose a `D : K → I` such that `θ − D|_k = ξ ∘ d`".

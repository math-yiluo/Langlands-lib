# Cyclic base change for `GL_n` at a split place

The module `Langlands.BaseChange.SplitPlace` (namespace `Langlands.BaseChange`) provides the
objects for cyclic base change of `GL_n` at a place where the cyclic extension splits
completely, so that the local algebra is `F^l = Fin l → F`. It defines the cyclic shift of
`F^l`, convolution products of test functions, a condition on Haar measures that
characterizes the product Haar measure on `GL_n(F^l)`, the representation `π ⊗ ⋯ ⊗ π` of
`GL_n(F^l)` and the cyclic shift of tensor factors. It proves the defining formulas, an
intertwining identity and that `F^{l+1}` with its shift is a cyclic algebra. Every proof is
complete; nothing in this module is assumed.

## Sources

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14). Cited as AC. Chapter 1, §5 (printed pp. 48–49): the action
  `σ(x₁, …, x_m) = (x₂, …, x_m, x₁)` of `σ` on `E = E₁ × ⋯ × E₁`, the σ-centralizer
  equations (5.1), the change of variables (5.2) and the convolution product
  `φ₁ * φ₂ * ⋯ * φ_m` matched with `φ₁ ⊗ ⋯ ⊗ φ_m`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL. I.2.1 (printed pp. 10–11): cyclic
  `F`-algebras; II.1.3 (printed p. 56): `Π^σ = (g ↦ Π(g^σ))` and isomorphisms `A` of `Π` onto
  `Π^σ`, `A ∘ Π(g) = Π(g^σ) ∘ A`; II.2.8 (printed pp. 67–68): the identification
  `G(E) = G(E₁)^r` and the map `φ ↦ φ*` sending `φ₁ ⊗ ⋯ ⊗ φ_r` to `φ₁ * ⋯ * φ_r`;
  II.2.15 (printed pp. 76–77): the split case `E₁ = F`, `δ^σ = (δ₂, …, δ_d, δ₁)`, the tensor
  power `Π = π^{⊗d}` on `V^{⊗d}` and `dg_E = (dg)^d`.

## Setting and the split convention

`GL_n(R)` is the Library's `GeneralLinear n R` (`Matrix.GeneralLinearGroup (Fin n) R`) and
`F^l` is `Fin l → F` with the product `F`-algebra structure. The cyclic shift is
`(σ x) i = x (i + 1)`, indices modulo `l`. This is AC's convention (Chapter 1, §5, printed
p. 48: `σ(x₁, …, x_m) = (x₂, …, x_m, x₁)`) and HL's (II.2.15, printed p. 76:
`δ^σ = (δ₂, …, δ_d, δ₁)`), written with indices `0, …, l - 1`. With it, the norm
`N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}` of `δ = (δ₀, …, δ_{l-1})` has first component
`δ₀ δ₁ ⋯ δ_{l-1}`; every `γ ∈ GL_n(F)` is a norm (take `δ = (γ, 1, …, 1)`); and the split
tensor `φ₀ ⊗ ⋯ ⊗ φ_{l-1}` is matched with the convolution product `φ₀ * ⋯ * φ_{l-1}`, in this
order (AC (5.1)–(5.2); HL II.2.8). These consequences are explanations of the convention; this
module proves none of them, and the matching is `SplitMatchingStatement`.

**`GL_n(F^l) = GL_n(F)^l` is never constructed.** HL and AC write `G(E) = G(F)^d`. The Lean
code never builds an isomorphism `GL_n(F^l) ≃ GL_n(F)^l` nor a product measure. Instead the
`i`-th component of `g : GL_n(F^l)` is its image
`Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i) g` under the `i`-th
coordinate ring homomorphism `F^l → F`; items 3–5 and `splitTensor` (`Langlands.BaseChange.CuspForm`)
use only these components.

## Definitions

1. `splitCyclicShift F l : (Fin l → F) ≃ₐ[F] (Fin l → F)`, for a commutative semiring `F` and
   `l : ℕ`, is Mathlib's `AlgEquiv.piCongrLeft' F (fun _ : Fin l => F) (finRotate l).symm`.
   Mathlib's `finRotate l` sends `i` to `i + 1` modulo `l`, and
   `splitCyclicShift F l x i = x (finRotate l i)` holds by `rfl` (lemma
   `splitCyclicShift_apply`). This is the split convention above.
2. `convolutionProduct μ φ`, for a group `G` with `[TopologicalSpace G] [IsTopologicalGroup G]
   [MeasurableSpace G] [BorelSpace G]`, a measure `μ` on `G` with
   `[IsFiniteMeasureOnCompacts μ]`, `l : ℕ` implicit and `φ : Fin (l + 1) → SchwartzBruhat G`,
   is the test function `φ 0 * (φ 1 * (⋯ * φ l))`, where `*` is the Library's
   `Hecke.TestFunction.convolution μ`, `(f * g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)`. It is defined by
   recursion on `l`: `φ 0` for `l = 0`, and `convolution μ (φ 0) (convolutionProduct μ
   (Fin.tail φ))` for `l + 1`. This is AC's `φ₁ * φ₂ * ⋯ * φ_m` (printed p. 49) and HL's
   `φ*` of a split tensor (II.2.8), with the convolution taken for the supplied measure `μ`.
   The measure is an explicit argument; nothing is chosen.
3. `IsSplitProductHaar μF μE : Prop`, for a commutative ring `F` with
   `[TopologicalSpace F] [IsTopologicalRing F]`, `n l : ℕ` implicit, σ-algebras on
   `GL_n(F)` and `GL_n(F^l)` as instance arguments, `μF` on `GL_n(F)` and `μE` on
   `GL_n(F^l)`: for every `ψ : Fin l → SchwartzBruhat (GL_n(F))`,
   `∫ g, splitTensor (fun i => ψ i) g ∂μE = ∏ i, ∫ g, ψ i g ∂μF`, where
   `splitTensor ψ` (`Langlands.BaseChange.CuspForm`) is `g ↦ ∏ i, ψ i (g_i)`.
   - *Meaning.* Under `GL_n(F^l) = GL_n(F)^l`, the product measure `μF ⊗ ⋯ ⊗ μF` integrates
     `ψ₀ ⊗ ⋯ ⊗ ψ_{l-1}` to `∏ i, ∫ ψ i dμF` (Fubini), so the condition says that `μE` behaves
     like that product measure on split tensors: HL II.2.15's normalization `dg_E = (dg)^d`.
   - *Why integrals of split tensors.* Stating the condition through integrals avoids building
     the identification `GL_n(F^l) = GL_n(F)^l` and a product measure, which only proofs would
     need. Among Haar measures it still pins `μE` down (an explanation, not proved here): two
     Haar measures on `GL_n(F^l)` differ by a positive scalar `c`, and for a nonarchimedean
     local field there are `ψ i` (indicator functions of a compact open subgroup) whose
     integrals are positive and finite, so `IsSplitProductHaar μF μE` and
     `IsSplitProductHaar μF (c • μE)` together force `c = 1`.
4. `splitTensorRep ρ`, for a commutative ring `F`, `n l : ℕ` implicit, a complex vector
   space `V` and `ρ : Representation ℂ (GL_n(F)) V`, is the representation of `GL_n(F^l)` on
   Mathlib's tensor power `⨂[ℂ] _ : Fin l, V` (`PiTensorProduct`) given by
   `g ↦ ρ(g₀) ⊗ ⋯ ⊗ ρ(g_{l-1})`, with `g_i` the `i`-th component. In Lean it is
   `PiTensorProduct.mapMonoidHom` composed with the product
   `MonoidHom.pi fun i => ρ.comp (Matrix.GeneralLinearGroup.map (Pi.evalRingHom _ i))` of the
   component maps. Under `GL_n(F^l) = GL_n(F)^l` it is the representation `ρ ⊗ ⋯ ⊗ ρ` of
   `GL_n(F)^l`, HL's `Π = π^{⊗d}` on `V^{⊗d}` (II.2.15).
5. `splitTensorShift V l : (⨂[ℂ] _ : Fin l, V) ≃ₗ[ℂ] (⨂[ℂ] _ : Fin l, V)` is Mathlib's
   `PiTensorProduct.reindex ℂ (fun _ : Fin l => V) (finRotate l).symm`, which sends
   `v₀ ⊗ v₁ ⊗ ⋯ ⊗ v_{l-1}` to `v₁ ⊗ ⋯ ⊗ v_{l-1} ⊗ v₀` (lemma `splitTensorShift_tprod`).
   - *Relation to HL.* HL II.2.15 (printed p. 76) use the operator
     `A(v₁ ⊗ ⋯ ⊗ v_d) = v_d ⊗ v₁ ⊗ ⋯ ⊗ v_{d-1}` and write `Π(δ^σ) = A⁻¹ ∘ Π(δ) ∘ A`. The
     condition of HL II.1.3 (printed p. 56) for an isomorphism of `Π` onto `Π^σ`, which
     `SigmaIntertwiner` (`Langlands.BaseChange.TwistedCharacter`) formalizes, is `A ∘ Π(g) = Π(g^σ) ∘ A`. The inverse of
     HL's operator in II.2.15 satisfies it; `splitTensorShift` is that inverse, and lemma
     `splitTensorShift_comp` proves the condition.

## Lemmas (all proved)

- `splitCyclicShift_apply`: `splitCyclicShift F l x i = x (finRotate l i)` (by `rfl`).
- `splitCyclicShift_pow_apply`: `(splitCyclicShift F l ^ k) x i = x ((finRotate l ^ k) i)`,
  by induction on `k`.
- `finRotate_succ_pow_apply`: `(finRotate (l + 1) ^ k) i = i + (k : Fin (l + 1))` (with the
  cast of `k : ℕ` to `Fin (l + 1)` modulo `l + 1`), by induction on `k` using Mathlib's
  `finRotate_apply`.
- `isCyclicAlgebra_splitCyclicShift`: for a field `F` and `l : ℕ`,
  `IsCyclicAlgebra (splitCyclicShift F (l + 1)) (l + 1)` (the predicate of
  `Langlands.BaseChange.Norm`: finite,
  of dimension `l + 1`, reduced, `σ` of order `l + 1`, `σ`-fixed elements in `F`). Proof:
  finiteness, dimension (`Module.finrank_fin_fun`) and reducedness are instances; the order
  is `l + 1` by `orderOf_eq_iff`, since `σ^{l+1} = 1` by the two previous lemmas and, for
  `0 < m < l + 1`, `σ^m` moves `Pi.single 0 1` (its value at `0` is the value of
  `Pi.single 0 1` at `m ≠ 0`); a fixed `x` is the constant `x 0`, by `Fin.induction`, since
  `x (i + 1) = (σ x) i = x i`. For `l + 1` replaced by `0`, `F^0` is the zero ring and the
  shift has order `1`, so the lemma is stated for `l + 1`.
- `convolutionProduct_zero` (`convolutionProduct μ φ = φ 0` for `φ : Fin 1 → _`) and
  `convolutionProduct_succ` (`convolutionProduct μ φ = convolution μ (φ 0)
  (convolutionProduct μ (Fin.tail φ))` for `φ : Fin (l + 2) → _`), both by `rfl`.
- `splitTensorRep_tprod`: `splitTensorRep ρ g (tprod ℂ v) = tprod ℂ (fun i => ρ (g_i) (v i))`.
- `splitTensorShift_tprod`:
  `splitTensorShift V l (tprod ℂ v) = tprod ℂ (fun i => v (finRotate l i))`.
- `map_evalRingHom_entrywiseAut_splitCyclicShift`: the `i`-th component of
  `entrywiseAut (splitCyclicShift F l) n g` (the `g^σ` of `Langlands.BaseChange.Norm`) is the
  `finRotate l i`-th component of `g` (by extensionality and `rfl`).
- `splitTensorShift_comp`: for every `g : GL_n(F^l)`,
  `(splitTensorShift V l).toLinearMap ∘ₗ splitTensorRep ρ g =
  splitTensorRep ρ (entrywiseAut (splitCyclicShift F l) n g) ∘ₗ
  (splitTensorShift V l).toLinearMap`. Both sides agree on pure tensors by the three previous
  lemmas, and `PiTensorProduct.ext` concludes. So `splitTensorShift` is an isomorphism of
  `splitTensorRep ρ` onto its twist `g ↦ splitTensorRep ρ (g^σ)`, as `SigmaIntertwiner`
  requires; `SplitSigmaLiftStatement` uses it as the intertwiner of constant `1`.

## Dependencies and names

The module imports `Langlands.BaseChange.Norm` (`entrywiseAut`,
`IsCyclicAlgebra`), `Langlands.BaseChange.CuspForm` (`splitTensor`) and the
Library's `Langlands.Representation.Hecke.Convolution` (`Hecke.TestFunction.convolution`,
`HarmonicAnalysis.SchwartzBruhat`). All names are used as published, with the argument orders
of those modules.

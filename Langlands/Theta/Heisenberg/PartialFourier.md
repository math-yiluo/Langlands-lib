# The partial Fourier transform between two Schrödinger models

**GKT §1.2.5** (the polarizations `(X₁ ⊕ Z) ⊕ (Y₁ ⊕ Z*)` and `(Y₁ ⊕ Z) ⊕ (X₁ ⊕ Z*)`, p. 34;
**Theorem 1.27** and **Remark 1.28**, p. 35).

The module `Langlands.Theta.Heisenberg.PartialFourier` defines the Schrödinger model of a
partially swapped polarization and proves that the partial Fourier transform intertwines it with
the Schrödinger model of the original polarization and is unitary. It also holds the orthogonal sum
of two pairings and the tensor of two Schwartz–Bruhat functions, which the blocks of
`Langlands.Theta.Metaplectic.Block` use.

## Content

**Tensors.** `schwartzBruhatTensor φ₁ φ₂ = φ₁ ⊗ φ₂`, `(x₁, x₂) ↦ φ₁(x₁) φ₂(x₂)`, a
Schwartz–Bruhat function on `X₁ × X₂`; `schwartzBruhatTensor_smul`;
`schwartzBruhatInner_tensor`: `⟨φ₁ ⊗ φ₂, φ₁' ⊗ φ₂'⟩ = ⟨φ₁, φ₁'⟩ ⟨φ₂, φ₂'⟩` for product measures.

**Orthogonal sums.** For pairings `β₁ : X₁ × Y₁ → R`, `β₂ : X₂ × Y₂ → R`:

- `sumPairing β₁ β₂ ((x₁, x₂), (y₁, y₂)) = β₁(x₁, y₁) + β₂(x₂, y₂)`;
  `polarizedForm_sumPairing`: the form of `W₁ ⊕ W₂` is the sum of the forms;
  `isPerfPair_sumPairing`: the sum of perfect pairings is perfect (an instance).
- `polarizedForm_partialSwap`, `partialSwapHeisenbergEquiv β₁ β₂`: the partial swap
  `((x₁, x₂), (y₁, y₂)) ↦ ((y₁, x₂), (x₁, y₂))` is an isomorphism of Heisenberg groups from
  `sumPairing β₁ β₂` to `sumPairing (-β₁.flip) β₂`. In the book's notation, with `X = X₁ ⊕ Z`,
  `Y = Y₁ ⊕ Z` and `Z*` a complement, the first polarization is `(X₁ ⊕ Z) ⊕ (Y₁ ⊕ Z*)` and the
  second `(Y₁ ⊕ Z) ⊕ (X₁ ⊕ Z*)` (the Library's `X₂ × Y₂` is the book's `Z ⊕ Z*`, and its model on
  `S(X₁ × X₂)` is the book's `C_c^∞(Y₁ ⊕ Z*)`, as in `Langlands.Theta.Heisenberg.SchrodingerFourier`).

**The partial Fourier transform of a perfect bicharacter** `α : X₁ × Y₁ → ℂ¹` (GKT Appendix 1.A):

- `partialPairingFourier μ α φ (y₁, x₂) = ∫ α(x₁, y₁) φ(x₁, x₂) dμ(x₁)`;
  `partialPairingFourier_apply`: in each `x₂` it is the Fourier transform `pairingFourier`.
- `partialPairingFourier_mem`: it preserves Schwartz–Bruhat functions. It is locally constant in
  `y₁` uniformly on the compact projection of the support of `φ`, and in `x₂` by the invariance of
  `φ` under small translations. Its support lies in `K × pr₂(supp φ)`, where `K` is the compact set
  of `y₁` on which `α(·, y₁)` is trivial on a neighbourhood of `0` fixing `φ`.
- `lintegral_enorm_partialPairingFourier_sq`: an isometry from `L²(μ × ν)` to `L²(μ' × ν)` for the
  dual measure `μ'` and every s-finite `ν` (Plancherel in `x₁` for each `x₂`, then Tonelli).
- `partialPairingFourier_tensor`: **Remark 1.28**, `ℱ(φ₁ ⊗ φ₂) = ℱφ₁ ⊗ φ₂`.

**Theorem 1.27.** Over a nonarchimedean local field with `2 ≠ 0`, for finite-dimensional spaces
with their module topologies, `β₁` perfect and `ψ` continuous and non-trivial:

- `schrodingerSBPartial hψ`: the Schrödinger model on `S(Y₁ × X₂)` of the partially swapped
  polarization, read through `partialSwapHeisenbergEquiv`. The element
  `(((x₀₁, x₀₂), (y₀₁, y₀₂)), t)` acts by
  `f ↦ ((y₁, x₂) ↦ ψ(t - β₁(x₀₁, y₁) + β₂(x₂, y₀₂) + ½(-β₁(x₀₁, y₀₁) + β₂(x₀₂, y₀₂)))
  f(y₁ + y₀₁, x₂ + x₀₂))` (`schrodingerSBPartial_apply`).
- `schrodingerPartialFourier β₁ hψ hψ1 μ`: **`F_{Y₁, X₁}`**,
  `φ ↦ ((y₁, x₂) ↦ ∫ ψ(β₁(x₁, y₁)) φ(x₁, x₂) dμ(x₁))`.
- `schrodingerPartialFourier_schrodinger`: **it intertwines** the Schrödinger model of
  `sumPairing β₁ β₂` on `S(X₁ × X₂)` with `schrodingerSBPartial` (translate `x₁` by `-x₀₁`, as in
  Theorem 1.25).
- `lintegral_enorm_schrodingerPartialFourier_sq`: **it is unitary** from `μ × ν` to `μ' × ν`.
- `schrodingerPartialFourier_tensor`: **Remark 1.28**, on `φ₁ ⊗ φ₂` it is
  `schrodingerFourier φ₁ ⊗ φ₂`.

The book leaves the proof of Theorem 1.27 to the reader. Its kernel `ψ(⟨y₁, x₁⟩)` is
`ψ(β₁(x₁, y₁))` here, with the same dictionary as Theorem 1.25.

## Declarations

- `schwartzBruhatTensor`, `schwartzBruhatTensor_apply`, `schwartzBruhatTensor_smul`,
  `schwartzBruhatInner_tensor`.
- `sumPairing`, `sumPairing_apply`, `polarizedForm_sumPairing`, `polarizedForm_partialSwap`,
  `partialSwapHeisenbergEquiv`, `partialSwapHeisenbergEquiv_apply`, `isPerfPair_sumPairing`.
- `partialPairingFourier`, `partialPairingFourier_apply`, `partialPairingFourier_tensor`,
  `partialPairingFourier_mem`, `lintegral_enorm_partialPairingFourier_sq`.
- `continuous_sumPairing_left`, `continuous_sumPairing_neg_flip_left`, `schrodingerSBPartial`,
  `schrodingerSBPartial_apply`, `schrodingerPartialFourier`, `schrodingerPartialFourier_apply`,
  `schrodingerPartialFourier_schrodinger`, `lintegral_enorm_schrodingerPartialFourier_sq`,
  `schrodingerPartialFourier_tensor`.

All in the name space `Langlands.HeisenbergGroup`.

## Dependencies

`Langlands.Theta.Heisenberg.SchrodingerFourier`.

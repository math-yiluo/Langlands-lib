# Hartogs's theorem on separate holomorphy

Module `Langlands.Analysis.SeveralComplex.Hartogs.Basic` proves Hartogs's
theorem on separate holomorphy for products of open subsets of
finite-dimensional complex normed spaces. It also proves the diagonal form
used by the principle of meromorphic continuation
(`Langlands.Analysis.Meromorphic.HartogsDiagonal`). The module reduces
everything to the case `E × ℂ`, `differentiableOn_prod_complex_of_separately`
of `Langlands.Analysis.SeveralComplex.Hartogs.BaireStep`, by induction on the
dimension of the second factor.

All functions take values in `ℂ`. "Holomorphic" means `DifferentiableOn ℂ`.
`f` is *separately holomorphic* on `U₁ ×ˢ U₂` if
`z ↦ f (z, w)` is holomorphic on `U₁` for every `w ∈ U₂` and `w ↦ f (z, w)` is
holomorphic on `U₂` for every `z ∈ U₁`.

## Provenance

Hartogs's theorem is classical (F. Hartogs, 1906). Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024),
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, use
it in §3.2 (p.193; TeX `1911.02342.tex` lines 665–669). For the theorem they
cite S. G. Krantz, *Function theory of several complex variables*, §0.2 and
Theorem 1.2.5. The reduction to one extra complex variable by induction is the
standard one. The formulation for products of open sets and the transfer along
continuous linear equivalences are internal to the Lean proof.

## Results

Throughout, `E₁`, `E₂` and `E₂'` are complex normed spaces.

- `differentiableOn_comp_prodMap`: if `f : E₁ × E₂ → ℂ` is holomorphic on
  `U₁ ×ˢ U₂` and `L : E₂' →L[ℂ] E₂`, then `p ↦ f (p.1, L p.2)` is holomorphic on
  `U₁ ×ˢ L ⁻¹' U₂`. This is composition with the continuous linear map
  `(z, w) ↦ (z, L w)`.
- `differentiableOn_of_comp_equiv`: for a continuous linear equivalence
  `e : E₂' ≃L[ℂ] E₂`, if `p ↦ f (p.1, e p.2)` is holomorphic on
  `U₁ ×ˢ e ⁻¹' U₂`, then `f` is holomorphic on `U₁ ×ˢ U₂`. Apply the previous
  item with `L = e.symm` and use `e (e.symm w) = w`.
- `differentiableOn_prod_of_subsingleton`: if `E₂` has at most one point and
  `z ↦ f (z, w)` is holomorphic on `U₁` for every `w ∈ U₂`, then `f` is
  holomorphic on `U₁ ×ˢ U₂`. Near a point `p`, `f q = f (q.1, p.2)`.
- `differentiableOn_prod_complex_prod` (the induction step). Assume two
  hypotheses: `IH`, that separate holomorphy implies holomorphy on products of
  open sets in `E₁ × E₂`; and `hA`, the same for `(E₁ × E₂) × ℂ`. Then the same
  holds for `E₁ × (ℂ × E₂)`.

  Proof: let `f` be separately holomorphic on `U₁ ×ˢ V`, with `V ⊆ ℂ × E₂` open,
  and let `p = (z₀, (t₀, w₀)) ∈ U₁ ×ˢ V`. Choose open `D ∋ t₀` and `B' ∋ w₀` with
  `D ×ˢ B' ⊆ V`, and put `g ((z, w), t) = f (z, (t, w))`. For fixed `t ∈ D`, the
  map `(z, w) ↦ g ((z, w), t)` is separately holomorphic on `U₁ ×ˢ B'`, hence
  holomorphic by `IH`. For fixed `(z, w) ∈ U₁ ×ˢ B'`, the map `t ↦ g ((z, w), t)`
  is holomorphic on `D`. By `hA`, `g` is holomorphic on the open set
  `(U₁ ×ˢ B') ×ˢ D`. Then `f = g ∘ φ` with the continuous linear map
  `φ (z, (t, w)) = ((z, w), t)`, and `φ p` lies in that open set, so `f` is
  differentiable at `p`.
- `differentiableOn_prod_pi_of_separately`: for every `n` and every
  finite-dimensional `E₁` (in a fixed universe), a function on
  `E₁ × (Fin n → ℂ)` that is separately holomorphic on a product of open sets
  is holomorphic there.

  Proof by induction on `n`, with `E₁` varying. The case `n = 0` is the
  subsingleton case. For `n + 1`, transfer along the continuous linear
  equivalence `ℂ × (Fin n → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)` given by `Fin.cons`
  (`Fin.consLinearEquiv`). Then apply the induction step with `E₂ = Fin n → ℂ`,
  with `IH` the induction hypothesis for `E₁`, and with `hA` the case `E × ℂ`
  (`differentiableOn_prod_complex_of_separately`) for the finite-dimensional
  space `E = E₁ × (Fin n → ℂ)`.
- `differentiableOn_prod_of_separately` (Hartogs's theorem). Let `E₁` and `E₂`
  be finite-dimensional, `U₁ ⊆ E₁` and `U₂ ⊆ E₂` open, and `f : E₁ × E₂ → ℂ`
  separately holomorphic on `U₁ ×ˢ U₂`. Then `f` is holomorphic on `U₁ ×ˢ U₂`.
  Proof: transfer along the coordinate isomorphism
  `(Fin (finrank ℂ E₂) → ℂ) ≃L[ℂ] E₂` of a basis (`Module.finBasis`), and apply
  the previous item.
- `differentiableOn_diag_of_separately` (diagonal form). Let `E` be
  finite-dimensional, `U ⊆ E` open, and `G : E → E → ℂ`. Suppose
  `s ↦ G s t` is holomorphic on `U` for every `t ∈ U`, and `G s` is holomorphic
  on `U` for every `s ∈ U`. Then `s ↦ G s s` is holomorphic on `U`. Proof: apply
  Hartogs's theorem to `(s, t) ↦ G s t` on `U ×ˢ U`, and compose with the
  diagonal map `s ↦ (s, s)`, which maps `U` into `U ×ˢ U`.

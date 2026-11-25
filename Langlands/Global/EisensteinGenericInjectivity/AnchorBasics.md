# Regular lines and holomorphy of Eisenstein series along lines

Module `Langlands.Global.EisensteinGenericInjectivity.AnchorBasics` studies the Eisenstein
series `hK.eisensteinSeries φ λ g` (module `Langlands.Global.AdelicEisensteinSeries`) along the
complex line `λ + z μ`, `μ = 1 ⊗ χ` for a rational character `χ` of `P`: each term is multiplied
by an exponential of its height, regularity depends only on `Re z`, and, given summable
majorants uniform on compact sets of regular parameters, the series is holomorphic in `z`. The
module `Langlands.Global.EisensteinGenericInjectivity.Anchor` uses these facts.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`. Notation: `X_P = ComplexCharacterParameter F P = X^*(P) ⊗ ℂ`, `H_P(x)(χ) = hK.height x χ`,
`out(c)` the chosen representative in `G(F)` of a coset `c ∈ P(F) \ G(F)`. Complete types are
printed by `PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the page of
`Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `eisensteinTerm_add_smul`: shifting the parameter `λ` by `z • (1 ⊗ χ)` multiplies the
  Eisenstein term at the coset `c` by `exp(z · H_P(out(c) · g)(χ))`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.eisensteinTerm_add_smul.{u} {F : Type u} [Field F]
    [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} {p : P ⟶ G}
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) (χ : P.rationalCharacters) (z : ℂ)
    (g : AdelicGroupPoints F G) (c : ParabolicRationalCosets F p) :
    hK.eisensteinTerm φ (lam + z • 1 ⊗ₜ[ℤ] χ) g c =
      hK.eisensteinTerm φ lam g c * Complex.exp (z * ↑((hK.height (↑(Quotient.out c) * g)) χ))
  ```
- `parameterRealPart_add_smul`: the real part of `λ + z • (1 ⊗ χ)` is
  `Re λ + (Re z) • (1 ⊗ χ)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.parameterRealPart_add_smul.{u} {F : Type u} [Field F]
    {P : Langlands.GroupScheme (Spec ↧F)} (lam : ComplexCharacterParameter F P)
    (χ : P.rationalCharacters) (z : ℂ) :
    (parameterRealPart F P) (lam + z • 1 ⊗ₜ[ℤ] χ) = (parameterRealPart F P) lam + z.re • 1 ⊗ₜ[ℤ] χ
  ```
- `isRegularParameter_add_smul_iff`: hence `λ + z • (1 ⊗ χ)` is `R`-regular if and only if
  `λ + (Re z) • (1 ⊗ χ)` is.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.isRegularParameter_add_smul_iff.{u} {F : Type u}
    [Field F] {G P : Langlands.GroupScheme (Spec ↧F)} {p : P ⟶ G}
    {M : Langlands.GroupScheme (Spec ↧F)} {A : Langlands.CommGroupScheme (Spec ↧F)}
    [IsAffineHom G.X.hom] {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono (Over.Hom.left r.data.i.hom.hom)] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (Over.Hom.left (Langlands.CommGroupScheme.groupHom r.data.f).hom.hom)]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (R : ℝ)
    (lam : ComplexCharacterParameter F P) (χ : P.rationalCharacters) (z : ℂ) :
    r.IsRegularParameter hA hT R (lam + z • 1 ⊗ₜ[ℤ] χ) ↔
      r.IsRegularParameter hA hT R (lam + ↑z.re • 1 ⊗ₜ[ℤ] χ)
  ```
- `differentiableOn_eisensteinSeries_line` (**holomorphy along lines**): suppose the Eisenstein
  terms of `φ` have summable majorants uniform for `g` in a compact set and `s` in a compact set
  of parameters that are `R`-regular in a chart `e : ℂⁿ ≃ X_P` (the form of the conclusion of
  `EisensteinAbsoluteConvergenceStatement`, proved as
  `Langlands.Global.eisensteinAbsoluteConvergence`). Then `z ↦ E(φ, e(s₀ + z v))(g)` is
  holomorphic on every open set of `z` on which these parameters are `R`-regular.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.differentiableOn_eisensteinSeries_line.{u}
    {F : Type u} [Field F] [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} {p : P ⟶ G}
    {K : Subgroup (AdelicGroupPoints F G)} {M : Langlands.GroupScheme (Spec ↧F)}
    {A : Langlands.CommGroupScheme (Spec ↧F)} [IsAffineHom G.X.hom] {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) [Mono (Over.Hom.left r.data.i.hom.hom)]
    [Fintype (relativeWeylGroup r.data.i)]
    [Mono (Over.Hom.left (Langlands.CommGroupScheme.groupHom r.data.f).hom.hom)]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hK : IsIwasawaCompact p K) (R : ℝ)
    (φ : AdelicGroupPoints F G → ℂ)
    (hconv :
      ∀ (C : Set (AdelicGroupPoints F G)),
        IsCompact C →
          ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (Λ : Set (Fin n → ℂ)),
            IsCompact Λ →
              (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
                ∃ b,
                  Summable b ∧
                    ∀ (c : ParabolicRationalCosets F p),
                      ∀ g ∈ C, ∀ s ∈ Λ, ‖hK.eisensteinTerm φ (e s) g c‖ ≤ b c)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ v : Fin n → ℂ) {S : Set ℂ}
    (hS : IsOpen S) (hreg : ∀ z ∈ S, r.IsRegularParameter hA hT R (e (s₀ + z • v)))
    (g : AdelicGroupPoints F G) :
    DifferentiableOn ℂ (fun z => hK.eisensteinSeries φ (e (s₀ + z • v)) g) S
  ```

## Proofs

- `eisensteinTerm_add_smul`: the term is `φ(γ g) exp⟨λ, H_P(γ g)⟩` and the pairing is linear
  in `λ`, with `⟨1 ⊗ χ, H⟩ = H(χ)` (`complexParameterPairing_tmul`).
- `differentiableOn_eisensteinSeries_line`: on a closed ball around `z₀` inside the open set,
  the parameters `e(s₀ + z v)` form a compact set of `R`-regular parameters, so the hypothesis
  gives one summable majorant. Each term is `φ(γ g)` times the exponential of an affine
  function of `z`, hence entire, and `Complex.differentiableOn_tsum_of_summable_norm` gives
  holomorphy of the sum on the open ball.

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), §2.2, printed p. 191: the series (2.1), `E(g, φ, λ) = ∑_γ φ_λ(γ g)` with
`φ_λ(g) = φ(g) m_P(g)^λ`, converges absolutely and locally uniformly in `g` and `λ` for `Re λ`
sufficiently regular; §2.1, printed p. 190, for `X_P = X^*(M) ⊗ ℂ` and `m_P`. The holomorphy
along lines is the consequence of that locally uniform convergence used here.

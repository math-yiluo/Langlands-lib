# A regular parameter at which Eisenstein series of independent forms are independent

Module `Langlands.Global.EisensteinGenericInjectivity.Anchor` proves
`exists_regular_det_ne_zero`: for linearly independent, continuous, left
`U(𝔸)M(F)`-invariant functions `ψ_1, …, ψ_m` on `G(𝔸)` whose Eisenstein terms have summable
majorants uniform on compact sets of `R`-regular parameters, every nonempty open set of
`R`-regular parameters in a chart contains a parameter `λ` and points `g_1, …, g_m` with
`det(E(ψ_k, λ)(g_i)) ≠ 0`. The proof of `Langlands.Global.eisensteinGenericInjectivity`
(module `Langlands.Global.AdelicEisensteinGenericInjectivityProof`) starts from this parameter.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`. Notation as on the page of `Langlands.Global.EisensteinGenericInjectivity.AnchorBasics`;
`E(ψ, λ)(g) = hK.eisensteinSeries ψ λ g`. Complete types are printed by
`PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the page of
`Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `height_out_one_mul`: the chosen representative of the trivial coset lies in the image of
  `P(F)`, so it does not change the Iwasawa height (`IsIwasawaCompact.height_rational_mul`).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.height_out_one_mul.{u} {F : Type u} [Field F]
    [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion (Over.Hom.left p.hom.hom)] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (g : AdelicGroupPoints F G) : hK.height (↑⟦1⟧.out * g) = hK.height g
  ```
- `exists_regular_det_ne_zero` (**anchor**): let `G` be connected reductive, `iU` the
  geometric unipotent radical, `hK : IsIwasawaCompact p K`, `ψ : Fin m → (G(𝔸) → ℂ)` linearly
  independent, continuous and left invariant under `parabolicQuotientSubgroup F p iU l`, and
  `hconv` the majorant hypothesis for `R`. For every chart `e : ℂⁿ ≃ X_P` and every nonempty
  open `W ⊆ ℂⁿ` of points `s` with `e s` `R`-regular, there are `s ∈ W` and
  `g : Fin m → G(𝔸)` with `det(E(ψ_k, e s)(g_i)) ≠ 0`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exists_regular_det_ne_zero.{u} {F : Type u} [Field F]
    [NumberField F] {G P : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion (Over.Hom.left p.hom.hom)] {K : Subgroup (AdelicGroupPoints F G)}
    {M U : Langlands.GroupScheme (Spec ↧F)} {A : Langlands.CommGroupScheme (Spec ↧F)}
    [IsAffineHom G.X.hom] {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) [Mono (Over.Hom.left r.data.i.hom.hom)]
    [Fintype (relativeWeylGroup r.data.i)]
    [Mono (Over.Hom.left (Langlands.CommGroupScheme.groupHom r.data.f).hom.hom)]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : G.IsConnectedReductive)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hK : IsIwasawaCompact p K) {m : ℕ}
    (ψ : Fin m → AdelicGroupPoints F G → ℂ) (hcont : ∀ (k : Fin m), Continuous (ψ k))
    (hinv : ∀ (k : Fin m), IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (ψ k))
    (hind : LinearIndependent ℂ ψ) (R : ℝ)
    (hconv :
      ∀ (k : Fin m) (C : Set (AdelicGroupPoints F G)),
        IsCompact C →
          ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (Λ : Set (Fin n → ℂ)),
            IsCompact Λ →
              (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
                ∃ b,
                  Summable b ∧
                    ∀ (c : ParabolicRationalCosets F p),
                      ∀ g ∈ C, ∀ s ∈ Λ, ‖hK.eisensteinTerm (ψ k) (e s) g c‖ ≤ b c)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) {W : Set (Fin n → ℂ)}
    (hWo : IsOpen W) (hWne : W.Nonempty) (hWreg : ∀ s ∈ W, r.IsRegularParameter hA hT R (e s)) :
    ∃ s ∈ W, ∃ g, (Matrix.of fun i k => hK.eisensteinSeries (ψ k) (e s) (g i)).det ≠ 0
  ```

## Proof of `exists_regular_det_ne_zero`

1. The Library theorem `Langlands.Analysis.exists_profileMatrix_det_ne_zero` (module
   `Langlands.Analysis.HolomorphicFiniteRank`) gives points `g⁰_i` with `det(ψ_k(g⁰_i)) ≠ 0`.
2. `frequency_separation` (module `Langlands.Global.EisensteinGenericInjectivity.Separation`)
   gives a character `χ`. The ray parameters `s` at which some tuple of cosets other than the
   trivial one keeps the total height `∑_i H_P(ray(s) g⁰_i)(χ)` form a countable set: there are
   countably many tuples and each contributes a finite set. The function
   `s ↦ det(ψ_k(ray(s) g⁰_i))` is continuous (`continuous_ray`) and nonzero at `0` (`ray_zero`),
   so it is nonzero at some `s₀` outside the countable set. Put `g_i = ray(s₀) g⁰_i`.
3. Fix `s_W ∈ W`, `λ₀ = e(s_W)` and `v = e⁻¹(1 ⊗ χ)`. On the strip `S = {|Re z| < ε}` the
   parameters `e(s_W + z v)` are `R`-regular (`isRegularParameter_add_smul_iff`), and
   `f(z) = det(E(ψ_k, e(s_W + z v))(g_i))` is holomorphic: each entry by
   `differentiableOn_eisensteinSeries_line`, the determinant by the Library theorem
   `Langlands.Analysis.Meromorphic.mdifferentiableOn_det` (module
   `Langlands.Analysis.Meromorphic.LocalScalarization`).
4. For real `y`, `eisensteinTerm_add_smul` and `det_tsum` (module
   `Langlands.Global.EisensteinGenericInjectivity.ProductTsum`) give
   `f(iy) = ∑'_{cs} B(cs) exp(i y θ(cs))` over `m`-tuples of cosets, with
   `B(cs) = det(term(ψ_k, λ₀, g_i, cs_i))` absolutely summable (`summable_norm_det_pi`) and
   `θ(cs) = ∑_i H_P(out(cs_i) g_i)(χ)`. By step 2 the trivial tuple is the only one of frequency
   `∑_i H_P(g_i)(χ)` (`height_out_one_mul`). Its coefficient is
   `∏_i m_P(g_i)^{λ₀} · det(ψ_k(g_i)) ≠ 0`, by the Library lemma
   `IsIwasawaCompact.eisensteinTerm_eq_of_representative` (module
   `Langlands.Global.AdelicEisensteinRationalCosets`). `exists_shift_tsum_ne_zero` (module
   `Langlands.Global.EisensteinGenericInjectivity.Cesaro`) gives `y` with `f(iy) ≠ 0`.
5. If the determinant vanished at every point of `W` for these `g_i`, `f` would vanish near `0`,
   and the identity theorem on the convex strip
   (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) would give `f(iy) = 0`.

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), §2.2, printed p. 191, the series (2.1) and its absolute convergence for
`Re λ` sufficiently regular. The anchor is not taken from a source: Bernstein–Lapid obtain the
injectivity (8.4) from the constant term formula (6.17) of §6.10, printed p. 208, and the
argument of §8.5, printed pp. 224–225.

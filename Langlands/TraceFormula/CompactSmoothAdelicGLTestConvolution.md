# Dixmier–Malliavin on tensor test functions of `GL_n(𝔸_E)`

`Langlands.TraceFormula.CompactSmoothAdelicGLTestConvolution`. The factorization of a tensor test
function `a ⊗ b` of the Library's space `CompactSmoothAdelicGLTest E n` into convolutions whose
right-hand factors keep the finite component `b`. Namespace `Langlands.TraceFormula`.

## Statements

- `CompactSmoothAdelicGLTest.tensor_eq_sum_convolution`: for a number field `E`, `n : ℕ`, a Borel
  structure on `AdelicGL E n`, any left Haar measure `μ` on it, `a : ArchimedeanGL.SmoothCompactKernel
  E n`, `b : CompactFiniteGLTest E n` and a neighbourhood `U` of `1` in `InfiniteAdelicGL E n`, there
  are `m`, `α α' : Fin m → ArchimedeanGL.SmoothCompactKernel E n` and `e : CompactFiniteGLTest E n`
  with `tsupport (α i) ⊆ U`, `tsupport (α' i) ⊆ tsupport a`, and

  `adelicTestTensor E n a b g = ∑ i, ∫ y, adelicTestTensor E n (α i) e y *
    adelicTestTensor E n (α' i) b (y⁻¹ * g) ∂μ` for all `g`.

- `CompactFiniteGLTest.exists_compactOpen_leftInvariant`: every compactly supported locally constant
  `b` on `GL_n(𝔸_{E,f})` is left invariant under a compact open subgroup; this is
  `Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance` (`Langlands/Representation/Hecke`),
  with `finiteAdelicGL_t2Space`, `finiteAdelicGL_totallyDisconnectedSpace'` and the local compactness
  of `Langlands/Global/AdelicGLTopology`.
- `CompactFiniteGLTest.subgroupIndicator K hK`: the indicator of a compact open subgroup as a finite
  test.
- `finiteSliceMeasure μ K`, the measure `S ↦ μ({g : g_∞ ∈ S, g_f ∈ K})` on `GL_n(E_∞)`, and
  `isHaarMeasure_finiteSliceMeasure`: it is a left Haar measure when `μ` is one and `K` is a compact
  open subgroup (left invariance because `GL_n(E_∞)` acts on the first coordinate only; finiteness on
  compact sets because `{g_∞ ∈ C, g_f ∈ K}` is compact; positivity on open sets because `K` is open).

## Proof of the factorization

Take `K` compact open fixing `b` on the left and `e = 1_K`. For `y` with `y_f ∈ K`,
`b(y_f⁻¹ g_f) = b(g_f)`; for the other `y` the left factor vanishes. Hence
`((α ⊗ 1_K) ⋆_μ (α' ⊗ b))(g) = b(g_f) · ∫ α(z) α'(z⁻¹ g_∞) dν(z)` with `ν = finiteSliceMeasure μ K`. The
archimedean theorem `ArchimedeanGL.SmoothCompactKernel.exists_eq_sum_convolution` for the Haar
measure `ν` writes `a = ∑ αᵢ ⋆_ν α'ᵢ`, and summing gives `a ⊗ b`.

No comparison between `μ` and a product of Haar measures of the factors is needed, and `μ` may be
any left Haar measure (for instance the image of the Haar measure of the group-scheme points
`G(𝔸_E)`, `G = GL_n`, under the Library's identification).

## Why the finite component is kept

For the simple trace formula (`Langlands/TraceFormula/GeneralLinearSimpleTraceFormulaStatement`),
conditions imposed on the finite component of a test function at a finite place (vanishing of
unipotent integrals, regular ellipticity of the support) must pass to the factors of the
convolutions. Here every right-hand factor `α'ᵢ ⊗ b` has the finite component `b` of the original
tensor, and every product `(αᵢ ⊗ e) ⋆ (α'ᵢ ⊗ b)` has finite component `e ⋆ b = b`.

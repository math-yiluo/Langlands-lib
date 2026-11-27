# Levi parts of parabolic elements in a σ-regular twisted class

Module `Langlands.BaseChange.TwistedLocalDescent.Classification`.

- `charpoly_parabolic`: the characteristic polynomial of a block upper triangular element is the
  product of those of its diagonal blocks, i.e. of the blocks of its Levi part.
- `parabolicCyclicNorm σ B l p`: the norm `N(p) = p σ(p) ⋯ σ^{l-1}(p)` of a parabolic element, as
  a parabolic element; `leviProjection_parabolicCyclicNorm`: its Levi part is the blockwise norm of
  the Levi part of `p`.
- `charpoly_baseChange`: base change commutes with characteristic polynomials.
- `exists_levi_twistedConj_of_parabolic` (**classification**): let `E/F` be a cyclic algebra of
  group `⟨σ⟩` of order `l` over nonarchimedean local fields, `δ ∈ GL_n(E)` norm-associated with a
  regular semisimple `γ ∈ GL_n(F)`, `m` a Levi class system of `γ` (the Library's
  `IsLeviClassSystem`) and `d j ∈ M(E)` with blockwise cyclic norms the blocks of `m j`. If
  `p ∈ P(E)` equals `g⁻¹ δ σ(g)`, then the Levi part `x` of `p` is `M(E)`-twisted conjugate to some
  `d j`.

  Proof: by the norm lemma (`cyclicNormLemma`) each block `x_i` has a norm associated with some
  `γ'_i ∈ GL_{n_i}(F)`. Comparing characteristic polynomials of `N(p)` (block triangular, so the
  product over the blocks) with that of `N(δ)` (conjugate to `γ`) gives
  `charpoly(γ') = charpoly(γ)`; since `γ` is regular semisimple, `γ` and the block diagonal element
  `γ'` are conjugate (`exists_matrix_conj_of_charpoly_eq_of_separable`), so `γ'` is `M(F)`-conjugate
  to some `m j`. Then for each block the norms of `x_i` and of `d j i` are conjugate, and the second
  part of the norm lemma makes `x_i` and `d j i` twisted conjugate in `GL_{n_i}(E)`.

The classification describes the Levi parts of parabolic elements in the exact twisted orbit of
`δ`. It is the algebraic input of the support statement implicit in Henniart–Lemaire (2011),
II.4.5. Given open windows around the representatives `d j`, this classification and compactness
(`exists_nhds_forall_proj_mem`, module `Langlands.BaseChange.TwistedLocalDescent.Support`) give a
neighbourhood of `δ` such that test functions supported there have twisted constant terms
supported in the union of the `M(E)`-twisted saturations of those windows (see
`Langlands.BaseChange.TwistedLocalDescent.Proof`). The constant term itself need not be supported
on the twisted conjugates of the `d j`: for `GL_1` over `F = E = ℚ_3`, `σ = 1` and `δ = 1`, the
constant term of the indicator of `1 + 3^r ℤ_3` is that indicator.

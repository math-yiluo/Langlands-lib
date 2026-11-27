# Hilbert–Schmidt cuspidal operators of tensor test functions on `GL_n`

Module `Langlands.TraceFormula.GeneralLinearTensorCuspidalHilbertSchmidtStatement` contains one
proposition definition and no proof:

- `Langlands.TraceFormula.GeneralLinearTensorCuspidalHilbertSchmidtStatement.{u} : Prop`.

It states that, for `GL_n` over a number field `F`, the cuspidal operator of every tensor test
function `a ⊗ b` is Hilbert–Schmidt. This is the hypothesis on tensor test functions of
`Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaStatement`, stated as a proposition
of its own.

## Statement

Let `F : Type u` be a number field and `n : ℕ`, and write `GLₙ` for the group scheme
`GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`. The data are those of the
Library's positive rational quotient, exactly as in `GeneralLinearTensorSimpleTraceFormulaStatement`:

- `hPD : ParabolicDynamicStatement` and `hG : IsConnectedReductive GLₙ`;
- a commutative group scheme `T` with a central morphism `i : T → GLₙ` (`hc : IsCentral i`) whose
  restriction of characters is injective (`hi`) with range of finite index, and an isomorphism `e`
  of `T` with the split torus indexed by a finite type `I`;
- right invariance of Haar measure on the norm-one subgroup `normOneSubgroup F GLₙ`.

Let `μG` be Haar measure on `GL_n(𝔸_F)`. For

- `a : ArchimedeanGL.SmoothCompactKernel F n`, a smooth compactly supported function on the
  archimedean group `GL_n(F_∞)`,
- `b : CompactFiniteGLTest F n`, a locally constant compactly supported function on the finite
  adelic group,
- and every proof `h` that `g ↦ (a ⊗ b)(g)` is `μG`-integrable, where
  `(a ⊗ b) = adelicTestTensor F n a b` is read on the group-scheme points through
  `GeneralLinearGroupPoints.adelicHomeomorph`,

the operator `fullAEL2CuspidalIntegratedAction … μG (a ⊗ b) h` is Hilbert–Schmidt
(`Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt`). That operator is the integrated right
action `∫ (a ⊗ b)(g) R(g) dμG(g)` on the closed cuspidal subspace `fullAEL2CuspidalSubmodule` of
`L²` of the positive rational quotient.

## Source and correspondence

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Theorem 9.1.2 (Gelfand and Piatetski-Shapiro), printed p. 241 (PDF p. 253): `L²_cusp([G])` is
  closed and `R_cusp(f)` is of trace class for every `f ∈ C_c^∞(A_G \ G(𝔸_F))`.
- Lemma 9.3.3 and its proof, printed pp. 247–248 (PDF pp. 259–260): if
  `‖R(f)ϕ‖_∞ ≤ C ‖ϕ‖₂` on a closed invariant subspace `V`, then `R(f)` restricted to `V` has a
  square-integrable kernel and is Hilbert–Schmidt. Trace class then follows by writing `f` as a
  finite sum of convolutions (Dixmier–Malliavin).
- In the number field case the uniform estimate (9.13) for cuspidal `ϕ` is proved in §9.4, which
  ends on printed p. 257 (PDF p. 269). In the function field case the proof in §9.5 (printed
  p. 262, PDF p. 274) shows directly that `R_cusp(f)` is Hilbert–Schmidt.

The October 2026 errata (registered `getz-hahn-2024-errata-2026-10`) correct one step in §9.5;
the statement of Theorem 9.1.2 is unchanged.

The proposition is the Hilbert–Schmidt step for `GL_n`, for the tensor test functions of the
Library. For `GL_n` the group `A_G` of Getz–Hahn is the positive real torus `A⁺` of the centre.
The operator of `a ⊗ b` on `L²` of the positive rational quotient is the operator of its
`A⁺`-average, which is a smooth compactly supported function on `A_G \ G(𝔸_F)`. The cuspidal
subspace is the Library's almost-everywhere cuspidal subspace, as in
`GeneralLinearTensorSimpleTraceFormulaStatement`.

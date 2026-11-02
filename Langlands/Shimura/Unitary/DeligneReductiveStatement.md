# The Deligne torus is reductive: statement

Author: Worker 207.

This module states that the real Deligne torus `𝕊 = Res_{ℂ/ℝ} 𝔾_m` is reductive, in the two
senses defined in `Langlands.GroupScheme.Reductive.Basic`. It proves nothing. The only
declaration is the `Prop`-valued definition `ReductiveStatement` in the namespace
`Langlands.Shimura.DeligneTorus`.

## Lean statement

```lean
def ReductiveStatement : Prop :=
  GroupScheme.IsConnectedReductive groupScheme ∧ GroupScheme.IsReductive groupScheme
```

- `groupScheme` is the published real Deligne group scheme over `Spec (CommRingCat.of ℝ)`, from
  `Langlands.Shimura.Unitary.DeligneGroupScheme` (Worker 57). Its points with values in a real
  algebra `A` are the units of `QuadraticAlgebra A (-1) 0`, that is, of `A ⊗_ℝ ℂ`. So it is
  `Res_{ℂ/ℝ} 𝔾_m`, and its real points are `ℂˣ`.
- `IsConnectedReductive groupScheme` (over the field `ℝ`) says four things. The group is smooth
  and affine over `Spec ℝ`. Its underlying scheme is connected. Its base change to
  `AlgebraicClosure ℝ` has trivial unipotent radical: every smooth connected unipotent closed
  subgroup with normal image is trivial. This is Milne's definition 6.46.
- `IsReductive groupScheme` (over the base scheme `Spec ℝ`) says three things. The group is
  smooth and affine over `Spec ℝ`. For the unique point `s` of `Spec ℝ`, the geometric fibre
  along `Spec κ(s)^alg → Spec ℝ` (`geometricFiber`) is pseudo-reductive. This is Conrad's
  Definition 3.1.1.

The two conjuncts overlap: both contain smoothness and affineness. The second also states
reductivity of a geometric fibre over a second algebraic closure, the closure of the residue
field `κ(s)` rather than of `ℝ` itself. Neither conjunct follows from the other by a theorem
already in the Library: the Library does not prove that the unipotent radical is invariant
under extension of algebraically closed fields. That is why both are stated.

## Sources

- Milne, *Introduction to Shimura varieties*, in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Mathematics Proceedings 4 (2005), Section 2, paragraph "Hodge
  structures as representations of S", printed p. 282 (PDF p. 294): "Let S be C^× regarded as
  a torus over R." The same paragraph fixes the isomorphism `S_C ≅ Gm × Gm`. Source ID
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`.
- Milne, *Algebraic groups* (2017), source `milne-2017-algebraic-groups` (printed page `p` is
  PDF page `p + 16`):
  - 6.46 (printed p. 135): a connected group variety is reductive if its geometric unipotent
    radical is trivial. This is `IsConnectedReductive`.
  - Proposition 21.60 (printed p. 442, PDF p. 458): over a perfect field, a connected group
    variety is reductive if and only if its radical is a torus.
  - Corollary 19.18 (printed p. 401, PDF p. 417): a connected group variety with a faithful
    representation that is semisimple over `k` and over `k^a` is reductive.
- Conrad, *Reductive group schemes* (2014), Definition 3.1.1 (p. 81), source
  `conrad-2014-reductive-group-schemes`: a reductive group over a scheme `S` is a smooth
  `S`-affine group whose geometric fibres are connected reductive groups. This is `IsReductive`.

## Provenance

The sources do not state "the Deligne torus is reductive" as a numbered result. It is the
standard fact that tori are reductive, applied to `𝕊`, which Milne calls a torus over `ℝ`. Two
derivations from the cited results:

- `ℝ` is perfect, and the radical of a torus is the torus itself, so Proposition 21.60 applies.
- `𝕊_ℂ ≅ 𝔾_m × 𝔾_m` is a split torus. Its diagonal embedding into `GL_2` is a faithful
  representation that is a sum of one-dimensional representations over `ℂ`, so Corollary 19.18
  applies to `𝕊_ℂ`. The unipotent radical is a geometric notion, so `𝕊` is reductive over `ℝ`.

The second derivation is the one a Lean proof can follow. The companion statement
`Langlands.GroupScheme.IsSplitTorus.ReductiveStatement` (module
`Langlands.GroupScheme.Torus.SplitReductiveStatement`) says that split tori are reductive.
`isSplitTorus_complexGroupScheme` (module `Langlands.Shimura.Unitary.DeligneSplitTorus`) says
that `𝕊_ℂ` is a split torus. Every algebraically closed field over `ℝ` contains a copy of `ℂ`,
so every geometric fibre of `𝕊` is a split torus.

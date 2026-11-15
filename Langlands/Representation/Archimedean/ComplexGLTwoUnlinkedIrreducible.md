# Irreducibility of principal series of `GL_2(ℂ)` for unlinked characters

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducible`.

This module states one proposition,
`Langlands.Archimedean.ComplexGLTwoUnlinkedIrreducibleStatement` (GL2Irr). It proves nothing.
GL2Irr is the two-character case of the irreducibility criterion for principal series of
`GL_n(ℂ)`: the principal series of `GL_2(ℂ)` attached to two complex characters that are not
linked is irreducible. It is the basic input for a proof of the swap statement
`ComplexStandardUnlinkedSwapStatement` (module `ComplexStandardUnlinkedSwap`), which in turn
serves both halves of the split in `ComplexLargeStandardIrreducibleSplit.md`. GL2Irr is stated
separately, rather than taken as the case `n = 2` of
`ComplexStandardIrreducibleCriterionStatement` (Sp_C), because a proof of Sp_C may itself use the
swap statement, and the swap statement is to be proved from GL2Irr.

## Notation

As in `ComplexLargeStandardIrreducibleSplit.md`: `ComplexCharacterData` is the character
`z ↦ (z/|z|)^l |z|^{2t}` of `ℂˣ` with weight `l ∈ ℤ` and exponent `t ∈ ℂ`, `|z|` the usual
absolute value. For a list `ls` of `n` complex characters, `X(ls)` is the space
`kFiniteFunctions (complexStandardModule n ls) (unitaryCompact ℂ n)` of `U(n)`-finite functions
of the Library's standard module, with the `(𝔤𝔩_n(ℂ), U(n))`-action
`(complexStandardRep n ls, complexStandardLie n ls)` (right translation by `U(n)` and right
derivatives). The `j`-th entry of `ls` is the character on the `j`-th diagonal entry of the
Borel subgroup of upper triangular matrices, so `X([d, e])` is the Harish-Chandra module of
Tadić's `δ_d × δ_e` (see `ComplexGenericParameterReduction.md` for the passage from the
Library's left-equivariant functions to the usual induced picture).

`IsComplexLinked d e` (module `ComplexLargeStandardIrreducibleSplit`) says that there are
integers `p, q` with `0 < p * q`, `(t_d + l_d/2) - (t_e + l_e/2) = p` and
`(t_d - l_d/2) - (t_e - l_e/2) = q`. In Tadić's parametrization `γ(x, y)` with `x = t + l/2`,
`y = t - l/2`, this says that the quotient character `δ_d δ_e⁻¹` is `z ↦ z^p z̄^q` with
`p q > 0`. The relation is symmetric in `d`, `e`, and no character is linked to itself.

`IsIrreducibleGKModule ρ π` (module `GKModule`) says that the underlying space is nontrivial and
that its only subspaces stable under all `ρ k` and all `π X` are `0` and the whole space.

## The statement

`ComplexGLTwoUnlinkedIrreducibleStatement`: for all complex characters `d`, `e` with
`¬ IsComplexLinked d e`,

  `IsIrreducibleGKModule (complexStandardRep 2 [d, e]) (complexStandardLie 2 [d, e])`.

In words: `X([d, e])` is nonzero and has no `(𝔤𝔩_2(ℂ), U(2))`-submodules other than `0` and
itself. No condition is imposed on the order of `d`, `e` (the real parts of `t_d`, `t_e` may be
in either order or equal), and `d = e` is allowed. Since linkage depends only on the quotient
`δ_d δ_e⁻¹`, the hypothesis is unchanged when `d` and `e` are multiplied by a common character;
this is what a proof of the swap statement needs, because restricting a principal series of
`GL_n(ℂ)` to a `GL_2(ℂ)` block twists the two block characters by a common power of `|det|`.

## Source

Tadić 2009, §3, p. 11: "We shall say that `δ₁, δ₂ ∈ D` are linked if and only if `δ₁ × δ₂` is
reducible. The representation theory of `GL(2, ℂ)` implies that `δ₁` and `δ₂` are linked if and
only if there exist `p, q ∈ ℤ` such that `pq > 0` and `(δ₁δ₂⁻¹)(z) = z^p z̄^q = γ(p, q)(z)` for
all `z ∈ ℂ×` (see [JL])." Here `δ₁ × δ₂` is the representation of `GL(2, ℂ)` parabolically
induced from the Borel subgroup (p. 5), and [JL] is Jacquet–Langlands, *Automorphic forms on
`GL(2)`*. GL2Irr is the "only if" direction of the second sentence (if `δ₁ δ₂⁻¹` is not of that
form, then `δ₁ × δ₂` is irreducible), for `δ₁ = δ_d`, `δ₂ = δ_e`, transcribed with
`IsComplexLinked` as explained in `ComplexLargeStandardIrreducibleSplit.md`.

## Provenance

Direct transcription of Tadić's two-character statement (p. 11), in its "unlinked ⇒
irreducible" direction, for the Library's `complexStandardModule 2 [d, e]` and its `U(2)`-finite
part. The identification of that model with the classical principal series `δ_d × δ_e` is
described in `ComplexGenericParameterReduction.md` and `ComplexLargeStandardIrreducibleSplit.md`.

Source:

* M. Tadić, `GL(n, ℂ)^` and `GL(n, ℝ)^`, in: Automorphic Forms and L-functions II. Local
  Aspects, Contemp. Math. 489, Amer. Math. Soc., 2009, pp. 285–313
  (`tadic-2009-gl-n-c-gl-n-r-unitary-duals`, author's PDF; PDF page = page number of the
  running head). §1: parabolic induction `σ₁ × σ₂` (p. 5). §3: the parametrizations
  `δ(β, n)`, `γ(x, y)` and linked characters, with the description of linked pairs after [JL]
  (p. 11).

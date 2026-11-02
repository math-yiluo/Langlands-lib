# The quasi-split unitary group `U(1,1)` is connected reductive: statement

Author: Worker 293. This is statement S5 of task
`be70310c-1939-4a82-8293-c4d33f5883ae`. The module contains one `Prop`-valued
definition and no proof. A proof is left to a separate `lean.proof` task.

## The statement

`IsConnectedReductiveStatement` says the following. Let `F` and `E` be fields
in one universe `u`, with `[Algebra F E]` and
`[Algebra.IsQuadraticExtension F E]`. Let `κ` be a finite type in universe `u`,
and let `b` be an `F`-basis of `Matrix (Fin 2) (Fin 2) E` indexed by `κ`. Let
`c : E ≃ₐ[F] E` satisfy `c ≠ AlgEquiv.refl`. Then `groupScheme b c` satisfies
`IsConnectedReductive`.

Here `groupScheme b c` is the group scheme `U(1,1)` over
`Spec (CommRingCat.of F)` of unit 1, `Langlands.GroupScheme.Examples.QuasiSplitUnitary`
(Worker 399). It is the Library's `SchemeModel.unitaryGroupScheme` of `b` and
of the involution `X ↦ J (X.map c)ᵀ J` of `Matrix (Fin 2) (Fin 2) E`, where
`J = !![0, 1; 1, 0]`. The full unitary equation is imposed, with no
determinant condition.

`IsConnectedReductive` is the Library's predicate of
`Langlands.GroupScheme.Reductive.Basic`. It has four fields: the structure
morphism is smooth and affine, the underlying scheme is a connected space, and
the base change to `Spec (AlgebraicClosure F)` has trivial unipotent radical
(`HasTrivialUnipotentRadical`: every smooth, connected, unipotent, normal closed
subgroup is trivial).

No assumption on the characteristic of `F` is made, so the statement covers
characteristic `2`. The universe of `κ` is `u`, as required by
`groupScheme`.

## Sources and provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`
(printed page `p` is PDF page `p + 16`):

- 6.46 (printed p.135): a connected group variety over `k` is reductive if the
  unipotent radical of its base change to an algebraic closure is trivial. The
  reductivity paragraph on printed p.400 restates this with smoothness and
  connectedness.
- Proposition 19.13 (printed p.400): a group variety is reductive if and only
  if its base change to an extension field is.
- Example 19.19 (printed p.401): `GL_n` is reductive.
- 24.40–24.44 (printed pp.523–525): unitary groups of algebras with
  involution. Proposition 24.40(b) splits them over an extension of the centre,
  and display (158) on printed p.525 embeds the split form by
  `X ↦ (X, (Xᵗ)⁻¹)`.

Milne does not state this particular result. The statement is derived for this
task: `U(1,1)` becomes `GL₂` over `E`, and reductivity is invariant under field
extension. The parent program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e` asks for a
noncommutative, non-split connected reductive example.

## Intended proof

This is design information only; the module proves nothing. Deliverable 3,
`QuasiSplitUnitarySplitting.splittingIso`, identifies the base change of
`groupScheme b c` to `Spec E` with `GeneralLinear.groupScheme (Fin 2)
(CommRingCat.of E)`. The Library's statement
`Langlands.GroupScheme.GeneralLinear.IsConnectedReductiveStatement`
(`Langlands/GroupScheme/Reductive/GeneralLinearStatement`, Milne 19.19) says
that `GL_n` is connected reductive over every field. The Library proves it as
`Langlands.GroupScheme.isConnectedReductive_generalLinear`
(`Langlands/GroupScheme/Reductive/GeneralLinear`), which also provides
`HasTrivialUnipotentRadical.of_iso`. From these, smoothness and connectedness
descend along `Spec E ⟶ Spec F`, affineness comes from the unitary model, and
the geometric unipotent radical is handled by transporting that of `GL₂` along
the base change of the splitting to `AlgebraicClosure F`.

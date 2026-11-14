# Character determination on the intersection Levi without characteristic zero

Module `Langlands.AllField.Representation.Geometric.IntersectionLeviDiagonalCharacter`.

The Library theorem `Langlands.Geometric.intersectionLeviDiagonalCharacterTheorem`
(module `Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof`)
proves `Langlands.Geometric.IntersectionLeviDiagonalCharacterStatement`: a character
`χ : I →* ℂˣ` of the intersection Levi
`I = General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F) (permutation n F w)`
that is trivial on every diagonal matrix of `I` is trivial. That statement assumes
`CharZero F`, which holds for p-adic fields but not for local fields of positive
characteristic. Its only use of `CharZero F` is that `2 ≠ 0` in `F`. This module proves the same
conclusion over every field that has an element other than `0` and `1`, in particular
over every nonarchimedean local field. The all-field port uses it in
`Langlands.AllField.Representation.Geometric.IntersectionLeviModulusBalance` in place of
the characteristic-zero theorem. This is an internal generalization with no separate
literature counterpart; the provenance of the statement is that of
`IntersectionLeviDiagonalCharacterStatement` (see its Markdown).

The helper declarations are in the namespace
`Langlands.AllField.Geometric.DiagonalCharacter`. They reuse `diagonalUnit`,
`diagonalUnit_one`, `character_pi`, `leviEmbedding_diagonalUnit` and `sourceActualEquiv`
from the original module's namespace `Langlands.Geometric.DiagonalCharacter`,
`GeneralLinear.transvectionUnit` (module `Langlands.Group.GL.Transvection`), and
`refinedLeviEquiv` and `exists_standardIntersections` from `Langlands.Geometric`. None of
these assumes `CharZero`.

## Declarations

- `DiagonalCharacter.scale_transvection`: for a unit `s`, the diagonal matrix that
  scales row `i` by `s` (and fixes the other rows) conjugates the transvection with entry
  `c` at `(i, j)` to the transvection with entry `s * c`:
  `d_s * t(c) = t(s c) * d_s`. Proof: entrywise comparison of the two matrix products.
  The original instead uses only `s = 2`, where `t(2c) = t(c)^2`.
- `DiagonalCharacter.character_transvection`: if `F` has an element `s ≠ 0, 1`, every
  monoid homomorphism `χ : GL_k(F) →* ℂˣ` is trivial on every transvection. Proof:
  conjugation invariance (`ℂˣ` is commutative) and `scale_transvection` give
  `χ(t(s b)) = χ(t(b))` for every `b`. Put `b = c / (s - 1)`, so `s b = b + c`; since
  `t(b + c) = t(b) t(c)`, this reads `χ(t(b)) χ(t(c)) = χ(t(b))`, hence `χ(t(c)) = 1`.
  The original derives `χ(t) = χ(t)^2` from the case `s = 2`, which needs `2 ≠ 0`.
- `DiagonalCharacter.character_GL`: under the same hypothesis, a character of
  `GL_k(F)` that is trivial on all unit diagonal matrices is trivial. Proof: as in the
  original, by `Matrix.diagonal_transvection_induction_of_det_ne_zero`.
- `DiagonalCharacter.character_pi_GL`: the same for a finite product of general linear
  groups. Proof: as in the original, reduce to each factor with `character_pi`.
- `exists_ne_zero_ne_one`: a field with a nontrivial valuative relation (in particular
  a nonarchimedean local field) has an element `s` with `s ≠ 0` and `s ≠ 1`. Proof: the
  valuation takes a value other than `0` and `1` (`Valuation.IsNontrivial`), so its
  argument is neither `0` nor `1`.
- `intersectionLeviDiagonalCharacter` (theorem): for a field `F` with an element other
  than `0` and `1`, every `n`, block shapes `B C : GeneralLinear.BlockShape n` and
  `w : MinimalRepresentatives B C`, a character `χ : I →* ℂˣ` with `χ m = 1` whenever the
  matrix of `m` is `Matrix.diagonal (fun i => (t i : F))` for some `t : Fin n → Fˣ`
  satisfies `χ m = 1` for every `m : I`. This is the statement of
  `IntersectionLeviDiagonalCharacterStatement` with the hypothesis `CharZero F` replaced by
  `∃ s : F, s ≠ 0 ∧ s ≠ 1`. Proof: the proof of the original theorem, with
  `character_pi_GL` of this module in place of the characteristic-zero version. The
  standard intersections `exists_standardIntersections` identify `I` with a product of
  block-diagonal Levi groups; the diagonal hypothesis transfers along this
  identification by `leviEmbedding_diagonalUnit`.

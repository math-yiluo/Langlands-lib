# One-step splitting and tower sections over arbitrary fields

Module
`Langlands.GroupScheme.Trigonalizable.PerfectOneStep`, namespace
`Langlands.GroupScheme.TrigonalizableExtensionSplit`.

The Library's `linearAdditiveExtensionSplitting` (Milne 15.34(d) for a
diagonalizable quotient) and `LinearKernelTower.exists_section_of_admitsTower`
are stated over algebraically closed fields. This module removes that
restriction wherever the correction equation is solvable, and proves
solvability over a perfect field when `D(Λ)` is connected.

## Declarations

- `exists_section_of_solvable`: over any field `k`, for `E` affine,
  `q : E ⟶ D(Λ)` flat and surjective, a closed embedding `a` of the actual
  kernel of `q` into `𝔾ₐ`, a character `χ` and an action `b` satisfying the
  conjugation law `hconj` and the linearity law `hlin` (exactly the hypotheses
  of `LinearAdditiveExtensionSplittingStatement`), and the solvability
  hypothesis `hsolv` of `exists_corrected_of_solvable`, `q` has a homomorphic
  section. The proof is the Library proof of `linearAdditiveExtensionSplitting`
  with `exists_corrected_of_solvable` in place of `exists_corrected`.
- `OneStepSplitting k Λ`: the body of `LinearAdditiveExtensionSplittingStatement`
  for one fixed field `k` and character group `Λ`, without algebraic closure:
  every such extension of `D(Λ)` over `k` (with `E` affine and locally of
  finite type and `q` flat, surjective and locally of finite presentation) has
  a homomorphic section.
- `oneStepSplitting_of_perfect`: if `k` is perfect and `D(Λ)` is connected,
  `OneStepSplitting k Λ` holds. The hypothesis `hsolv` is supplied by
  `PerfectCorrection.surjective_or_charValue_pow_eq_one`, with the stability of
  the range of `a` given by the Library's `weight_stable`.
- `exists_section_of_step'`, `exists_section_of_hasTower'`,
  `exists_section_of_admitsTower'`: the Library's tower induction
  (`LinearKernelTower.exists_section_of_step`, `exists_section_of_hasTower`,
  `exists_section_of_admitsTower`), with the hypothesis
  `LinearAdditiveExtensionSplittingStatement` replaced by `OneStepSplitting k Λ`
  and no algebraic closure. The proofs are the Library proofs; the one-step
  hypothesis is applied to the same inverse image of the section.

## Provenance

Internal generalizations of the published Library proofs in
`LinearAdditiveExtensionSplittingProof.lean` and `LinearKernelTowerSection.lean`,
which follow Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`,
SHA256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Theorem 15.34 (printed p.319) and the proof of Theorem 16.26 (printed
pp.332–333). The connected perfect case corresponds to the use of 15.34(a)–(c)
in case (c) of the proof of 16.26.

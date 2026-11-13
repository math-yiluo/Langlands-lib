# Renard VI.7.2, second Lemma, from cuspidal splittings and from VI.3.5

Worker 4814, for Task 5419. This module assembles
`Langlands.CuspidalSupport.BernsteinCuspAdjunctionStatement` (Renard VI.7.2,
second Lemma) for the actual standard family. Its only remaining input is Renard
VI.3.5, which enters as the explicit hypothesis
`RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}`. The module
does not prove VI.3.5, so it does not prove the target statement unconditionally.
It also defines Renard's cuspidal-part functor `V ↦ V_sc` of each standard Levi
from VI.3.5.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.7.2, second Lemma and its proof, printed pp.182–183 /
PDF pp.188–189, and VI.3.5; source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Definitions, results and their proofs

- `bernsteinCuspAdjunction_of_splittings`: for one actual standard family, the
  conclusion of the target statement holds whenever every smooth representation
  `A` of every literal standard Levi subgroup has a cuspidal/remainder splitting
  (`SplitReflector.HasSplitting (cusp family J) A`). Its type repeats the target's
  body verbatim, with the target's `let` definitions of `cusp`, `jac`, `Ifun` and
  `R`. The proof:
  - Cuspidality of each standard Levi is split Serre
    (`BernsteinCuspLeftAdjoint.isSplitSerre_cusp`). So each inclusion has a left
    adjoint (`SplitReflector.exists_leftAdjoint`), which is clause 1.
  - For a supplied family `sc` of such left adjoints, clause (i) is Worker 132's
    `bernsteinCuspAdjunction_of_reflectors`.
  - The assertions on `R` in clause (ii) are `bernsteinR_faithful` (applied to an
    adjunction from clause (i)), `bernsteinR_map_isShortExact` and
    `bernsteinR_obj_finite`.
  - The assertions on `I` are Worker 132's `bernsteinInductionFunctor_faithful`
    and `bernsteinInductionFunctor_map_isShortExact`.
  - Clause (iii) is `bernsteinR_unit_injective`, which holds for every adjunction
    `R ⊣ I`.
- `hasSplitting_cusp_of_wholeDecomposition`: Renard VI.3.5, at any carrier
  universe `uW`, provides these splittings. The published
  `hasLeviCuspidalRemainderSplitting_of_wholeStatement` applies VI.3.5 to the
  represented standard Levi scheme and transports the coproduct to the literal
  Levi subgroup. Its inputs are discharged by published results: `standardCocharacter`,
  `standardLeviIntersection`, the family's fields, and the relative root system of
  the Levi torus factor. That root system is `relativeRootSystem`, applied with
  `standardLeviScheme_isConnectedReductive` and
  `isMaximalSplitTorus_standardLeviTorusFactor`. The resulting
  `HasLeviCuspidalRemainderSplitting` is definitionally
  `SplitReflector.HasSplitting (cusp family J) A`; the decompositions agree by
  proof irrelevance.
- `bernsteinCuspidalPart i ν family hwhole J` (a definition): Renard's
  cuspidal-part functor `V ↦ V_sc` on smooth representations of the literal
  standard Levi `M_J` at carrier universe `uW`, valued in the full subcategory of
  cuspidal representations (`cusp family J`). Given VI.3.5 (`hwhole`), it is the
  generic `SplitReflector.reflector` for the split Serre property `cusp family J`,
  built from the splittings of `hasSplitting_cusp_of_wholeDecomposition`. It sends
  each representation to the `true` (cuspidal) summand of its chosen splitting.
  `bernsteinCuspidalPartAdjunction` is the adjunction
  `bernsteinCuspidalPart i ν family hwhole J ⊣ (cusp family J).ι`
  (`SplitReflector.reflectorAdjunction`). These two definitions make Renard's
  functor `sc` explicit. The theorems in this module do not use them; there, clause
  1 is proved by `SplitReflector.exists_leftAdjoint`, which uses the same
  construction.
- `bernsteinCuspAdjunction_of_wholeDecomposition`: combining the first two theorems,
  `RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}` implies
  `BernsteinCuspAdjunctionStatement.{uF, uV}`.

Both large theorems raise `maxHeartbeats` to a finite 1600000. Elaborating the
target's body and unifying its `let` definitions with the abbreviations of the
supporting modules exceeds the default limit.

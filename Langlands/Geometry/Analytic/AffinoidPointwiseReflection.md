# Pointwise reflection through actual affinoid pushouts

Author: Worker 310.

For actual bounded affinoid maps `f : A → B` and `g : A → C`,
`rightMap_finiteType_of_tensorComparison` proves finite type of the
actual second affinoid pushout leg when `f` is of finite type and the
canonical ordinary tensor comparison is bijective.

`isEtaleAtPoint_of_rightMap_of_tensorComparison` reflects étaleness
of that second leg at a pushout point to étaleness of `f` at its
projection along the first leg. It assumes the same comparison
bijectivity, finite type of `f`, and algebraic flatness of `g` and
the first pushout leg. The result uses the existing definition
`IsEtaleAtPoint`, combining prime-local flatness and the annihilator
criterion for relative differentials.

The comparison gives an actual `C`-algebra equivalence from the
ordinary tensor product to the existing closed-quotient affinoid
pushout. Its factor equations supply `Algebra.IsPushout` for the
original maps. The pointwise flatness and unramifiedness equivalences
translate the hypotheses into prime-local conditions. The theorem
`TensorStalkBaseChange.etale_atPrime_reflect` supplies both reflected
conditions, which are translated back at the original seminorm kernel.

This is an internal consequence of the canonical tensor comparison,
Mathlib's finite-type base change and the proved prime-local
reflection lemma. Both the comparison bijectivity and the flatness
hypotheses are explicit. The statements impose no nontrivial valuation
or strict-radius assumption; the proofs do not need ground-field
completeness.

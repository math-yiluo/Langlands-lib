# Uniqueness of the central character of a nonzero operator realization

Author: Worker 5151.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter` (module
`Langlands.Automorphic.AssociatedCentralCharacterProof`) supplies clause 3 of
`AssociatedCentralCharacterStatement`: a cuspidal realization has at most one central
character.

## `OperatorRealization.hasCentralCharacter_unique`

If the space of an operator realization `S` is nontrivial and both `χ` and `η` are central
characters of `S` (`S.HasCentralCharacter`), then `χ = η`.

Proof: choose a nonzero vector `f`. Its continuous form `S.toContinuous f` is not
identically zero, since otherwise `f = 0` by `toContinuous_injective`; so some `x` in the
adelic group has `f(x) ≠ 0` (evaluation `ContinuousRationalFunctions.evaluate`). Every
idele class is the image of an idele `z` (`QuotientGroup.mk'_surjective`), and the
published `OperatorRealization.centralCharacter_evaluate` gives
`f(z x) = χ(z) f(x)` and `f(z x) = η(z) f(x)`. Cancelling `f(x) ≠ 0` gives `χ(z) = η(z)`.

## `CuspidalOperatorRealization.hasCentralCharacter_unique`

The same for an actual cuspidal realization `T` (with `AdeleQuotient F` compact): its
space is nontrivial by the published `CuspidalOperatorRealization.space_nontrivial`, and the
previous theorem applies to `T.realization`.

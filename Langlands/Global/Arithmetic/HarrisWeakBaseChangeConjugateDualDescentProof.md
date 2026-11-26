# The conjugate dual of a weak descent: proof

Module: `Langlands.Global.Arithmetic.HarrisWeakBaseChangeConjugateDualDescentProof`.

`Langlands.Global.Harris.weakBaseChangeConjugateDualDescent` proves
`Langlands.Global.Harris.WeakBaseChangeConjugateDualDescentStatement.{uE, uD, uV, uW}` of
[HarrisCyclicDescentCorrectionStatement](HarrisCyclicDescentCorrectionStatement.md) for all four
universes.

## Statement proved

Let `E : Type uE` and `D : Type uD` be CM number fields with `[Algebra E D]` and compact adele
quotients. Let `S Sdual : CuspidalOperatorRealization E r` and
`T : CuspidalOperatorRealization D r`. Suppose that `Sdual.realization.IsContragredientOf
S.realization`, that `T.isoClass.IsConjugateSelfDual`, and that
`T.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.isoClass`. Then
`T.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} Sdual.complexConj.isoClass`. The hypotheses are
exactly those of the statement; the proof uses no Galois, cyclicity or unitarity assumption.

## The implemented proof

The lemmas used are proved in
[WeakBaseChangeConjugateDual](../../Automorphic/Unramified/WeakBaseChangeConjugateDual.md).

1. `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff` turns the conjugate
   self-duality of the class of `T` into that of `T.realization`.
2. `OperatorRealization.complexConj_isContragredientOf_of_isConjugateSelfDual` then shows that
   `T.complexConj` realizes the contragredient of `T`.
3. `CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_of_isContragredientOf` applies to the
   contragredients `Sdual` of `S` and `T.complexConj` of `T`. It gives that `T.complexConj` is a
   weak base change of `Sdual`.
4. `CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_complexConj` applies the CM
   involutions on both levels: `T.complexConj.complexConj` is a weak base change of
   `Sdual.complexConj`.
5. `CuspidalOperatorRealization.complexConj_complexConj` rewrites `T.complexConj.complexConj` as
   `T`.

## Relation to the source

Harris 1998, Lemma 1.6 (printed p. 189; companion TeX `math_9611226v1.tex`, lines 756–761) argues:
"base change from `E` to `E^u` commutes with complex conjugation and with the contragredient.
Thus `BC_{E^u/E}(π̌ ∘ c) = π̌^u ∘ c = π^u`." Here `S`, `Sdual` and `T` play the roles of `π`, `π̌`
and `π^u`. Steps 3 and 4 are the two commutations, and steps 1, 2 and 5 are the identity
`π̌^u ∘ c = π^u`, from the conjugate self-duality of `π^u`. The Lean proof stays at the level of
actual spectral presentations. The contragredient presentations come from
`cuspidalDualPresentationExistence` and the conjugated ones from arithmetic pullback. Their
spectra are compared at almost all base places. The proof uses no strong multiplicity one and no
uniqueness of presentations.

# Weak base change under contragredients and CM conjugation

Module: `Langlands.Automorphic.Unramified.WeakBaseChangeConjugateDual`.

The module proves four lemmas about the actual cuspidal classes and the weak base change relation
`CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf` of
[WeakTransfer](WeakTransfer.md). They are internal lemmas: each one composes Library constructions
and asserts no new existence or uniqueness result. Their mathematical content is the remark in
Harris 1998, Lemma 1.6 (printed p. 189; companion TeX `math_9611226v1.tex`, lines 756–761) that
base change "commutes with complex conjugation and with the contragredient". The base change used
here is the arithmetic weak base change of Arthur–Clozel 1989, Chapter III, Definition 1.1, as
formalized in `Langlands.Unramified.SpectralSystem.IsArithmeticWeakBaseChangeOf`.
`Langlands.Galois.HarrisParityBaseChangeProof` contains private versions of the same arguments,
for fields in one universe. This module states them as public lemmas with independent universes
for the two fields.

## Conjugate self-duality as a contragredient

`Langlands.Automorphic.OperatorRealization.complexConj_isContragredientOf_of_isConjugateSelfDual`
takes a CM number field `F`, a rank `n` and an actual realization `S : OperatorRealization F n`.
If `S.IsConjugateSelfDual`, it gives `S.complexConj.IsContragredientOf S`: the actual CM image
of `S` realizes the contragredient of `S`.

Proof. Let `C` be the conjugate-contragredient pairing of `S`, and let
`e = S.complexConjEquiv : S ≃ S.complexConj` be the actual CM equivalence. The pairing is
`B y x = C y (e⁻¹ x)`. Under `e`, the finite action of `S.complexConj` at `d` is the finite
action of `S` at `finiteConj d` (`complexConjEquiv_finite`), and likewise for the compact action
with `compactConj` (`complexConjEquiv_compact`). For the real Lie algebra, the transport
`ArchimedeanLieTransport.realLieEquiv` along the CM involution of `F` is entrywise equal to
`lieConj`, so `complexConjEquiv_differential` gives the same relation with `lieConj`.
The conjugate invariance of `C`, applied at the conjugated element, then gives the ordinary
invariance of `B`. Here the proof uses that `finiteConj`, `compactConj` and `lieConj` are
involutions, which follows from the CM involution being an involution. The functional
`B.flip x` equals `C.flip (e⁻¹ x)`. Hence the contragredient property, injectivity and
surjectivity onto the contragredient functionals carry over from `C` through the bijection
`e⁻¹`.

## CM image as arithmetic pullback

`Langlands.Automorphic.CuspidalOperatorRealization.arithmeticComap_fieldConj` takes a CM field
`F` with `[CompactSpace (AdeleQuotient F)]` and `S : CuspidalOperatorRealization F r`. It proves
`S.arithmeticComap (fieldConj F) = S.complexConj`. Both realizations are the image of the
submodule of `S` under the same map of stable automorphic functions. After
`OperatorRealization.arithmeticComap_toSubmodule` and
`OperatorRealization.complexConj_toSubmodule`, the equality holds by definition.

## Contragredients on both levels

`Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_of_isContragredientOf`
takes number fields `E : Type uE` and `D : Type uD` with `[Algebra E D]` and compact adele
quotients, and actual realizations `S Sd` over `E` and `T Td` over `D` of rank `r + 1`. It
assumes `T.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.isoClass`,
`Sd.realization.IsContragredientOf S.realization` and
`Td.realization.IsContragredientOf T.realization`, and concludes
`Td.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} Sd.isoClass`. No CM or Galois hypothesis is
used.

Proof. `isWeakBaseChangeOf_isoClass_iff` gives presentations `P` of `S` and `Q` of `T` whose
systems satisfy the weak base change relation. `cuspidalDualPresentationExistence` supplies
presentations `Pd` of `Sd` and `Qd` of `Td`, with factors in the universes `uV` and `uW`. Take a
base place `v` that is good for `P` and `Q`, lies outside the exceptional set of `Pd`, and has no
place above it in the exceptional set of `Qd`. This holds for cofinitely many `v`, by
`Finset.eventually_cofinite_notMem` and `SpectralSystem.eventually_avoidsAbove`. For every place
`w` above `v` with residue degree `f`, `eigenvalues_eq_map_inv_of_isContragredientOf` gives two
equalities. The spectrum of `Qd` at `w` is the reciprocal of that of `Q`, and the spectrum of
`Pd` at `v` is the reciprocal of that of `P`. Hence the spectrum of `Qd` at `w` is the reciprocal
of the `f`-th power of the spectrum of `P` at `v`. It equals the `f`-th power of the reciprocal
spectrum, because `Eigenvalues.power` maps `z ↦ z ^ f` over the unordered spectrum and
`(z⁻¹) ^ f = (z ^ f)⁻¹`. The ramification condition is unchanged.

## CM conjugation on both levels

`Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_complexConj` takes
CM number fields `E : Type uE` and `D : Type uD` with `[Algebra E D]` and compact adele
quotients. It proves that
`T.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.isoClass` implies
`T.complexConj.isoClass.IsWeakBaseChangeOf.{uE, uD, uV, uW} S.complexConj.isoClass`.

Proof. Rewrite both CM images as arithmetic pullbacks along the CM involutions
(`arithmeticComap_fieldConj`). The witnesses are the pulled-back presentations
`P.arithmeticComap (fieldConj E)` and `Q.arithmeticComap (fieldConj D)` of
`CuspidalSpectralPresentation.arithmeticComap`. Their spectrum at a place `v` is that of the
original presentation at the conjugate place. The complex conjugations of `E` and `D` commute
with `algebraMap E D`. Indeed, for `a : E` and a complex embedding `φ` of `D`, both
`φ (c_D (algebraMap E D a))` and `φ (algebraMap E D (c_E a))` are the complex conjugate of
`φ (algebraMap E D a)` (`IsCMField.complexEmbedding_complexConj`, applied to `φ` and to
`φ ∘ algebraMap E D`), and `φ` is injective. So the conjugate of a place `w` above `v` lies above the conjugate of `v`. The induced isomorphisms of
residue fields commute with the algebra maps, so residue degrees are preserved
(`Algebra.finrank_eq_of_equiv_equiv`). The induced multiplicative equivalence of ideals of
`𝓞 D` preserves the multiplicities that compute ramification indices
(`Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`, `multiplicity_map_eq`). The set of
good base places is pulled back along the injective place map of the involution of `E`, which
preserves the cofinite filter. At each such place the original identities, read at the conjugate
places, are the required identities with the same residue-degree powers.

# Conjugate self-duality from a contragredient CM image

Module `Langlands.Automorphic.ConjugateSelfDualCriterion`. It proves a criterion for
conjugate self-duality (`OperatorRealization.IsConjugateSelfDual`, defined in
`Langlands.Automorphic.ConjugateContragredient`) and the identification of the arithmetic
pullback along the CM involution with the CM image. `F` is a CM number field in an
arbitrary universe; `fieldConj F` is its CM involution as a ring automorphism.

## Results

- `OperatorRealization.isConjugateSelfDual_of_complexConj_isContragredientOf`: for an
  actual automorphic realization `S` of `GL_n(𝔸_F)`, if the CM image `S.complexConj`
  realizes the contragredient of `S` (`S.complexConj.IsContragredientOf S`), then
  `S.IsConjugateSelfDual`. The conclusion is the whole pairing condition
  `IsConjugateContragredientPairing`: invariance under the conjugate-twisted finite,
  compact and Lie algebra operators, values of the partial map in the contragredient
  functionals, and the partial map injective and onto the contragredient functionals.
- `CuspidalOperatorRealization.arithmeticComap_fieldConj`: for a cuspidal realization
  `S`, `S.arithmeticComap (fieldConj F) = S.complexConj`.
- `CuspidalOperatorRealization.IsoClass.arithmeticComap_fieldConj`: its class form,
  `IsoClass.arithmeticComap (fieldConj F) c = IsoClass.complexConj c`.
- `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_of_isContragredientOf`: if
  `Sd` realizes the contragredient of the cuspidal realization `S` and
  `Sd.complexConj.isoClass = S.isoClass`, then `S.isoClass.IsConjugateSelfDual`.

## Proofs

- The criterion. Let `B` be the contragredient pairing of `S.complexConj` against `S`, and
  `e : S ≃ S.complexConj` the CM image equivalence (`complexConjEquiv`). The pairing
  `C y x = B y (e x)` is the required pairing of `S`. Invariance: `e` intertwines the
  finite (resp. compact) action of `d` on `S` with that of `finiteConj d` (resp.
  `compactConj k`) on `S.complexConj` (`complexConjEquiv_finite`, `complexConjEquiv_compact`),
  and these conjugations are involutions, because `fieldConj F` is one; so the invariance of
  `B` at `finiteConj d` (resp. `compactConj k`) is the conjugate-twisted invariance of `C`.
  For the Lie algebra, `e` intertwines `lieAction X` on `S.complexConj` with
  `lieAction (lieConj X)` on `S`: the arithmetic transport of real Lie algebra elements along
  `fieldConj F` is `lieConj`, computed entrywise in the mixed coordinates
  (`mixedSpace_infiniteComplexConj`), and `complexConjEquiv_differential` gives the
  enveloping algebra action. Since `lieConj` is an involution, the infinitesimal invariance
  of `B` at `lieConj X` is the twisted one of `C`. The partial map of `C` at `x` is that of
  `B` at `e x`, so it takes contragredient values, is injective, and is onto the
  contragredient functionals, because `e` is bijective.
- The pullback identity compares the underlying submodules
  (`OperatorRealization.arithmeticComap_toSubmodule`,
  `OperatorRealization.complexConj_toSubmodule`), which agree by definition, and then the
  cuspidal structures. The class form follows on a representative.
- The class criterion applies `IsoClass.complexConj` to the class equality: since it is an
  involution, `Sd.isoClass = S.complexConj.isoClass`, so `Sd` is equivalent to
  `S.complexConj`. `IsContragredientOf.of_equivalence_right` moves the contragredient
  relation to `S.complexConj`, and the criterion and `isoClass_isConjugateSelfDual_iff`
  conclude.

## Provenance

Derived content. The criterion makes precise the passage from `π ≅ π̌ ∘ c` to the pairing
that defines `IsConjugateSelfDual` in `Langlands.Automorphic.ConjugateContragredient`.
The same argument appears as the private lemma `isConjugateSelfDual_of_complexConj` of
`Langlands.Galois.HarrisParityBaseChangeProof`, with its auxiliary lemmas (the involution
properties of the CM conjugations and the Lie algebra intertwining) and the private
pullback identity `arithmeticComap_fieldConj` there; this module states the criterion and
the pullback identity publicly so that other proofs can use them. The auxiliary lemmas
remain private here.

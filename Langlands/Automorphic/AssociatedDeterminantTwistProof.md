# Determinants and finite-order twists under weak association

All declarations lie in the namespace
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup`.

The theorem `associatedDeterminantTwist` proves the published proposition
`AssociatedDeterminantTwistStatement` of the module
`Langlands.Automorphic.AssociatedDeterminantTwistStatement`. Its type is exactly
`AssociatedDeterminantTwistStatement.{u, uV, uP, uQ}`, with the four universes
independent: `u` for the number fields and the automorphic realizations, `uV` for
the carrier of the Weil-side representation `S`, and `uP` and `uQ` for the local
factors of the presentations on the two sides. No hypothesis is added to the
statement, and the proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The statement is the conjunction of three propositions, each proved by its own
theorem in this module:

- `presentedDeterminantAssociation : PresentedDeterminantAssociationStatement.{u, uV, uP}`;
- `presentedTwistAssociation : PresentedTwistAssociationStatement.{u, uV, uP, uQ}`;
- `classTwistAssociation : ClassTwistAssociationStatement.{u, uV, uP, uQ}`.

Throughout, `c` is a class family with `IsArithmeticClassFamily c`, `F` and `E` are
number fields with `E / F` Galois and `[CompactSpace (AdeleQuotient F)]`, and
`S` is a finite-dimensional complex representation of `RelativeWeilGroup c F E`.

## The determinant

Let `T` be a cuspidal realization with a presentation `P` such that
`IsWeaklyAssociated S P.spectralSystem`, and let `ω` be a continuous character of
the idele class group with `T.HasCentralCharacter ω`.

1. The published `isWeaklyAssociatedClass_isoClass_iff` turns the pair `(P, hP)`
   into the class-level relation `IsWeaklyAssociatedClass S T.isoClass`.
2. The published `associatedCentralCharacter` (module
   `Langlands.Automorphic.AssociatedCentralCharacterProof`) then gives a Hecke
   character `δ` with
   `FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E δ`,
   together with the clause that every central character of `T` equals `δ`.
3. By that uniqueness clause, `ω = δ`, so
   `FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω`.

## The presented twist

Let `T` and `T'` be cuspidal realizations with presentations `P` (universe `uP`)
and `P'` (universe `uQ`), let `χ` be a Hecke character with
`IsFiniteOrderDeterminantTwist χ T T'`, and suppose
`IsWeaklyAssociated S P.spectralSystem`.

1. **A constructed twist.** The first component of the twist relation says that
   `χ` has finite order. So the published constructions
   `CuspidalOperatorRealization.determinantTwist` and
   `CuspidalSpectralPresentation.determinantTwist` give a cuspidal realization
   `Tχ := T.determinantTwist χ` and a presentation `Pχ := P.determinantTwist χ` of
   it. The realization of `Tχ` is the space of forms `g ↦ χ(det g) f(g)` for `f`
   in the space of `T`.
2. **Association with the constructed twist.**
   `OperatorRealization.isDeterminantMultiple_determinantTwist` shows that the
   realization of `Tχ` is the determinant multiple of that of `T` by `χ`. The
   published `presentedDeterminantMultipleAssociation` (module
   `Langlands.Automorphic.HeckeDeterminantTwistAssociationProof`) then gives
   `IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
   Pχ.spectralSystem`, and `isWeaklyAssociatedClass_isoClass_iff` turns this into
   the class-level relation for `Tχ.isoClass`.
3. **The constructed twist is the given one.**
   `determinantTwist_isFiniteOrderDeterminantTwist` shows
   `IsFiniteOrderDeterminantTwist χ T Tχ`. Two finite-order twists of `T` by the
   same `χ` are equivalent (`IsFiniteOrderDeterminantTwist.target_equivalent`, module
   `Langlands.Automorphic.FiniteOrderDeterminantTwist`), so `Tχ` is equivalent to
   `T'`, and `CuspidalOperatorRealization.isoClass_eq_iff` gives
   `Tχ.isoClass = T'.isoClass`.
4. **Transfer to the given presentation.** The class-level relation therefore
   holds for `T'.isoClass`. The published `IsWeaklyAssociatedClass.presentation`
   (module `Langlands.Automorphic.AssociatedPresentationSpectrum`) passes from a
   class-level witness to every presentation of the representative: the spectral
   systems of two presentations of the same realization have the same Euler
   polynomial wherever both are defined
   (`CuspidalSpectralPresentation.spectralSystem_sameEulerPolynomials`). Applied to
   `P'`, it gives the conclusion
   `IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
   P'.spectralSystem`.

## The class twist

Let `π` and `π'` be cuspidal classes with `π.IsFiniteOrderDeterminantTwist χ π'`
and `IsWeaklyAssociatedClass.{u, uV, uP} S π`.

1. **Representatives.** By `Quotient.inductionOn₂` it suffices to treat
   `π = T.isoClass` and `π' = T'.isoClass`, where the class relation becomes
   `IsFiniteOrderDeterminantTwist χ T T'`.
2. **A source presentation.** `isWeaklyAssociatedClass_isoClass_iff` gives a
   presentation `P` of `T` in universe `uP` with
   `IsWeaklyAssociated S P.spectralSystem`.
3. **A target presentation in universe `uQ`.** The published
   `Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence` (module
   `Langlands.Automorphic.CuspidalAdmissible.Existence`) gives an irreducible
   admissible finite slice of `T'`. Flath's factorization,
   `CuspidalOperatorRealization.exists_presentation_of_finiteSlice` (module
   `Langlands.Automorphic.CuspidalSlicePresentation`), turns it into a presentation
   of `T'` whose local components are irreducible and admissible at every place.
   The small-realization comparison `CuspidalSpectralPresentation.exists_small`
   (module `Langlands.Automorphic.CuspidalPresentationUniverse`) replaces it by a
   presentation `P'` of `T'` with local factors in universe `uQ`.
4. **Conclusion.** `presentedTwistAssociation` applied to `T`, `T'`, `P`, `P'` and
   `χ` gives `IsWeaklyAssociated (FiniteRepresentation.twist
   (reciprocityCharacter c F E χ) S) P'.spectralSystem`, and
   `isWeaklyAssociatedClass_isoClass_iff` turns it into
   `IsWeaklyAssociatedClass.{u, uV, uQ}
   (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) T'.isoClass`.

## Source

G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), 439–455, §2.2, printed p.444 (PDF
p.6), registered as `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`. Henniart
states that association of `S` and `Π` immediately implies
`det S = ω_Π ∘ τ_F`, and moreover that for a quasicharacter `χ` of
`𝔸_F^×/F^×` the representations `(χ ∘ τ_F) ⊗ S` and `(χ ∘ det) ⊗ Π` are
associated. He gives no further argument. The statement's
Markdown explains how the Library proposition specializes these assertions: to
the relative Weil group of an arithmetic class family, to cuspidal realizations
and classes, to finite-order `χ`, and with `τ_F` the pointwise inverse of the
transfer. The proof above does not follow a written argument of Henniart. It
composes the Library's results on the central character of an associated
realization, on twists by determinant multiples, and on the comparison and
existence of spectral presentations.

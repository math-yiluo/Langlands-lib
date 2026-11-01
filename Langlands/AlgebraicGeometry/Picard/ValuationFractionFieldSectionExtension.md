# Actual section extension over valuation domains

This internal adapter applies the published generic-section extension theorem
to a valuation spectrum and transports its conclusion to an arbitrary chosen
fraction field. Its provenance is composition of existing Library results;
it makes no new translation claim about the literature.

Let `R : CommRingCat.{u}` be a valuation domain, let `K : Type u` be any
specified fraction field with its given `R`-algebra structure, and let
`p : X ⟶ Spec R` be separated, locally of finite type, and formally
unramified. Assume `ClosedIrreducibleImages p` on this displayed base.
There is no noetherianity or valuation-rank hypothesis, and fields are included.

`fractionFieldSectionRestriction_bijective_of_valuation` proves that actual
sections of `p` restrict bijectively to actual maps from `Spec K` whose
composite with `p` is `Spec.map (algebraMap R K)`. Injectivity is the
published separatedness consequence. For surjectivity, the published
`valuation_spec_geometricallyUnibranch` supplies the base condition for
`unramifiedGenericSectionExtension`. The published
`fractionFieldSectionRestriction_surjective_iff` transports that
generic residue-field conclusion to the specified fraction field.

`valuationFractionFieldSectionEquiv` packages this bijection as an
equivalence of the two actual-morphism subtypes. Its forward map is
exactly `fractionFieldSectionRestriction R K p`, as its application
lemma states; the inverse is obtained from bijectivity.

`existsUnique_fractionFieldSectionExtension` unpacks surjectivity into a
unique actual morphism `s : Spec R ⟶ X`. It proves both `s ≫ p = 𝟙 (Spec R)`
and that restriction along the original fraction-field algebra map is the
prescribed `sK`. Equality of the restriction subtypes and injectivity give
uniqueness. No change of valuation ring or fraction field occurs.

The closed-image hypothesis remains an input. This module does not prove
that hypothesis from DVR tests, construct a scheme representing bundle
classes, compare such classes with actual bundles, or prove the host
two-axis line-bundle extension statement.

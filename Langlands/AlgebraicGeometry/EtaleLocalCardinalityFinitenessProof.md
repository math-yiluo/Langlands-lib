# Finiteness from constant local geometric cardinality

The theorem
`Langlands.AlgebraicGeometry.etaleLocalCardinalityFiniteness` proves the unchanged
`Langlands.AlgebraicGeometry.EtaleLocalCardinalityFinitenessStatement.{u}`
for every universe `u`. It assumes exactly quasi-compactness, separatedness,
etaleness and the stated constant-cardinality condition on all local bases.
The counted objects are actual field-valued scheme morphisms over the given
base map. The number is chosen before the algebraically closed field and its
algebra structure, as in the target.

For `EtaleLocalCardinality.valuation_extension`, let `A` be a valuation subring
of an algebraically closed field `K`, and let `b : Spec A ⟶ Y`. The Library
`Langlands.LocalGalois.Separable.sepClosed_henselian` makes `A` Henselian, and
`Langlands.LocalGalois.residue_isAlgClosed` makes its residue field `L`
algebraically closed. Define `S` to be the actual lifts of `b`, and define `G`
and `C` to be the actual lifts after restriction to `Spec K` and `Spec L`.

Restriction `S → G` is injective by the uniqueness part of the separated
valuative criterion. Restriction `S → C` is surjective: a closed-fibre lift
defines a point of the pullback of `f` over `Spec A`, and
`HenselianSections.exists_section_of_smooth_of_surjective` lifts this point to
a section, whose projection gives a lift of `b`. Etaleness supplies the
smoothness used here. The residue map `A → L` is surjective, as required by
that section theorem.

The generic lift type `G` is finite by
`finite_lifts_of_quasiCompact_etale`, which requires no finiteness of `f`.
The injection makes `S` finite too. The original hypothesis at the single local
base `(A,b)` gives `Nat.card G = Nat.card C`: both `K` and `L` are permitted
field tests with their natural `A`-algebra structures. The surjection onto `C`
gives `Nat.card C ≤ Nat.card S`, so the injection `S → G` is bijective. Every
specified generic lift therefore extends over `A`. The argument also applies
when the lift types are empty.

For the final theorem, `HasLocalConstantGeometricLiftCardinality.pullback`
transports the original local-base condition to `pullback.snd f g` for an
arbitrary base change `g : T ⟶ Y`. Quasi-compactness, separatedness and
etaleness also survive base change, so `valuation_extension` gives
`HasAlgClosedValuationLifts` for this projection. The helper
`specializingMap_of_algClosed_valuation_lifts` then proves that it lifts
specializations. That helper factors the specialization stalk map through a
valuation subring of the algebraic closure of the source residue field; the
closed point of an extended valuation-ring lift supplies the desired
specialization.

The final geometric step is
`EtaleLocalCardinality.finite_of_specializing_pullbacks`. For any pullback
square, the canonical isomorphism with the chosen pullback transports the
specializing-map property. Thus `f` is universally specializing.
`universallyClosed_eq_universallySpecializing`, together with
quasi-compactness, makes it universally closed. Etaleness supplies local finite
type and local quasi-finiteness. With separatedness this makes `f` proper,
and `IsFinite.of_isProper_of_locallyQuasiFinite` gives `IsFinite f`.

This is an internal derived proof from the named Library and Mathlib theorems.
Its valuative and Henselian route establishes the published target directly;
it does not use the constructible-degree route discussed in the statement's
Markdown. The target pair and its imports are unchanged. All rings and fields
used in the proof remain in the universe of the target, and no noetherian or
additional finiteness hypothesis is introduced.

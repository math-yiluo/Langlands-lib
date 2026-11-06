# The stable-lift formula for opposite normalized Jacquet duality

Author: Worker 937.

This module records an explicit evaluation formula for the natural isomorphism
of `Aubert.General.IwahoriNaturalJacquetDuality`. It packages the formula as a
proposition about an arbitrary natural isomorphism, and it proves that the
stable-pairing construction yields an isomorphism with this property. The
formula is the defining property of the duality in the Proposition of Renard
2026, VI.9.6, and it is the lift property that the formal proof of second
adjointness (the first Theorem of VI.9.6) uses. The packaging is internal and
derived.

The ambient group `G` is any locally compact nonarchimedean group. `U` and `O`
are closed subgroups normalized by a subgroup `M`, and `g : G` is a fixed
element. Write `rU` and `rO` for the literal functors
`normalizedJacquetFunctor U M hU hMU` and `normalizedJacquetFunctor O M hO hMO`
of `General.Parabolic`, and `D` for `SmoothRep.contragredientFunctor`, all on
smooth complex representations with group universe `uG` and carrier universe
`uV`.

## The definition

`IsStableLiftDuality U M O hU hO hMU hMO g Ψ` is a `Prop` about a natural
isomorphism

`Ψ : D ⋙ rU ≅ rO.op ⋙ D`,

that is, a natural family `rU(Ã) ≅ (rO A)~`. It states: for every smooth `A`
and every class `x` in the carrier of `rO.obj A`, there is an open subgroup `W`
of `G` such that for every open subgroup `K ≤ W` that

- is compact,
- satisfies `Jacquet.IsIwahoriContraction K U M O g`, and
- satisfies `Jacquet.IsIwahoriContraction K O M U g⁻¹`,

there is a `K`-fixed vector `v` of `A` with
`Jacquet.Localization.mk A.representation O 1 v = x`, and for every `K`-fixed
smooth functional `Λ` of `A`

`smoothDualPairing (rO.obj A).representation (Ψ.hom.app (op A) (mk Λ)) x =
smoothDualPairing A.representation Λ v`,

where `mk Λ` is `Jacquet.Localization.mk (smoothContragredient A.representation) U 1 Λ`.
In words: `Ψ` pairs the class of `Λ` with `x` by evaluating `Λ` on one
`K`-fixed representative `v` of `x`, and one representative works for all
`K`-fixed `Λ` at once. The three conditions on `K` are exactly the field `Good`
of `Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis`.
The definition assumes nothing about `Ψ` beyond its type, and it does not
require `v` to lie in a stable image; the proofs below produce such a `v`.

## The theorems

All three theorems assume `hc : ∀ m ∈ M, m * g = g * m`,
`hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g`, and the
reciprocity of the actual inverse-half Haar characters,
`hχ : ∀ m : M, (closedInverseHalfCharacter U hU M hMU m : ℂ) *
(closedInverseHalfCharacter O hO M hMO m : ℂ) = 1`.

`exists_isStablePairing_contragredient_normalizedJacquet_iso` works on one
smooth `A` satisfying the `Admits` hypotheses of the stable-pairing data above.
It gives a bilinear pairing `b` between the `U`-coinvariants of the smooth
contragredient and the `O`-coinvariants of `A`, with `IsStablePairing` for that
data, and an isomorphism `E : rU.obj A.contragredient ≅ (rO.obj A).contragredient`
whose evaluation is `b` on representatives through
`Jacquet.Localization.trivialEquiv`. This is the per-object construction of
`IwahoriNaturalJacquetDuality`, now exporting `b` and its stable-pairing
property together with `E`. The proof takes `b` from
`StablePairingData.exists_isStablePairing`, the equivalence on coinvariants from
`IsStablePairing.exists_equiv` (identity equivalence of `M`, reciprocal
characters `hχ`), and transports the lower side to smooth functionals with
`twistEquiv` and `SmoothRep.contragredientIso`.

`exists_isStableLiftDuality_of_admits` assumes `Admits` for every smooth
representation and concludes

`∃ Ψ : D ⋙ rU ≅ rO.op ⋙ D, IsStableLiftDuality U M O hU hO hMU hMO g Ψ`.

It chooses `b A` and `E A` for every `A` with `choose`. Naturality of `E` is
proved by bundled-morphism extensionality, surjectivity of `Localization.mk`,
and `IsStablePairing.natural`, as in `IwahoriNaturalJacquetDuality`; the
components are assembled with `NatIso.ofComponents`. For the lift property,
`StablePairingData.exists_open_stable_lift` gives, for the coinvariant class of
`x`, an open `W` such that every good `K ≤ W` has a `K`-fixed `t` in the stable
image of compression by `g⁻¹` representing that class. Injectivity of
`trivialEquiv` turns this into `Localization.mk A.representation O 1 t = x`.
The pairing formula is the evaluation formula of `E A` followed by the
stable-pairing property of `b A` at `K`, `Λ` and `t`.

`exists_isStableLiftDuality_of_splits` derives the same conclusion from Fitting
splittings, with the hypotheses of
`nonempty_contragredient_normalizedJacquet_iso_of_splits`: `hUpperSplit` gives
`Jacquet.CompactCompressionSplits A.representation A.isSmooth K hK g` for every
smooth `A` and every compact open `K` with `IsIwahoriContraction K U M O g`, and
`hLowerSplit` gives the same for `g⁻¹` when `IsIwahoriContraction K O M U g⁻¹`.
It applies `StablePairingData.admits_of_iwahoriContractions_of_splits` to each
object, with `hUpperSplit` on `A.contragredient` and `hLowerSplit` on `A`, and
then the previous theorem. There is no admissibility or finite-dimensionality
premise. Renard 2026, VI.9.1, Proposition, gives such splittings for every smooth
representation; that proposition is not proved here, so both splitting families
remain hypotheses.

## Provenance

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6,
reformulates (VI.9.6.2) as a Proposition (printed p. 202, PDF p. 208): an
`M`-equivariant duality `⟨.,.⟩_P` between `r_P(V)` and `r_{P̄}(Ṽ)`. Its proof
(printed pp. 202–205, PDF pp. 208–211) uses the decompositions
`V^K = V^K_0 ⊕ V^K_*` and `Ṽ^K = Ṽ^K_0 ⊕ Ṽ^K_*` from the proof of the Jacquet
lemma VI.9.1. On `K_M`-fixed parts it sets `⟨v̄, λ̄⟩ = ⟨s^K_P(v̄), s^K_{P̄}(λ̄)⟩`,
pairing the stable representatives. The formula in `IsStableLiftDuality` is this
definition, with `O` in the role of Renard's `N` and `U` in the role of `N̄`.
Renard's representative `λ` may be replaced by any `K`-fixed representative of
`λ̄`: such representatives differ by an element of `Ṽ^K_0`, which is orthogonal
to `V^K_*`. This replacement is a derived remark, not stated in the source.

The stable-pairing data, its `Admits` hypotheses and the stable-pairing
existence and naturality results come from `Jacquet.StablePairingProof` and
`Jacquet.IwahoriStablePairingData`. Their provenance is Casselman, *Introduction
to admissible representations of p-adic groups*, Chapter III (revision April 29,
2019), III.5–III.6. Packaging the lift as `IsStableLiftDuality`, with one
representative for all `K`-fixed functionals, is a derived formulation, chosen
for the second-adjointness argument.

The module proves no splitting, reciprocity or contraction-basis result for
rational points of a reductive group; these appear as hypotheses.

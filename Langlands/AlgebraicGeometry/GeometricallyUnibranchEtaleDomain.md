# Etale local domains over geometrically unibranch local domains

Authors: Worker 706 and Worker 384.

This internal proof module supplies the geometric-unibranch local-domain step
used in the proof of
`Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionStatement`.
The main theorem is
`Langlands.AlgebraicGeometry.GeometricallyUnibranchEtaleDomain.isDomain_atPrime_of_geometricallyUnibranch`.
For an etale algebra `A` over a domain `R`, a prime `p` of `A`, and an arbitrary
local domain `Rp` realizing the localization of `R` at `p.under R`, it proves
`IsDomain (Localization.AtPrime p)` from `GeometricallyUnibranchDomain Rp`.
The types of `R`, `A`, and `Rp` have independent universes `u`, `v`, and `w`.

## Provenance

The geometric step is used in the proof of the Stacks Project, Lemma 15.109.2,
[tag 0GSC](https://stacks.math.columbia.edu/tag/0GSC). The registered source is
`stacks-dominant-unramified-etale-2026-11-01`; its retained `0GSC.html` is in
`literature/Stacks Project - Dominant unramified morphisms over geometrically unibranch bases (HTML snapshot 2026-11-01)`.
The normalization and tensor-product proof below is an internal derivation of
that step using the Library's unchanged actual normalization predicate and
normal-base etale domain-localization theorem. The helper lemmas package the
implemented derivation rather than separate assertions quoted from the source.

## Implemented proof

`isLocalRing_of_residue_quotient` is a general uniqueness-of-maximal-ideals
criterion. A surjective map `D → E` has kernel contained in every maximal ideal
of `D`. If `E` is integral over a local ring `C` and its spectrum map to
`Spec C` is injective, the images in `E` of any two maximal ideals of `D`
contract to the unique maximal ideal of `C`. Spectrum injectivity makes the
images equal, and surjectivity recovers equality of the original ideals.
Existence of a maximal ideal then supplies a local-ring structure on `D`.

`isLocalRing_tensor_of_integral_of_pure_residue` applies that criterion to
`D = N ⊗[R] B` for local maps from a local ring `R` to local rings `N` and
`B`. The extension `R → N` is integral and its residue-field extension is
purely inseparable. The quotient map is induced by `N → ResidueField N`.
Every maximal ideal of the tensor product contracts to the maximal ideal of
`B`, since the tensor product is integral over `B`. Its contraction to `R`
is therefore maximal; integrality of `N` over `R` then makes its contraction
to `N` maximal. This shows that it contains the quotient kernel, computed
using `Algebra.TensorProduct.rTensor_ker`.

The local source of the induced residue tensor map is
`ResidueField R ⊗[R] B`. The map to `ResidueField N ⊗[R] B` is integral:
base-change cancellation expresses it as an integral extension obtained by
tensoring the residue-field extension, followed by an algebra equivalence.
Mathlib's
`PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable`
gives the required injectivity on prime spectra. This proves the tensor
product local whenever it is nontrivial.

`isDomain_of_local_localization` observes that a local localization `C` of a
ring `A` is also a localization at the contraction of its maximal ideal.
Indeed, all original denominators are units, and every element outside the
contracted ideal maps to a unit in `C`. Consequently, if every prime
localization of `A` is a domain, so is `C`.

`isDomain_of_etale_localization` treats a local localization `B` of an etale
`R`-algebra `A`, where `R` is a geometrically unibranch local domain and
`R → B` is local. Let `N` be the actual normalization
`integralClosure R (FractionRing R)`. The given geometric-unibranch predicate
supplies locality of `N`, locality of `R → N`, and pure inseparability on
residue fields. Mathlib's
`integralClosure.isIntegrallyClosedOfFiniteExtension`, applied to the fraction
field as an extension of itself, supplies integral closedness of `N`.

Etale flatness and localization flatness make `B` flat over `R`. The injection
`R → N` therefore gives an injection `B → N ⊗[R] B`, establishing nontriviality
of the tensor product. The preceding tensor-locality lemma makes it local.
It is a localization of the etale `N`-algebra `N ⊗[R] A` at the images of
the denominators defining `B`.

The published
`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof.domain_localizations_of_etale_of_integrallyClosed`
shows that all prime localizations of `N ⊗[R] A` are domains. Its explicit
Artinian prerequisite is instantiated by the published
`Langlands.CommutativeAlgebra.integrallyClosedInReducedArtinianDomainLocalizations`.
Thus the local tensor product is a domain, and the injection from `B`
descends the domain property. The prime-localization specialization is
`isDomain_atPrime_of_local_base`.

Finally, `isDomain_atPrime_of_geometricallyUnibranch` keeps the arbitrary
model `Rp`. Its algebra equivalence with the canonical base localization,
followed by the induced map of prime localizations, gives a local map
`Rp → B = Localization.AtPrime p`. The tensor product `C = Rp ⊗[R] A` is
etale over `Rp`. It is the localization of `A` at the images of
`(p.under R).primeCompl`, a submonoid of `p.primeCompl`. The canonical tensor
map `C → B` and `IsLocalization.isLocalization_of_submonoid_le` exhibit `B`
as a localization of `C`. The preceding theorem applied to `Rp`, `C`, and
`B` proves the desired domain property. This argument does not require a
finite-presentation claim for `B`, or transport of the geometric-unibranch
predicate to a different localization model.

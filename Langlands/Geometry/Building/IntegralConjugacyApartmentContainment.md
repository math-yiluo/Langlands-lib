# Integral split-torus conjugacy preserves covering apartments

This internal construction joins actual integral split-torus conjugacy to the
published conjugate-apartment realization. The base is a commutative domain
`R` with fraction field `K`, and `M : IntegralModel R K G` is supplied. All
types have arbitrary common universe `u`, and both characteristics are allowed.
No local-field assumption is imposed on `K`.

Suppose `i₁ : T₁.toGrp → M.group` is the target integral torus inclusion,
`i₀ : T₀.toGrp → M.group` is the initial one, and
`A : SplitTorusConjugator i₁ i₀` is supplied. For the original generic torus
`S`, let `i : S.toGrp → G` be its inclusion and `D : KPApartmentData i ω`
its supplied valuation-apartment data. The scheme map underlying `i` is
monomorphic and the structural map of `G` is affine.

An initial point `q : G(K)` and an actual torus isomorphism

    e₀ : S ≅ (T₀)_K

must satisfy the generic square

    i ≫ Int(q) = groupHom(e₀.hom) ≫ M.genericHom i₀.

`SplitTorusConjugator.inverse_translated_generic_comm` derives

    i ≫ Int((A.genericPoint M)⁻¹ * q) =
      groupHom((e₀ ≪≫ (A.torusIso_K).symm).hom) ≫ M.genericHom i₁.

The isomorphism `A.torusIso_K` is the actual pullback of the recorded integral
isomorphism. The proof expands `innerIso_mul_hom`, substitutes the initial
square and `A.inverse_generic_comm M`, then uses composition in the
commutative group-scheme category. No geometric conjugation square is assumed
in addition to the initial one.

`D.integralConjugacyApartmentMap A q` sends `x` to

    ((A.genericPoint M)⁻¹ * q) • D.apartmentMap x.

For an arbitrary subset `Y` of the original `D.ReducedBuilding`,
`subset_range_integralConjugacyApartmentMap` assumes all `M.integralPoints`
fix `Y` pointwise and the `q`-translated chart covers `Y`. The actual inverse
conjugator is in that subgroup, so the same original chart preimage of each
point still maps to that point. This follows from `mul_smul`, inverse closure
of the integral-point subgroup, and its pointwise fixation hypothesis.

`subset_range_integralConjugacy_conjugateApartmentMap` further assumes the
scheme map underlying `M.genericHom i₁` is monomorphic. The derived square
then defines `D.transport` for the target generic torus and the published
`D.conjugateApartmentMap` into the original reduced building. The theorem
proves `Y` is in this actual map's range. It transports each original chart
preimage by `apartmentTransportEquiv` and uses
`conjugateApartmentMap_transport`.

Finally `exists_integralConjugacy_conjugateApartmentMap` does not assume a
conjugator. It assumes `R` is Henselian local, `M.IsSmooth`, a surjective
algebra map `R → k` to a field, connectedness of the actual `k`-fibre of
`M.group`, connected reductivity of `G`, and two closed integral split torus
maps whose specified generic maps are maximal split tori. It retains the
initial chart, initial square, and integral fixation hypotheses above. The
model constructor `M.henselianSplitTorusConjugator` provides `B`; the output
is the actual isomorphism `e`, point `g`, derived square `h`, membership
`g * q⁻¹ ∈ M.integralPoints`, and coverage by
`D.conjugateApartmentMap e g h`. The monicity required by this target chart
follows from generic maximality: the statement installs
`hi₁K.1.2` as the closed-immersion instance before forming the existential
conclusion, and the proof uses the same instance. The membership uses cancellation of `q`
with `q⁻¹` and inverse closure of the same actual integral-point subgroup.

The provenance is derived model and group-action glue. The algebraic input
is `IntegralModel.SplitTorusConjugacy`; the geometric input is
`ConjugateApartmentRealization`. This module constructs no integral model,
initial covering apartment, or special torus containing a prescribed
subtorus. It asserts neither centralizer membership nor a Galois-normalizer
condition. Those are separate conclusions of the fixed-pair
special-apartment statement `UnramifiedFixedPairSpecialApartmentStatement`,
which `unramifiedFixedPairSpecialApartment` (module
`UnramifiedFixedPairSpecialApartmentProof`) proves.

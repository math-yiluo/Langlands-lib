# Discrete free representables from eventual equivariance

This internal construction gives an explicit geometric condition under which
the free lifted representable belongs to the category of discrete sheaves.
It uses the previously constructed `TwistedOver.GlobalLift` and a local
action system `S` on the same twisted category. Assume `S.IsLiftSystem`:
the twist of an admissible action arrow at `h` is `h⁻¹`.

For an ordinary arrow `k : V.obj ⟶ L.obj`, the lemma `precomp_eq_iff`
identifies fixedness under normalized restriction with the equality
`(a h).unop ≫ ι(k) = ι(k) ≫ (L.action h).unop`. It follows by composing
with the inverse global action on one side or the other and using the
faithfulness of `ι`.

`GlobalLift.EventuallyEquivariant S` requires this intertwining equality
for every ordinary arrow to `L.obj`, every admissible source action, and all
elements of some open subgroup contained in the source's acting subgroup.
The subgroup may depend on the arrow and the action. The theorem
`eventuallyEquivariant_iff` proves that this condition is equivalent to
discreteness of the actual lifted presheaf, assuming the ordinary over
category is locally small in the coefficient universe. The proof translates
between ordinary arrows and their `Shrink` representatives and applies
`precomp_eq_iff`.

For a translation-invariant topology `J`, assume `P.RespectsIso`, a
commutative ring `R : Type w`, twisted module sheafification and
`S.HasFiniteEquivariantRefinements (twistedTopology ρ J)`.
`isDiscrete_freeSheaf` applies `LocalActionFree` to prove discreteness of
the previously constructed `L.freeSheaf J R`. `discreteFreeSheaf`
packages this sheaf in the full subcategory of discrete module sheaves.
`discreteFreeSheafHomEquivFixedSections` transports the existing
fixed-section equivalence to morphisms in that full subcategory.

With ordinary module sheafification and pointwise right Kan extensions along
`ι.op` as in `TwistedFreeRepresentable`, `fixedSectionLift_restricts`
states that a fixed section lifted by this equivalence restricts to an
ordinary free-sheaf map representing exactly the same section. It uses the
previous restriction isomorphism and the inverse law of the equivalence.

The provenance is internal. All constructions use the published
normalization, free-sheaf adjunction and preservation of discreteness by
sheafification. Eventual equivariance remains an explicit assumption;
neither existence of analytic lifts nor their eventual compatibility is
proved here. This module supplies no compatible Čech model or global
comparison proof.

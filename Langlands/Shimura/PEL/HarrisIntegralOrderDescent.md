# Actual Harris order actions from normalized full Tate images

Author: Worker 344.

This internal construction recovers an integral action of the original
`harrisHodgePELIntegralOrder` on the actual abelian scheme of a positive
polarized Harris object. The input is its original normalized frame, or
the original existential normalization of a fixed level orbit. The
rational action, abelian scheme, polarization and level remain the given
ones.

The base is a connected, locally noetherian, quasi-separated universe-zero
scheme. The supplied point has an algebraically closed residue field.
The original torsion finite-etale statement and invertibility of every
positive full-index integer on the base are inputs. The fixed-level
specialization also retains the existing finite-fibre and roots-of-unity
geometry arguments required by the original level tower.

`harrisIntegralFrame_order_full_image` first uses the existing equivalence
between frame normalization and equality of the carried source lattice
with the actual full integral Tate image. Every element of the Harris
order preserves that carried lattice by
`harrisIntegralFrameLattice_order_mem`. Equality therefore shows that
each original rational order endomorphism preserves the full integral
Tate image at the supplied geometric point.

`harrisIntegralFrameActionRestriction` applies the published
`Tate.exists_ofHom_eq_of_full_image` to each of those actual rational
endomorphisms. This gives an actual endomorphism of the same abelian
scheme with exactly the prescribed rationalization. The published
`Tate.ofHom_injective` reflects its unit, multiplication, zero and
addition identities from the original rational order action. Thus the
result is a unital ring action, packaged as the existing
`PolarizedWeilLevel.IntegralActionRestriction`, including its exact
agreement equation on every original order element.

`harrisIntegralActionRestriction_unique` proves that any two integral
restrictions on the same object have equal actions. The proof uses the
same injectivity and their prescribed rationalization; this uniqueness
does not require the connectedness, local noetherianity or geometric
point hypotheses used for existence.

`harrisIntegralLevelActionRestriction` chooses the normalized frame
already asserted by the original `HarrisIntegralLevelCondition` and
applies the frame construction. No new level subgroup hypothesis is
needed: order preservation holds for every compatible frame. The
uniqueness theorem makes the resulting integral action independent of
that choice.

The provenance is derived from the published Harris lattice order action,
normalization equivalence and connected integral reflection theorem.
This file does not construct a normalizing isogeny or a normalized
level, realize an arbitrary Tate lattice, change the polarization, or
prove representability. It removes the additional integral order action
input once the original full Tate normalization is supplied.

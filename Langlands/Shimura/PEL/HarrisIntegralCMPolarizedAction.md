# Actual polarized CM actions from the integral joint condition

This is an internal assembly of the published full-order Harris action
condition, geometric polarization base change, and faithfulness witnessed by
an actual Harris adelic frame. It introduces no literature assertion.

Fix the universe-zero arithmetic data, normalized Harris signature charts,
prerequisite package `P`, an abelian scheme `B/S`, its selected dual witness
`W`, and a fixed map `lam` satisfying the existing geometric polarization
predicate. For a quasi-separated test `T/S`, let `a` be an actual integral
Harris-order action on the direct pullback `B_T`, satisfying
`harrisIntegralCMFullActionCondition`. Assume mere existence of an actual
Harris adelic frame at a supplied field-valued point of `T`, for the rational
extension of `a` and the original regular Harris source.

`harrisIntegralCMFullActionPolarizedAction` constructs the existing
`PolarizedWeilLevel.PolarizedAction` on that same direct pullback. Its rational
action is exactly `harrisHodgePELRationalAction`, its dual data are derived
from `W` by canonical pullback, and its polarization is exactly the canonical
pullback of `lam`. The geometric polarization proof uses the named
`P.polarizationBaseChange` premise with those constructed witnesses.
Published relative dual-map additivity supplies the required endomorphism
additivity. The full integral condition supplies rational compatibility with
the unchanged positive auxiliary involution. Only the faithfulness proof
uses the frame: `action_injective_of_adelicFrame` combines noncollapse of the
actual rational endomorphism ring with simplicity of the original Harris
algebra. The frame does not change any of the constructed data.

The two projection theorems record the literal rational action and actual
polarization. `harrisIntegralCMFullActionPolarizedRestriction` retains the
original action `a` as an actual integral restriction on this same polarized
family. Agreement on every element of the full Harris order is the published
rational-extension identity.

When `B` has the prescribed Harris relative dimension,
`harrisIntegralCMFullActionPolarizedAction_determinantDimension` proves the
original normalized determinant-and-dimension condition. The determinant is
the unchanged second conjunct of the joint action condition; the dimension
is transported by actual base change. In particular the normalized reflex
coefficient map remains the one associated to `T.hom` followed by `p`.

The final section specializes this construction to an actual morphism `k`
into `harrisIntegralCMActionLocus`, with the same endomorphism and mixed Hom
representers required by that existing locus. The test is any object of the
full locally noetherian category over `S`. Its actual integral action and
proof of the full-order condition are obtained from
`harrisIntegralCMFullActionLocusHomEquiv k`, rather than supplied separately.
`harrisIntegralCMActionLocusPolarizedAction` constructs the polarized action,
and its `_action` theorem identifies the rational action with the extension
of the literal relative restriction of the raw universal action along the
composite of `k` and the closed inclusion. The corresponding integral
restriction retains that classified action, and the final theorem proves the
same normalized determinant-and-dimension condition.

The inputs assert a polarization only for the supplied ambient family and
supply a pointed adelic frame for the test action. They do not assume the
output polarized action, its faithfulness or its normalized CM condition.
This unit does not construct the ambient moduli scheme, a frame locus or an
adelic level orbit, and it does not prove that arbitrary tests admit such a
frame. It also does not supply the missing mixed Hom representative, prove
admissibility of a representing scheme, smoothness or division projectivity,
or discharge the generic fibre-ampleness premise of integral representative
existence. Those remain separate obligations of the host representability
proof.

# Quasi-split inner forms after a change of base field

Module: `Langlands.GroupScheme.Rational.QuasiSplitInnerFormBaseChange`,
namespace `Langlands.GroupScheme`.

A quasi-split inner-form presentation `qf : QuasiSplitInnerForm G` of a group `G` over
a field `k` (module `Rational/QuasiSplitInnerForm`) consists of a quasi-split model,
its adjoint quotient, local isomorphisms from the model to `G` over the cover
`Spec qf.carrier → Spec k`, and an adjoint-valued cocycle recording their
discrepancy. After a change of base field to `E`, the local isomorphisms and their
discrepancy equation base change to the pulled-back fpqc cover
`Spec (E ⊗_k qf.carrier) → Spec E`, whose coordinate ring can be a product of fields,
so the base-changed data are not again a `QuasiSplitInnerForm`. Triviality of the
base-changed cocycle on that cover gives an isomorphism between `G_E` and the
base-changed quasi-split model by fpqc descent.

## Declarations

- `LocalGroupIso.HasDiscrepancy.baseChange`: let `e : LocalGroupIso G H U` have
  discrepancy cocycle `ξ` for an automorphic action `a` of `A` on `G`
  (`e.HasDiscrepancy a ξ`). For `b : S' ⟶ S`, `V : Over S'` and
  `r : (Over.map b).obj V ⟶ U`, the base-changed family
  `(e.refine r).baseChangeFamily b` has discrepancy cocycle `ξ.baseChange b V r` for
  the base-changed action `a.baseChange b`.
- `IsQuasiSplit.baseChange_of_algebraicExtension`: if `G` is quasi-split over `k` and
  `K/k` is algebraic, `(baseChange (algebraBaseMap k K)).obj G` is quasi-split.
- `QuasiSplitInnerForm.baseChangeIsoOfTrivial (E) (h)`: for a field `E` over `k` and
  `h : (qf.cocycle.baseChangePullback (algebraBaseMap k E)).IsTrivial`, an
  isomorphism `(baseChange (algebraBaseMap k E)).obj qf.model ≅
  (baseChange (algebraBaseMap k E)).obj G`.
- `QuasiSplitInnerForm.isQuasiSplit_baseChange_of_trivial (E) (h)`: under the same
  hypothesis and `E/k` algebraic, `(baseChange (algebraBaseMap k E)).obj G` is
  quasi-split.

## Proofs

`HasDiscrepancy.baseChange`: after applying the injective point comparison
`baseChangePointsEquiv b H Z`, both sides are computed by `baseChangeFamily_toFun`,
`AutomorphicAction.baseChangePointsEquiv_act` and `Cocycle.baseChange_toFun`, and the
equation becomes the original discrepancy equation at the refined test points.

`IsQuasiSplit.baseChange_of_algebraicExtension`: connected reductivity passes to
algebraic extensions (`IsConnectedReductive.baseChange_of_algebraicExtension`) and a
geometric Borel subgroup base-changes to a geometric Borel subgroup
(`IsGeometricBorelSubgroup.baseChange`).

`baseChangeIsoOfTrivial`: the cover `U = Spec qf.carrier → Spec k` is fpqc
(`fieldExtension_fpqc`), hence so is its pullback `U'` over `Spec E`. The family
`(qf.localIso.refine counit).baseChangeFamily b` over `U'` has discrepancy cocycle
`qf.cocycle.baseChangePullback b` for the base-changed inner action, by the first
result; `LocalGroupIso.descendOfTrivial` descends it to an isomorphism.
`isQuasiSplit_baseChange_of_trivial` transports quasi-splitness of the base-changed
model along this isomorphism (`IsQuasiSplit.of_iso`).

## Provenance

Internal. The statements are the base-change compatibility of inner twisting: if the
class of the twisting cocycle becomes trivial over `E`, then `G_E` is isomorphic to the
base change of the quasi-split model. The proof combines the Library's local
isomorphism families, base change of actions and fpqc descent.

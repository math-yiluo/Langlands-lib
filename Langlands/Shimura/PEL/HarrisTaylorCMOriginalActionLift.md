# Original integral CM representatives in the closed action locus

This internal construction connects an original `IntegralCMRepresentative` to
the existing closed Harris integral-action locus. All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic fields and the
abelian schemes have the universe-zero sizes of the existing CM problem.

Fix the original central simple unitary data `D`, normalized signature charts
`C`, named `Prerequisites P`, and an `AdmissibleCMBaseCategory` object `Z`.
Retain the finite-Weil transition, rational adelic comparison, geometric point,
finite-fibre, and torsion inputs used to form an original representative
`x : IntegralCMRepresentative ... U`. The level `U` is arbitrary. In particular,
the construction introduces no smallness assumption on `U`.

Write `B` for `x.data.1.actionObj.abelianScheme`, `a` for
`x.restriction.action`, `W` for the original `dualWitness P x.data.1`, and
`lam` for the original geometric polarization `x.data.1.polarization`. The star
structure throughout is exactly `auxiliaryStarRing D C`, the existing positive
auxiliary left involution. These are objects from this very representative,
including its supplied integral restriction; no replacement family is chosen.

## Original action and its literal pullbacks

`integralCMRepresentative_rationalAction` proves that the canonical rational
extension of `a` is exactly `x.data.1.actionObj.action`. Its proof applies the
existing `harrisHodgePELRationalAction_unique` to the agreement stored in
`x.restriction`. Thus the comparison identifies the original rational action,
rather than only its values at a point or its isogeny class.

`integralCMRepresentative_integralRosati` proves `IntegralRosatiEquations` for
`a` and `lam` with the representative's original chosen dual, inverse Poincare
bundle, evaluation, and dual geometry. The proof applies the rational-to-integral
Rosati equivalence from `HarrisIntegralCMRosatiReflection`, using the integer
units in `Z.property.torsionUnits` and the original dual additivity. It rewrites
the extended action by the preceding equality and uses the involution
compatibility stored in `x.data.1`.

For every `T : Over Z.obj.left`, let `BT` be the direct base change of `B`,
`aT := baseChangeOrderAction T.hom B a`, `WT := W.pullback P T.hom`, and
`lamT := W.pullbackMap P T.hom WT lam`. Then
`integralCMRepresentative_rationalAction_baseChange` identifies the rational
extension of `aT` with
`(rationalBaseChangeEnd T.hom B).comp x.data.1.actionObj.action`.
This follows from the published base-change law for rational extension and the
original-action equality.

`integralCMRepresentative_fullActionCondition` proves
`harrisIntegralCMFullActionCondition D C P Z.obj.hom B W lam T aT`.
For its Rosati conjunct the proof applies `IntegralRosatiEquations.baseChange`
to the original integral equations with the canonical pulled-back dual data.
For its determinant conjunct it uses the displayed equality of rational
actions and
`harrisTaylorCMRationalLieDeterminantCondition_baseChange_of_naturality`.
The required Lie naturality is `Z.property.lieNaturality`, and the original
determinant condition is `x.condition.1`. Consequently the determinant is the
existing normalized Harris determinant, with the existing conjugated reflex
scalar map, on the same pulled-back family and action.

## Actual classification and naturality

The classification results retain an explicit ambient relative-End
representative `R : Over Z.obj.left`, assumed separated and locally of finite
type, together with its natural comparison `eR` on the full category of locally
noetherian tests. Use the already defined
`harrisIntegralCMClosedActionLocus D C P Z.obj.hom B W lam R eR`, its inclusion
`inc`, and the existing actual universal action `aU`.

For every locally noetherian test `Q`,
`integralCMRepresentative_actionLift` defines an actual morphism
`Q.obj ⟶ harrisIntegralCMClosedActionLocus ...`. It applies the inverse of
`harrisIntegralCMClosedActionLocusFullHomEquiv` to `aT` and the full action
condition proved above. The construction uses the existing locus and its
existing Hom equivalence.

`integralCMRepresentative_actionLift_apply` proves the literal formula

```text
(relativeEndRestrict B (actionLift Q ≫ inc)).comp aU
  = baseChangeOrderAction Q.obj.hom B a.
```

The proof rewrites with the value formula of that Hom equivalence and projects
its inverse law to the underlying integral ring homomorphism.
`integralCMRepresentative_actionLift_eq` proves that every actual morphism
with this same restriction equals the constructed morphism, using injectivity
of the equivalence and subtype extensionality.

`integralCMRepresentative_action_restrict` proves that restricting the direct
pullback of the original global action along any arrow `f : T' ⟶ T` gives its
direct pullback to `T'`. It applies Cartier's `restrict_baseChange_map` to each
actual endomorphism. Finally,
`integralCMRepresentative_actionLift_naturality` proves
`f.hom ≫ actionLift Q = actionLift Q'` for every morphism `f : Q' ⟶ Q` of
locally noetherian tests. Uniqueness reduces the assertion to equality of the
restricted actions; the value formula, the preceding restriction law, and
Cartier's `restrict_comp` establish that equality.

## Provenance and retained obligations

This is a derived comparison using the existing integral restriction,
rational-extension uniqueness, Rosati reflection, base-change theorems,
normalized Lie determinant, and closed-action classification. It makes no
additional assertion from external literature. The level data and the
original polarized CM representative remain the supplied data of `x`.

The output classifies an action on this fixed family relative to a supplied
relative-End representative. It does not construct an ordinary ambient moduli
scheme, produce an integral restriction for an arbitrary rational
representative, descend the map through rational-isogeny classes, or represent
the normalized CM presheaf. Scheme existence, output admissibility, smoothness,
division-case projectivity, and the natural comparison on the full
componentwise admissible category remain obligations of
`DivisionCMRepresentabilityStatement`.

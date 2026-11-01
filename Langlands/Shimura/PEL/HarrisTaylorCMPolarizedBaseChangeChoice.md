# Dual-choice independence of normalized CM polarized pullback

Author: Worker 57.

This derived construction proves that the existing actual normalized CM
polarized class and tower pullbacks are independent of their constrained dual
evaluation families. It constructs `classTowerBaseChangeOfExists` from the
existence of these inputs, proves that every actual family computes this map,
and retains the existing square with joint normalized action-class pullback.

The arithmetic input is the actual totally real number field `E`, CM quadratic
extension `F/E`, central simple unitary datum `D` on `A`, and imaginary
quadratic CM field `L` with its displayed algebra structure on `F`. The
signature charts are those on `harrisCMSection E (algebraMap L F) τ₀`. The
single map `p : S ⟶ Spec F` determines the actual reflex structure
`D.harrisTaylorReflexStructure C p`, using the conjugated scalar map of the
imported Harris–Taylor normalization. At the target it is the structure
induced by `b ≫ p`. No independently supplied reflex map occurs.

The source and target are the existing `HarrisNumericalWeilLevel.IsoClass`
and `isoClassTower`, specialized to these induced reflex structures. A class
is a numerical subtype of the determinant subtype of the actual polarized
rational-isogeny quotient. Its numerical image has one actual representative
satisfying the determinant condition, geometric relative dimension
`[E : ℚ] * n²`, and the full central Lie trace test. The imported normalized
comparison identifies these tests with normalized determinant and geometric
dimension on that same representative. The construction retains the original
positive auxiliary left involution, Hodge form, opposite-group Harris level
indices and actual transporter arrows.

All schemes and arithmetic types are in universe zero. The arbitrary morphism
`b : T ⟶ S` is between quasi-separated schemes. The source point is `t ≫ b`
and the target point is `t : Spec Ω ⟶ T`, for a field `Ω`, with the displayed
finite-fibre witnesses. The named tensor comparison, composition, unit
coherence, associativity, left-unitor comparison and symmetry propositions;
Picard-zero pullback, Mumford-bundle Picard-zero and universal base-change
propositions; integral dual naturality and full polarization stability;
relative finite-Weil transition, rational adelic comparison and torsion
finite-etaleness propositions remain inputs. Invertibility of every positive
indexed torsion order, finite etale roots of unity on both bases, Lie
base-change naturality on `S`, and positive ordered-pair dual additivity on
both bases also remain explicit. No flatness of `b` is required.

For each actual source positive polarized action `X`,
`PositivePullbackDualData ... b X` is `DualEvaluationData` indexed by the
actual abelian-scheme pullback of `X.actionObj.abelianScheme`. Its fields
provide a dual-scheme witness, dual geometry, an inverse Poincare line bundle
with its tensor evaluation isomorphism, and dual endomorphism additivity.
Thus two families `dualData₁` and `dualData₂` may choose different such inputs
for the same actual pullback. They supply neither arbitrary output classes
nor a desired independence equation, and no equality of their line bundles
or polarized representatives is claimed.

`classBaseChange_dualData` proves equality of the two existing normalized
class functions at every Harris level. Function extensionality and two uses
of `Subtype.ext` remove only the numerical and determinant proof fields.
The underlying-value formulas of normalized CM, numerical and determinant
pullback reduce the goal to `ambientClassBaseChange_dualData` applied to
`q.val.val`. That imported theorem compares the actual pulled-back
representatives in the original polarized setoid, so the quotient relation
is unchanged. Extensionality at each level and class gives
`classTowerBaseChange_dualData`, equality of the existing natural
transformations, including all subgroup-forgetting and Hecke transporter
arrows.

`classTowerBaseChangeOfExists` accepts
`dualExists : ∀ X, Nonempty (PositivePullbackDualData ... b X)`.
Classical choice selects one constrained input for each actual source object,
and the existing normalized polarized pullback constructs the tower map.
`classTowerBaseChangeOfExists_eq` uses the proved family independence to
identify this map with the map computed by every supplied actual family.
`classTowerBaseChangeOfExists_app` evaluates that equality on each level and
class. The result therefore depends only on the displayed existence premise,
which remains a hypothesis rather than a theorem of this module.

`classTowerBaseChangeOfExists_forgetCMAction` applies the existing actual
normalized forgetful square to the chosen family. In categorical order, the
canonical polarized pullback followed by target forgetting equals source
forgetting followed by the existing `actionClassTowerBaseChange`. Its target
is the constant tower of joint normalized determinant-and-dimension action
classes, and the map on those classes is the actual rational action pullback.

Provenance is an internal consequence of the imported actual pullback,
ambient dual-choice theorem, injective subtype inclusions and existing
forgetful square. This is no new translation of a literature result. It
establishes no dual-existence theorem, removes none of the named construction
premises, and requires no invariance of dimension under arbitrary rational
isomorphism. It does not construct an unpointed PEL moduli functor, prove point
independence or representability, or supply canonical models, scheme levels
or coefficient descent. Those remain obligations of the host geometry task.

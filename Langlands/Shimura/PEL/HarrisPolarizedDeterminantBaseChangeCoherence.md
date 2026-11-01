# Coherence of actual Harris determinant pullback

This derived module proves identity and composition for the existing actual
pointed pullback of determinant-compatible Harris polarized level classes.
It constructs equality transports for their structural-map and point
presentations, then restricts the proved ambient polarized coherence laws
through the existing subtype inclusion. The maps compared are
`harrisClassBaseChange` and `harrisClassTowerBaseChange` from
[HarrisPolarizedDeterminantBaseChange](HarrisPolarizedDeterminantBaseChange.md).

The arithmetic inputs are a central simple unitary datum `D` on `A` over
a totally real number field `E` and its totally complex quadratic extension
`F`, signature charts `C`, and the CM-section proposition `hΦ`. The scalar
towers from `ℚ` through `E` and `F` to `A` remain explicit. The structural
map is an actual morphism
`p : S ⟶ Spec (D.kottwitzCocharacterReflexField C)`.
The imported positive auxiliary left involution, Hodge form, original
`HarrisLevel D` category and opposite-group transporter arrows are retained.

The existing `HarrisIsoClass` is the determinant-compatible subtype of the
actual polarized quotient. Its determinant condition equates the rational
Lie determinant with the reflex polynomial on every finite family in the
integral order, finite Lie chart and smaller open. The condition uses
actual structure-sheaf coefficients pulled along the displayed reflex-field
map. The polarized quotient retains the actual equivariant rational
isomorphism, geometric polarization multiplier and compatible fixed-level
orbit equation. This module uses these existing definitions.

All schemes and arithmetic types have universe zero. The bases are
quasi-separated. The named tensor comparison, composition, unit,
associativity, left-unitor and symmetry propositions, Picard-zero pullback,
Mumford-bundle Picard-zero and universal base-change propositions remain
inputs. The existing pullbacks also retain explicit
`DualAbelianBaseChangeNaturalityStatement` and
`PolarizationBaseChangeStatement` arguments. Identity uses
`LieBaseChangeNaturalityStatement S`; composition uses this proposition
on both `S` and the intermediate base `T`.

The finite Weil transition and torsion finite-etale propositions,
rational profinite-integer/finite-adele comparison, invertibility of all
positive indexed torsion orders, finite etale roots of unity and
ordered-pair dual additivity remain inputs on the applicable bases.
Points have source `Spec Ω` for a field `Ω`, with the displayed
finite-fibre witnesses for finite-etale covers. The three dual families
in composition are independently quantified constrained
`PositivePullbackDualData` on each source object's actual abelian-scheme
pullback. These supply dual construction and evaluation data, rather than
a class map or a coherence equation. No flatness, reducedness,
connectedness or algebraic-closedness premise is introduced.

`harrisClassPresentationEq` transports an equality `p = q` of reflex
structural maps and an equality `s = r` of field-valued points on the
same scheme. Equality elimination makes it the identity on the existing
restricted subtype; proof irrelevance handles the finite-fibre witnesses.
Its value formula `harrisClassPresentationEq_val` is the existing ambient
point-equality transport `ambientClassPointEq`. Thus changing only the
structural-map presentation leaves the ambient class unchanged.
`harrisClassTowerPresentationEq` gives the same transport on the existing
class tower and becomes its identity natural transformation. Its component
formula is `harrisClassTowerPresentationEq_app`.

For identity pullback, the source has structure `p` and point `t ≫ 𝟙 S`,
and the target has structure `𝟙 S ≫ p` and point `t`.
`harrisClassBaseChange_id` identifies the existing pullback with
presentation transport along `(Category.id_comp p).symm` and
`Category.comp_id t`. Function and subtype extensionality, followed by
the transport's value formula, reduce the assertion to the actual ambient
identity law. Extensionality at every original level and class gives
`harrisClassTowerBaseChange_id`.

For composition, let `b : T ⟶ S`, `c : R ⟶ T` and
`t : Spec Ω ⟶ R`. The finite-fibre witnesses are at `t`, `t ≫ c`,
`(t ≫ c) ≫ b` and `t ≫ (c ≫ b)`. Successive pullback starts at
point `(t ≫ c) ≫ b` and ends with structure `c ≫ (b ≫ p)`;
direct pullback starts at point `t ≫ (c ≫ b)` and ends with
structure `(c ≫ b) ≫ p`. Both target points are `t`.

At each original level, `harrisClassBaseChange_comp` proves
`F_c ∘ F_b = moveTarget ∘ F_direct ∘ moveSource`.
The source transport uses the reflexive structural equality and
`Category.assoc t c b`. The target transport uses
`Category.assoc c b p` and the reflexive point equality. Function and
subtype extensionality and the existing underlying-class formulas reduce
the equation to `ambientClassBaseChange_comp` at the underlying class.
The target's reflexive point transport is definitionally the identity.
No compatibility between the three dual families is assumed.

`harrisClassTowerBaseChange_comp` gives the corresponding equality
`F_b ≫ F_c = moveSourceTower ≫ F_direct ≫ moveTargetTower`.
Its proof evaluates at each level and class and applies the class-function
law using the transport component formula. The equality is on the original
Harris transporter category, including its level and Hecke transporter
arrows.

The provenance is internal: equality elimination constructs the transports,
and the injective inclusion into ambient polarized classes restricts the
proved actual ambient identity and composition laws. The imported
determinant and polarized definitions carry their original-source
conventions and citations. This module establishes formal coherence of
those constructions and makes no new original-literature assertion.

These laws concern the existing pointed determinant restriction with its
construction premises. Prescribed dimension, the positive Lie restriction,
normalized CM comparison, an unpointed moduli functor, representability,
canonical models, representing scheme levels and coefficient descent
require their respective constructions in the broader geometric task.

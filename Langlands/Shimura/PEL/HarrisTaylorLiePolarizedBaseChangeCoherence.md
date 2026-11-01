# Coherence of actual Harris positive Lie and dimension pullback

This derived module proves identity and composition for the existing actual
pointed pullback of Harris positive polarized level classes satisfying the
positive Lie and prescribed dimension conditions. It restricts
`HarrisPolarizedBaseChangeIdentity` and `HarrisPolarizedBaseChangeComposition`
through the actual subtype inclusion of `HarrisTaylorLiePolarizedClasses`.
The maps being compared are the existing `classBaseChange`,
`classTowerBaseChange` and `classTowerBaseChangeOfExists`; their construction
and dual-choice independence are imported.

The arithmetic inputs are the central simple unitary datum `D` on the algebra
`A` over the totally real number field `E` and its totally complex quadratic
extension `F`, signature charts `C`, and an imaginary quadratic CM number
field `L` mapping into `F`. The positive auxiliary left involution, actual
Hodge form, original levels `HarrisLevel D` and opposite-group transporter
arrows are those of the imported construction. The structural map is an
actual morphism `p : S ⟶ Spec F`.

The existing class predicate requires one actual polarized level
representative whose abelian scheme has prescribed relative dimension
`[E : ℚ] * n²` and satisfies the full positive Lie condition. That condition
uses the actual positive Lie tensor sheaf, its local rank `n`, and equality
of its two `E` actions. The subtype is an image inside the actual polarized
rational-isomorphism quotient. Its relation retains an actual equivariant
rational isomorphism with both inverse identities, the geometric
polarization multiplier equation and the compatible fixed-orbit equation.
The dimension and Lie witnesses concern the same representative.

All schemes and arithmetic types have universe zero. Each base is
quasi-separated. The tensor comparison, tensor composition, unit,
associativity, left-unitor and symmetry propositions, Picard-zero pullback,
Mumford-bundle Picard-zero property and universal base change remain
explicit inputs. The finite Weil transition proposition, rational
profinite-integer/finite-adele comparison, torsion finite-etale proposition,
invertibility of all positive indexed torsion orders, finite etale
roots of unity and ordered-pair dual additivity remain inputs on the
applicable bases. Points have source `Spec Ω` for a field `Ω`, with the
displayed finite-fibre witnesses for finite-etale covers. Algebraic
closedness, connectedness, local noetherianity, reducedness and flatness
of the base morphisms are not additional hypotheses here.

The dual families are the existing constrained
`HarrisPolarizedWeilLevel.PositivePullbackDualData`: dual-scheme, geometric,
inverse-Poincare, evaluation and endomorphism-additivity data on each source
object's own actual abelian-scheme pullback. They cannot supply an arbitrary
output abelian scheme, polarization, level orbit or class map. The published
theorems `dualAbelianBaseChangeNaturality` and `polarizationBaseChange`
provide the corresponding ambient pullback arguments internally. Their
conclusions are not additional assumptions of this module.

`classPresentationEq` transports both an equality `p = q` of structural
maps and an equality `s = r` of field-valued points on the same base.
It eliminates the two equalities and becomes the identity on the existing
restricted class image. Equalities of the finite-fibre witnesses are handled
by proof irrelevance. The theorem `classPresentationEq_val` identifies its
underlying ambient class with `ambientClassPointEq` at the point equality.
In particular, changing only the structural-map presentation changes no
underlying ambient class. `classTowerPresentationEq` performs the same
transport for the actual class tower and becomes its identity natural
transformation. Its component formula is `classTowerPresentationEq_app`.
These constructions apply to equal presentations; they select no paths
between unequal points.

For identity pullback, the source point is `t ≫ 𝟙 S`, the target point is
`t`, the source structure is `p`, and the target structure is `𝟙 S ≫ p`.
The theorem `classBaseChange_id` says that the existing restricted class
pullback is exactly `classPresentationEq` along
`(Category.id_comp p).symm` and `Category.comp_id t`.
Function extensionality and subtype extensionality reduce this to the
proved actual ambient identity law, after using the underlying-class
formula for presentation transport. Extensionality at every original
level and class proves `classTowerBaseChange_id`.

For composition, let `b : T ⟶ S`, `c : R ⟶ T`, and
`t : Spec Ω ⟶ R`. There are finite-fibre witnesses at `t`, `t ≫ c`,
`(t ≫ c) ≫ b` and `t ≫ (c ≫ b)`. The three constrained dual families for
`b`, `c` and `c ≫ b` are independent. The successive pullback has source
structure `p` and point `(t ≫ c) ≫ b`, and target structure
`c ≫ (b ≫ p)` and point `t`. Direct pullback uses source point
`t ≫ (c ≫ b)` and target structure `(c ≫ b) ≫ p`. Thus both
associativity transports are needed.

At each original level, `classBaseChange_comp` proves
`F_c ∘ F_b = moveTarget ∘ F_direct ∘ moveSource`.
Here `moveSource` is `classPresentationEq` along the reflexive structural
equality and `Category.assoc t c b`; `moveTarget` is along
`Category.assoc c b p` and the reflexive point equality. After function
and subtype extensionality, their underlying-class formulas reduce the
claim to `ambientClassBaseChange_comp` evaluated at the underlying
ambient class. Transport along the reflexive target point equality is
definitionally the identity there.

`classTowerBaseChange_comp` proves the corresponding equality of the
existing natural transformations:
`F_b ≫ F_c = moveSourceTower ≫ F_direct ≫ moveTargetTower`.
Its proof evaluates at each level and restricted class, uses the component
formula for presentation transport, and applies the class-function
equation. These are equalities on the original Harris transporter category,
including its level inclusions and Hecke transporter arrows.

`classTowerBaseChangeOfExists_id` and
`classTowerBaseChangeOfExists_comp` establish the same laws for the existing
choice-independent constructor that takes `∀ X, Nonempty` of the
constrained dual inputs. The proofs apply the preceding tower laws to
the `Classical.choice` families used in that constructor. For composition
the three existence families remain independent. These theorems do not
prove existence of those inputs or equality of the selected data.

The provenance is internal: the imported actual polarized pullbacks preserve
the joint image using the pulled-back source representative, and the proved
ambient coherence supplies equality after its injective inclusion. The
original dimension, positive Lie, polarization and level conventions are
documented with their Harris--Taylor III.1, printed pp.89--91 citations in
[HarrisTaylorLiePolarizedClasses](HarrisTaylorLiePolarizedClasses.md).
This module adds formal coherence for those existing constructions; it
does not assert a new source theorem.

No dimension invariance under arbitrary rational isomorphism is used.
The equalities do not replace a satisfying representative with an
unrelated dimension witness. They supply pointed coherence, with the
stated construction premises, rather than an unpointed moduli functor.
Representability, comparison with geometric-isogeny relations on
arbitrary schemes, canonical models, scheme levels, their Hecke
correspondences and coefficient descent remain obligations of the
broader geometric task.

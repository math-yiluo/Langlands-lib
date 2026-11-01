# Actual CM level lifts at identity field points

This module constructs a right inverse to each original normalized Harris CM
class transition over a field spectrum, pointed by its identity. It also proves
surjectivity over a general base when the existing point-functor automorphism
group is subsingleton. The classes, level category, transporters, and transition
maps are the existing ones. The construction does not introduce an alternative
moduli quotient or replace its polarized-isogeny relation.

The entry definition is
`HarrisTaylorCMWeilLevel.identityPointLevelLift`. For an arrow
`f : U ⟶ V` of `HarrisLevel D`, it sends a class at level V to a class at
level U. The theorem `classMap_identityPointLevelLift` states that the original
`HarrisNumericalWeilLevel.classMap f` sends that lift to the original class.
This is a chosen function of sets of classes, with no assertion of naturality
of the choices or a section morphism between representing schemes.

## Original construction and conventions

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 91 defines the quadruples with an abelian scheme, polarization, compatible
algebra action and invariant orbit of pairing-compatible adelic frames, modulo
polarized isogeny. It specifies the right action by composing the frame with
the translating element and states finite étale level forgetting and the
normal-level Galois-cover assertion. The supplied five-page author publication
and errata list was also read; it contains no correction to this passage.
That observation concerns the supplied list.

This module proves a pointwise surjectivity ingredient of those geometric
assertions by an explicit orbit argument. It does not attribute its proof
route to the book. The source's imaginary quadratic field E, CM field F and
totally real field F⁺ are the present L, F and E respectively.

The actual arithmetic inputs remain the totally real and CM number fields,
the quadratic extension, the central simple unitary datum D, the imaginary
quadratic subfield L, the embedding τ₀ and the prescribed signature charts C.
The determinant test uses `harrisCMSection E (algebraMap L F) τ₀` and
`D.harrisTaylorReflexStructure C p`, retaining the existing Harris–Taylor CM
normalization and reflex map. It is not an assertion about a different
unconjugated reflex convention.

An arrow `f : U ⟶ V` already contains its element and transporter condition in
the original opposite finite-adelic unitary group. The existing
`hodgeLevelFunctor D C` takes it to the frame-similitude transporter. Its
associated map is precisely the map used in `PolarizedWeilLevel.levelTower`
and the existing numerical class tower. All opposite-group and right-action
conventions are inherited from those constructions.

## Implemented lift

The private generic orbit lemma works with commuting actions of Γ and Gᵒᵖ on
X, a subsingleton group Γ, and subgroups U and V of G. If g satisfies
`g⁻¹ U g ≤ V`, the existing translation map on invariant orbits is surjective.
Given a target orbit represented by x, use the U-orbit of `right x g⁻¹`.
Every orbit is Γ-invariant because Γ is subsingleton. Applying the original
translation gives the V-orbit of `right (right x g⁻¹) g = x`. The proof uses
the existing right-action composition and identity equations.

The private representative lemma specializes these actions to the actual
`WeilAdelicFrame` of one `PositivePolarizedAction`. It uses the existing
`weilAdelicFrameRightAction`, `weilAdelicFrameMonodromyAction` and
`weilAdelicFrameActionsComm`. The auxiliary involution and the hodge-form
similitude group are the existing ones. No frame is postulated when the
target orbit is empty: a target orbit itself supplies a representative.

The theorem `classMap_surjective_of_subsingleton` then takes a class at the
target level and uses `HarrisNumericalWeilLevel.classOf_surjective` to obtain
one actual polarized representative X, an orbit z, and both its positive
determinant and numerical witnesses. It lifts only z, keeping X and both
witnesses unchanged. Congruence of `classOf` on that fixed X proves that the
new class maps to the original class. This avoids assuming that dimension is
invariant under every rational isogeny; it uses the same representative that
already carries the joint tests.

For the identity-point specialization, the base is `Spec Ω` and
`p : Spec Ω ⟶ Spec F` is retained. The point is its identity morphism. The
support module `FiniteEtale.IdentityPoint` derives subsingletonness of the
defined automorphism group by naturality on global sections. Thus
`identityPoint_classMap_surjective` has no group-triviality premise.
Algebraic closure of Ω is unnecessary for this stated result; over
algebraically closed fields it applies to the geometric-point situation
needed by the source construction.

The entry uses Mathlib's `Function.surjInv` on this proved surjectivity.
`classMap_identityPointLevelLift` follows from `Function.surjInv_eq`. The
choice uses a nonempty fiber already constructed by the preceding proof,
with no added nonemptiness hypothesis. The result provides classes of
actual polarized objects, rather than an assumed section of the output map.

## Retained inputs and scope

The general-base theorem retains a scheme S, its map to `Spec F`, the actual
point s, the finite-fiber proof hs, quasiseparatedness of S, finite étale roots
of unity, and positive-pair additivity on that base. The identity-point
specialization retains the corresponding inputs on `Spec Ω`, where
quasiseparatedness is provided by the existing scheme instance.

Both constructions also retain the named tensor preservation, composition,
unit, associativity, comparison and symmetry propositions, the named Picard
pullback, Mumford square and universal base-change propositions, the finite
Weil transition proposition, the actual rational/profinite/adelic comparison,
the torsion finite-étale proposition and invertibility of the positive integer
indices on the base. These are the precise prerequisites of the imported
polarized frame and class constructions.

No representability witness is needed for this pointwise class result. It
does not yet transfer surjectivity through geometric-family evaluation and
the disconnected presheaf to an original represented scheme transition.
Scheme-point surjectivity, étaleness, invertibility of the exact residual
comparison, applicable representability/existence, comparison with the source
moduli problem, canonical models and coefficient descent remain further
obligations. Neither freeness, smallness nor normality is needed for the
proved pointwise lift, although they occur in the source's stronger scheme
cover statement.

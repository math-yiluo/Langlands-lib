# Reduction of the connected torus bound

This internal reduction implements the route of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, Corollaries B.8.6–B.8.7 and the proof
of Proposition B.8.8(3), printed pp. 682–684 / PDF pp. 713–715. It retains
bounded-model existence, neutral lifting and a torus norm presentation as
explicit inputs. It does not prove these inputs or the unconditional target.

`UnramifiedTorusConnectedBoundAssemblyStatement` is a Prop-valued definition
of this conditional reduction at arbitrary universe `u`. Its three premises
are `UnramifiedTorusBoundedModelStatement`,
`UnramifiedTorusNeutralSurjectivityStatement` and
`UnramifiedTorusNormPresentationStatement`; its conclusion is exactly the
unchanged `UnramifiedTorusConnectedBoundStatement`.
The theorem `unramifiedTorusConnectedBoundAssembly` proves this implication.
It chooses the affine source torus and the surjective homomorphism with
torus full kernel furnished by the norm-presentation premise, then applies
the supplied-presentation theorem described below.

The helper `map_integralPoints_le_supplied_neutral` applies naturality of
the two integral-point maps to a homomorphism that factors through the
supplied relative identity component.

The theorem `connectedBound_of_neutral_lifting_and_norm_presentation`
assumes a nonarchimedean local field `F`, an affine torus `T` split by the
finite Galois intermediate field `L`, a supplied affine torus `S`, and a
scheme-surjective homomorphism `q : S → T` whose entire scheme-theoretic
kernel is a torus. The image under `q` of the character-valuation kernel of
`S` is assumed to lie in the norm-defined Iwahori subgroup of `T` for this
same `L`. It first chooses smooth maximal-bounded models of the source and
target tori and constructs their relative identity components.
The valuation bound on integral models places the points of the arbitrary
connected model inside the target full model. The proved smooth extension
criterion extends the generic identity to those models. Geometric
connectedness factors it through the target neutral model. The assumed
neutral lifting inclusion lifts these points to the source neutral
model; its point image lies inside that of the source full model. The
assumed norm presentation sends this last subgroup into the norm-defined
Iwahori subgroup.

Thus the presentation and its bounded-image inclusion remain premises of
the supplied-presentation theorem, and existence of such presentations
remains a premise of the global assembly. Neither form proves these inputs.

The source reference is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The reduction is internal derived infrastructure, and its Lean proof
uses the published model, relative-component and valuation interfaces.
The referenced B.8.6 lifting statement is a separate prerequisite; its
proof is not supplied here.

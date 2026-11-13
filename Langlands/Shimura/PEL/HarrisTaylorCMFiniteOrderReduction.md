# Finite-order transfer and local smallness for actual fixed frames

This is an internal reduction for the Harris–Taylor small-level rigidity proof.
It uses the actual rational self-isogeny, the actual compatible adelic frame,
and an element of the original Harris group throughout. It derives its claims
from the existing Tate action, scalar-extension equivalence, source form and
local smallness definitions. It makes no new attribution to external literature.

## The local identity witness

`OriginalLevelLocalIdentityFrameWitness` is a Prop-valued predicate for the
same Harris datum, positive polarized action object `X`, original level `U`,
rational multiplier `q`, action-object self-isomorphism `e`, and polarization
multiple equation `he` used by `OriginalLevelFrameWitness`. It also takes an
actual finite place `v` of the rationals.

The predicate asserts existence of an actual compatible adelic frame `eta`
and an element `u` of the original opposite Harris group such that `u` belongs
to `U.subgroup`, postcomposing `eta` by the actual rational self-isogeny equals
precomposing it by the scalar-extension image of `u`, and the actual projection
`D.rationalInvolution.pointsMap (finiteEvaluation v) (MulOpposite.unop u)` is one.
The predicate does not assert that `u` or `e` is globally the identity.

## Transfer of power relations

`originalElement_pow_eq_one_of_frame_isogeny` assumes the displayed actual
frame equation for `eta` and `u`. If the underlying rational endomorphism of
`e` has its `m`th power equal to one in the actual algebra `End0`, the theorem
proves `u ^ m = 1`. It permits any natural exponent `m`.

The frame equation identifies the rational Tate operator `f` and the source
operator `g` by `f (eta x) = eta (g x)`. Induction gives the same equality for
every power. The algebra homomorphism `rationalEndAction` transfers the assumed
endomorphism power relation to `f`. Injectivity of the frame then gives the
power relation on the source operator. The scalar-extended Harris source form
takes the value one, by `hodgeRationalPELConditions.baseChange_attains_one`;
therefore `bilinearSimilitudes.underlying_injective` recovers the whole
similitude, including its multiplier. Injectivity of the canonical Harris
scalar-extension group equivalence recovers the relation in the original group.
The local simple-ring instance is supplied by `D.simple` and introduces no
new assumption on the Harris datum.

`isOfFinOrder_originalElement_of_frame_isogeny` applies this power transfer
to a positive exponent witnessing finite order of the same actual rational
endomorphism. Thus the original frame element `u` has finite order.

## Applying actual local smallness

`exists_localIdentity_frame_of_levelIso_fixed` assumes that `U` is small at
`v`, that the actual level transport by `q`, `e`, and `he` fixes an actual
invariant level orbit, and that the underlying rational endomorphism of `e`
has finite order. It proves `OriginalLevelLocalIdentityFrameWitness` for these
data.

The proof first uses
`exists_frame_original_element_of_levelIso_fixed` to obtain `eta`, `u`, original
subgroup membership, and the actual frame equation. The finite-order transfer
above supplies a positive power relation for `u`. Passing first through
`MulOpposite.unop` and then through the actual coefficient-evaluation monoid
homomorphism supplies finite order of its local projection. The given
`LevelSmallAt` condition makes that local projection one.

These arguments work over the same general base and geometric point as the
frame construction; algebraic closedness and characteristic zero are not
required for this reduction. The finite-order premise remains explicit.
Proving finite order from positivity, polarization and level compactness,
and deducing identity of the actual rational self-isogeny from the local
identity witness, remain obligations of the exact small-level rigidity task.

# Strong transformations through the explicit hom-universe lift

This is an internal categorical construction for the actual point-fibre atlas
comparison. It uses the existing `PseudofunctorHomLift` construction and the
Mathlib definitions of strong transformation and fully faithful functor. It
introduces no geometric existence assumption or external literature assertion.

For two category-valued pseudofunctors on `LocallyDiscrete Cᵒᵖ` and a strong
transformation `α` between them, `homLiftStrongTrans` applies the explicit
morphism-universe lift to each component functor and each naturality isomorphism.
It leaves the object action unchanged. The identity and composition coherence
equalities follow by lowering each lifted component to the corresponding
equality of the original transformation. Naturality in 2-morphisms follows from
local discreteness of the source.

`liftFunctorFullyFaithful` lifts the supplied inverse on each Hom set. The inverse
equations are the original equations after applying the injectivity of `ULift`.
`homLiftStrongTransFullyFaithful` applies that construction to each fibre.
`homLiftStrongTrans_component` and `homLiftStrongTrans_obj` record the exact
component and object formulas. All base, fibre and lift universes are arbitrary.

# Nonzero primitive coordinates in unipotent bialgebras

Worker 1448. Derived algebraic helper.

`exists_nonzero_primitive_of_oneMemStable` uses the existing coordinate unipotence
predicate `OneMemStable K B`. If the bialgebra has a nonconstant element,
it produces a nonzero element with counit zero and comultiplication
`1 ⊗ b + b ⊗ 1`. It does not require smoothness, perfectness, finite type,
or commutativity of the multiplication.

The implementation passes to the module quotient of `B` by its constant
line. Right translations descend to this quotient. Left translations
by functionals vanishing on `1` kill constants and give a jointly
injective family of intertwining maps from the quotient to `B`.
Joint injectivity follows by composing any dual functional on the quotient
with the quotient map and applying the counit.

Apply the published `exists_invariant` to the finite regular span of
a nonconstant element, mapped into the quotient. A nonzero invariant
class has a representative `b`; replace it by `b - ε(b) 1`. Its translation
formula is `rightAct g b = g(1) b + g(b) 1`, because the difference is
constant and the counit determines that constant. Tensor separation
then gives the primitive identity.

This is an original implementation derived from the existing coordinate
interfaces. It supplies an algebraic step toward the perfect-field
split-unipotent target. It does not supply a smooth kernel, a surjective
quotient, or a split series.

The three preceding lemmas record the counit of right translation, stability
of the constant line under right translation, and vanishing of left
translation on constants when its functional kills `1`. They are proved
directly from the existing translation identities. The main theorem uses
`Bialgebra.IsPrimitiveElem`, whose counit-zero consequence is part of the
standard primitive-element interface.

`nonzeroPrimitive hB hconst` packages a chosen witness of this existence
theorem as a subtype element carrying proofs of nonvanishing and the
primitive identity. This is the named definition supplied by this module;
the argument above proves the existence needed for its choice.

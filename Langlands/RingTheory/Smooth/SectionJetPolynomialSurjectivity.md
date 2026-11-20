# Surjectivity of polynomial coordinates on section jets

Let `ε : A →ₐ[R] R` be an augmentation of a commutative algebra and write
`I = ker ε`. Suppose a family `z : σ → A` lies in `I` and its classes
generate the conormal module `I/I²` over `R`. The index type may be
arbitrary. Polynomial evaluation at `z` respects the augmentation at
zero and induces a surjection on the actual section jets at every order.
The source augmentation ideal is the ideal of variables.

The implementation uses conormal generation to express the class of each
element of `I` as an `R`-linear combination of finitely many classes of
the `z i`. Evaluating the same combination of variables gives an
approximation modulo `I²`. For each power `I^m`, ideal-product induction
gives an approximation modulo `I^(m+1)`. Successive corrections starting
with a constant term then give a polynomial representative for every
element of each jet quotient.

This is a derived form of the approximation argument in
`Algebra.SectionJet.Coordinates`. The approximation uses spanning of the
conormal classes and applies independently of their linear independence
or the smoothness of the target algebra. It supplies the surjectivity
hypothesis for the coefficient-ideal criterion used in the construction
of a section smoothness locus corresponding to SGA 3, Exposé XV,
Lemma 5.4.

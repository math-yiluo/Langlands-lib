# Normalizers of dense bounded subgroups in the adjoint quotient

`DenseBoundedNormalizerAdjointStatement` is an internal prerequisite for the
matrix proof of KP Proposition 2.2.16. It is a statement awaiting proof.

Let `F` be a nonarchimedean local field, `G` a connected reductive `F`-group,
and `q : G → A` an actual adjoint quotient by the full scheme center. If a
subgroup `H ⊆ G(F)` is algebraically bounded and its actual rational-point
family is Zariski dense in `G`, then the image of its abstract normalizer
under `q(F)` is algebraically bounded in `A(F)`.

Density means that the union of the scheme-point images of the inclusion
`H → G(F)` is dense. Boundedness is the regular-function predicate
`IsAlgebraicallyBounded`, on the actual affine group schemes. The statement
uses neither openness nor a norm-kernel hypothesis on `H`. It asserts
boundedness of the normalizer's image, without asserting that `q(F)` is
surjective.

This is an internal reformulation of the part of KP Proposition 2.2.16 that
controls conjugation modulo the center, rather than a translation of a
separately numbered result in the book. A proposed proof uses a closed
faithful matrix representation of `G`. Zariski density lets finitely many
matrices from `H` span the same vector space as all point matrices.
Conjugation by the normalizer preserves the bounded set of matrices from
`H`; the spanning matrices therefore bound that conjugation action and its
inverse. One must construct the corresponding faithful representation of
the actual adjoint quotient and justify the resulting algebraic
boundedness. These construction and boundedness steps are proof
obligations, not premises supplied by this statement.

The motivating source is Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Proposition 2.2.16, printed pp. 77–78, PDF pp. 108–109,
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The book proves the semisimple case by its Lemma 2.2.15; the proposed matrix
argument is a different route. No proof of this prerequisite is asserted
here.

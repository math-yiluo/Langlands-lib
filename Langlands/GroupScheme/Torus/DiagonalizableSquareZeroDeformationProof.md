# Lifting a specified diagonalizable reduction through a square-zero ideal

`Langlands.GroupScheme.diagonalizableSquareZeroDeformation` proves
`Langlands.GroupScheme.DiagonalizableSquareZeroDeformationStatement.{u}`.
For the square-zero ideal `J` of the arbitrary commutative base ring `R`, set
`S = R/J`. The theorem lifts the supplied isomorphism of the actual base
changes and proves equality with its homomorphism after reduction. The
character group `N` can have torsion.

The proof uses affine Hopf coordinates. The coordinate Hopf algebra `A` of
`G` is flat over `R` by flatness of the structure morphism. The coordinate
model for the diagonalizable group is `R[N]`. The natural scalar-extension
comparisons for Hopf spectra transport the specified isomorphism to a
bialgebra isomorphism from `S ⊗[R] R[N]` to `S ⊗[R] A`.

The inverse of the scalar-tensor algebra equivalence identifies `S[N]` with
`S ⊗[R] R[N]` as bialgebras. It takes each group-algebra monomial to a
group-like element `1 ⊗ Xⁿ`, so it preserves comultiplication and counit on
the algebra generators. The lemma `exists_bialgEquiv_lift_of_baseChange`
in `CompleteLocalDeformation/Lifting`
gives a bialgebra isomorphism `R[N] ≃ A`. Its scalar extension agrees with the
transported map on every monomial of `S[N]`, which determines the entire
bialgebra map. Taking Hopf spectra and using naturality of the
scalar-extension comparisons gives the original equality with `f₀.hom`.

The statement is the square-zero step in Brian Conrad, *Reductive group
schemes* (2014), p. 289, in the proof of Theorem B.3.2(2). The formal proof
uses the Library's group-like lifting by convolution idempotents. The
registered source is `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

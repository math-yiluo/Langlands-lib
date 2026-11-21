# Generic isomorphisms extend after the adjoint action

`Langlands.GroupScheme.reductiveLocalIntegerIsomorphism` proves
`Langlands.GroupScheme.ReductiveLocalIntegerIsomorphismStatement.{u}` for
every universe `u`. For every prescribed generic isomorphism
`f : G_F ≅ G'_F` and every adjoint quotient `q : G_F ⟶ A`, it gives a
point `x : A(F)` and an isomorphism `Φ : G ≅ G'` over the integers of
`F` such that `Φ_F(g) = f(x|_T · g)` for every test scheme `T` over `F`
and every `g ∈ G_F(T)`.

The Lean proof applies
`reductiveLocalIntegerIsomorphism_of_genericInnerIsomorphismTorsorExistence`
to `genericInnerIsomorphismTorsorExistence`. The existence theorem gives
the integral torsor over the extended outer class of `f`, with a
prescribed generic point evaluating to `f`. The reduction specializes
this existence theorem to the ring of integers of `F`. It obtains an
integral section of the torsor by applying Lang's theorem over the
finite residue field and lifting the resulting point by smoothness and
adic completeness.

Evaluation at the integral section gives `Φ`. The inverse of the
unique generic adjoint point carrying the prescribed generic point to
the generic image of the section gives the correction. The torsor
action law gives the required precomposition identity on all test
schemes. The canonical comparison of adjoint quotients transports the
correction to `A(F)`. It intertwines the two inner actions because
after fpqc local lifts both actions are conjugation.

The source is Brian Conrad, *Reductive group schemes* (2014),
Theorem 7.2.16 and proof, pp. 261–262. The registered source
`conrad-2014-reductive-group-schemes` has SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

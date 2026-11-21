# Étale descent on recognized open neighborhoods

Consider actual maps `q : A ⟶ B` and `f : B ⟶ C` between saturated
presentations. Take a finite étale neighborhood of `q` from `D` to `U`
and one of the composite from `E` to `T`, with `E` open and contained
in `D`. For a recognized affinoid `W` in `T`, its preimage in `E` is a
recognized affinoid `P`. The descent theorem assumes that the image
`q(P)` has a recognized affinoid `H` in `B`. This is the preimage of
`W` inside `q(E)`.

The `q` neighborhood recognizes the preimage `Q` of `H` in `D`. The
equality `P = Q ∩ E` makes `P` clopen in the chart of `Q`. The actual
restriction has norm-controlled lifts from the clopen Weierstrass chart,
and its flatness and unramifiedness at every point give algebraic finite
étaleness. The restriction identity for the bounded pullbacks gives
finite étaleness of `q` from `P` to `H`. The chart equation and the
image equality give spectral surjectivity. The algebra descent theorem
applies to the bounded maps from `W` to `H` to `P`. This establishes
finite étaleness from `q(E)` to `T` if the assumed recognition holds
for every `W`.

For étale `q` and étale composite, `finiteEtaleSourceNeighborhoods`
chooses the two neighborhoods at a lifting point. The small finite
neighborhood theorem shrinks the source of the composite's neighborhood
into the source of the cover's neighborhood. Étale openness makes
`q(E)` open. The finite étale criterion then gives all-pieces étaleness
of `f` at the covered point, with the image recognition hypothesis above.

The argument uses the Library's full-recognition pair systems, clopen
restrictions and finite Banach algebra descent. The field is complete and
ultrametric and may be trivially normed. The field, space and atlas-index
universes are independent.

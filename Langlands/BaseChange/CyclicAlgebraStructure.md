# Residue-field coordinates for a cyclic algebra

`Langlands.BaseChange.CyclicAlgebraStructure.exists_coordinates` constructs the
coordinate data used in the reduction of the norm lemma to a cyclic field extension.
The data keep track of the chosen maximal ideal, its residue field, and the
quotient maps giving each coordinate of the algebra isomorphism. This is an
internal formulation of the product decomposition in Henniart–Lemaire, §I.2.1.

The cyclic algebra has positive finite dimension and is reduced. After restriction
of scalars from the field, it is Artinian, so `IsArtinianRing.equivPi` supplies the
Chinese remainder isomorphism to the product of its maximal-ideal quotients.
The pullback of ideals by `σ` is a permutation. The characteristic idempotent of
any orbit in the product is fixed by `σ`. It is therefore an element of the base
field. Its value `1` at an ideal in the orbit forces that field element to be `1`,
so every maximal ideal is in the orbit.

With `m` a chosen maximal ideal, the successive pullbacks of `m` number the
`r` coordinates. Their period `r` divides the order `l` of `σ`. The power `σ^i`
identifies the `i`-th residue field with `E ⧸ m.asIdeal`. The resulting algebra
isomorphism has `i`-th coordinate the image of `σ^i x` in that residue field.
The automorphism `τ` is induced by `σ^r` on the same quotient.

The residue field has dimension `d = l / r` by the product isomorphism. A power
`τ^k` is the identity exactly when `σ^(r*k)` is the identity, using surjectivity
of the quotient map in one direction and all coordinates in the other. This
gives `orderOf τ = d`. A residue-field element fixed by `τ` lifts to the element
whose coordinates are all that element. The coordinate formulas make the lift
fixed by `σ`, so it belongs to the base field. These facts establish
`IsCyclicAlgebra τ d`.

## Source

Henniart and Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.1, printed pp. 10–11,
PDF pp. 18–19. Source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.

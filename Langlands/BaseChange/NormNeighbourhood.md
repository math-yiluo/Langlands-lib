# Norm neighbourhoods in the general linear group

`Langlands.BaseChange.normNeighbourhood` proves
`Langlands.BaseChange.NormNeighbourhoodStatement.{u, v}`. The proof uses the complete
nontrivially normed field structure `LocalGalois.localNormedField` on the given
nonarchimedean local field, with its original field operations and topology. It equips
the matrix space with the operator norm and uses the topology on its group of units.

## Norms near the identity

For `l > 0`, the strict derivative of `x ↦ x^l` at the identity matrix is
`X ↦ (l : F) • X`. This map is surjective in characteristic zero. The local
surjectivity theorem for strict derivatives shows that the image of the open
set of invertible matrices under the power map is a neighbourhood of the identity.
Pulling it back along the units inclusion gives a neighbourhood of `1` in `GL_n(F)`
whose elements are `l`-th powers. Base change of an `l`-th root gives a norm
representative because the base-changed element is fixed by every `σ^i`.

## Regular elliptic elements near the identity

For `n > 0`, the proof takes the Library's finite unramified extension `L/F`
of degree `n` and chooses a primitive element `α`. In a basis of `L` over `F`,
the matrix of multiplication by `1 + tα` varies continuously with `t` and is
the identity at `t = 0`. The units inclusion is an open embedding, so any
given neighbourhood of `1` in `GL_n(F)` contains one of these matrices with
`t ≠ 0`. The element `1 + tα` generates `L`. Cayley–Hamilton gives divisibility
of its multiplication matrix's characteristic polynomial by its minimal
polynomial, and both are monic of degree `n`. Thus the characteristic
polynomial is irreducible and separable.

## Openness at a regular semisimple norm

At a regular semisimple matrix `A = γ₀.val`, write
`S(c) = 1 + ∑ i : Fin n, c i • A^i`. On the open set where `g` and `S(c)` are
units, the map on matrix and coefficient pairs is
`(g, c) ↦ g * A * S(c)^l * g⁻¹`. Its strict derivative at `(1, 0)` sends
`(X, c)` to

```
X * A - A * X + A * ((l : F) • ∑ i : Fin n, c i • A^i).
```

The matrix decomposition in [RegularMatrixSlice](RegularMatrixSlice.md) solves
the commutator-plus-polynomial equation at `A⁻¹ * Y` for any target matrix `Y`.
Left multiplication of the commutator direction by `A` and division of the
coefficients by `l` give a preimage of `Y` for the displayed derivative. Local
surjectivity then gives a neighbourhood of `γ₀` whose elements have the form
`g * γ₀ * s^l * g⁻¹`, where `s.val = S(c)`. The cyclic-norm product calculation
shows that all these elements are norms. [NormPolynomialPerturbation](NormPolynomialPerturbation.md)

The resultant of the characteristic polynomial with its derivative is a
continuous function of the matrix entries. The proof evaluates the resultant
of the universal characteristic polynomial under entrywise specialization,
with the degree bounds given by `n` and `n - 1`. Its nonvanishing is equivalent
to separability. At each regular semisimple norm, intersecting this open locus
with the neighbourhood of norms gives a neighbourhood of regular semisimple norms.

The three arguments formalize the local ingredients used in Henniart–Lemaire,
*Changement de base et induction automorphe pour GL_n en caractéristique non
nulle*, Mém. SMF 124 (2011), II.2.10 and II.6.7–8, printed pp. 71 and 123–124.
The registered source is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.

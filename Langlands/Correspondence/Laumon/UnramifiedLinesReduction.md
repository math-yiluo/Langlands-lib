# Unramified lines from the field monodromy and ramification comparisons

`UnramifiedLineMonodromyReduction` is the implication from
`FiniteEtaleFieldMonodromyStatement` and `HenselianCompletionRamificationStatement` to
`UnramifiedLineMonodromyStatement`, at the universe of the fields. The proof
`unramifiedLineMonodromy_of_comparisons` uses the homeomorphism clause of the finite étale
comparison and the signed Frobenius power equation of the completion ramification comparison.

## Descent and realization

The kernel of the continuous open surjection `localResidueDegree` is inertia. The unramified
character `χ` therefore factors through a continuous character `ψ` of `ProfiniteIntegers`.
For a Weil element of integer degree `n`, its projection has residue degree `frobenius n`,
where the integer is viewed multiplicatively in the domain of `frobenius`. The character
value there is `c ^ n`, with `c = unramifiedScalar k ℓ χ`, since the chosen geometric
Frobenius lift has degree one. This proves the Weil group clause.

Composing `ψ` with `Galois.FiniteField.toProfiniteIntegers k` gives a continuous character of
the Galois group of `k` with geometric Frobenius value `c`. The homeomorphism
`fieldGaloisToAut` transfers the character to the group of automorphisms of the finite étale
fiber functor. Its scalar action on a universe lift of `PadicAlgCl ℓ` is continuous in each
matrix coefficient. Essential surjectivity of `universalLisseMonodromy_isEquivalenceAt`
realizes this action as the stalk of a lisse sheaf. The equivariant linear isomorphism gives
rank one and the geometric Frobenius action by `c`. The existence of this sheaf implies that
the choice in `unramifiedLine k ℓ χ` satisfies `IsUnramifiedLineFor`.

## Pullback to the ends

An embedding of `AlgebraicClosure k` into `endGenericClosure k` over `k` exists because the
target is separably closed and `k` is perfect. Its image lies in `endConstants k`. Write
`q = Nat.card k`. The signed power equation on the end constants identifies the action of
the completion restriction of a degree `n` Weil element on this image. For `n ≥ 0`, the
proof applies the equation to the image of the inverse `q^n` Frobenius iterate of a constant.
For `n < 0`, the equation gives the `q^(-n)` power directly. Thus the embedding intertwines
the completion restriction with the `n`-th power of geometric Frobenius.

`fieldMonodromyBaseChange_commutes` transfers this equality to the stalk of the pullback
along `puncturedEndToBase k e`. The action there is the scalar `c ^ n`, which is `χ` of the
Weil projection by the character formula. To extend the scalar identity to every Galois
element, fix a stalk vector and apply a linear functional to each side. The resulting
matrix coefficients are continuous by the universal monodromy equivalence, the finite étale
comparison for the end field, the continuous map `henselianCompletionGalois`, and the
continuity of `χ`. The local Weil projection has dense image, so the coefficients agree
everywhere. Linear functionals separate stalk vectors, giving the pullback identity for
each end.

## Source

The arithmetic input is Laumon’s inertia exact sequence and definition of a geometrically
constant module (Laumon 1987, (2.1.1), p. 151 and (2.1.5), p. 154). The construction applies
these to a rank-one character in the equal-characteristic setting of Henniart 1988, §§4.1–4.3,
pp. 509–510. The reduction expresses the realization and the pullback in terms of the
Library’s field monodromy and completion comparisons.

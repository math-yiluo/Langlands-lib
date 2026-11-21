# Factoring a finite map through a finite translation subgroup

`finiteTranslationQuotientFactorization` takes a finite morphism over a field
from an abelian variety to a scheme. A finite closed subgroup of the variety
preserves the map under translation on all scheme-valued points. The lemma
gives another abelian variety and a finite flat surjection through which the
map factors. The surjection agrees on the subgroup inclusion and the constant
map at the unit.

The finite subgroup is flat and locally finitely presented over the field.
The translation action therefore gives a finite locally free equivalence
relation. Invariance places each orbit in the inverse image of an affine
neighborhood of its image point. The inverse image is affine because the map
is finite. The finite locally free quotient theorem produces the quotient
scheme and its coequalizer, which supplies the desired factorization.
The descended commutative group law kills the subgroup. Smoothness descends
along the quotient group homomorphism. Properness and geometric connectedness
follow from the corresponding properties of the original abelian variety.

This is the finite subgroup quotient step used in the quotient and dimension
argument for Lefschetz separation. It adapts the Library's finite étale
quotient construction by using the finite invariant map for the affine orbit
condition and flat descent for smoothness. The motivating use of finite
subgroup quotients is in Mumford, *Abelian Varieties*, §17, printed pp. 164–165
(PDF p. 87 of `mumford-abelian-varieties-full-scan`).

# Quadratic cocycles in an opposite cell

`GaloisCocycle.exists_torusCocycle_of_oppositeCell` implements the
coordinate calculation of Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), Lemma 6.28, printed pp. 369–370. On a quadratic
field cover, suppose a twisted cocycle value at the nonidentity
coefficient automorphism `σ` has coordinates `u t σ(v)` for supplied
subgroup and torus points. The multiplication in these coordinates is
assumed injective, as it is for the opposite Bruhat cell.

The cocycle law gives `σ(u t σ(v)) = (u t σ(v))⁻¹`. Applying inversion
and comparing the ordered coordinates gives `v = u⁻¹`. Twisting by `u`
therefore leaves the single middle factor `t`. The Galois coefficients
at `1` and `σ` now lie in the image of the torus on the field cover.
The finite-Galois factorization theorem lifts the entire natural
cocycle through the monomorphic torus map. Its value at `σ` is exactly
`t`, and its image is cohomologous to the input on the same cover.

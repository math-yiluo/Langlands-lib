# Concrete archimedean Weil groups

Author: Worker 2.

The namespace is `Langlands.Weil.Archimedean`. `ComplexWeil` is `Complex` units,
with Mathlib's usual units topology, which records both the value and its inverse.
All coefficients and carriers in this pair are the actual real and complex
numbers in `Type`, with no field, algebraic-closure, or group parameter.

`RealWeil` has carrier `ComplexWeil × Bool`. The coordinates `(z,b)` represent
`z j^b`. For `b,c` in `{0,1}`, multiplication is

\[
 (z,b)(w,c)=\bigl(z\,\overline{w}^{\,b}w^{1-b}(-1)^{bc},
                    b+c\bmod 2\bigr).
\]

Here the displayed expression means `z*w` when `b=0` and `z*conjugate(w)` when
`b=1`, followed by the sign `-1` precisely when both parities are true.
The inverse is `(z⁻¹,0)` on the first component and
`(-conjugate(z⁻¹),1)` on the second. The identity is `(1,false)`.
The Lean `Group` instance proves associativity, both identity laws and inverse
cancellation by parity cases and complex-unit identities.

The topology is the product topology on complex units and discrete `Bool`.
`coordinates` is the identity homeomorphism with this product.
The `IsTopologicalGroup` instance proves multiplication and inversion continuous;
its case distinctions use the clopen parity fibers. `complexPart` is a continuous
coordinate function, with no claim of multiplicativity.

The continuous homomorphism `RealWeil.ofComplex` sends `z` to `(z,false)`.
`isOpenEmbedding_ofComplex` proves that this is an embedding onto an open subgroup.
The element `j=(1,true)` satisfies the proved identities
`j*j = ofComplex (-1)` and
`j * ofComplex z * j⁻¹ = ofComplex (conjugate z)`.
Thus the multiplication includes the nontrivial cocycle required by the real
Weil group.

`RealWeil.toGalois` takes values in Mathlib's actual real algebra automorphism
group `Complex ≃ₐ[Real] Complex`, equipped with its Krull topology. Its value is
the identity on the first component and `Complex.conjAe` on the second.
Continuity uses the discrete finite automorphism group.
`toGalois_surjective` follows from Mathlib's classification of real algebra
endomorphisms of the complex field as identity or conjugation.
`ker_toGalois` identifies its kernel with the range of `ofComplex`.
This is a concrete complex/real Galois map, without an assumed global Galois
representation or local-global embedding.

`complexNorm` is the continuous homomorphism `z ↦ |z|²` into real units.
Its values are positive. `RealWeil.norm` takes `(z,b)` to the same `|z|²`;
its multiplicativity and continuity are proved. It is positive on every element,
restricts to `complexNorm`, and has value `1` on `j`.
`componentSign` takes `(z,b)` to `(-1)^b`.
Their product `abelianCoordinate` is the continuous homomorphism
`(z,b) ↦ (-1)^b |z|²`, restricting to the complex norm and taking `j` to `-1`.
This pair constructs that homomorphism but does not assert an isomorphism from
the topological abelianization or a reciprocity theorem.

## Source correspondence

J. Tate, *Number theoretic background*, in *Automorphic Forms, Representations
and L-Functions*, Corvallis 1979, Part II, section 1.4.3, printed p.6
(PDF p.15), gives `W_C = C×` and the real group with two cosets,
`j²=-1`, and conjugation action, together with the real Galois projection and
the real abelianization convention. These passages were read directly.
Our coordinate order `z j^b` implements those relations; the explicit cocycle
formula and parity proofs are derived implementation details.
Section 1.4.6, printed p.7 (PDF p.16), defines the Weil norm via the normalized
local absolute value and its extension. This gives `|z|²` on complex units and
value `1` on `j`, as used here. In particular `complexNorm` uses the squared
complex modulus, not the unsquared Euclidean modulus.

The retained original is `Part II.pdf` in the Central-Library folder
`Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979`.
Source ID: `tate-1979-number-theoretic-background`.
SHA256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

This is one group-construction prerequisite of the broader global task.
Finite-dimensional representations and their isomorphism classes, identification
of the abelian coordinate with reciprocity, global Weil groups, and local-global
maps remain separate construction or theorem obligations. No Gamma factor,
additive character, representation classification, or existence theorem is
included as a field or assumed result.

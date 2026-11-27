# Geometric realization of Harris's algebraic coefficients

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p. 98 (PDF p. 106), realizes cohomology
with irreducible algebraic coefficients in the cohomology of a power
of the universal abelian family. The representation is a summand of
`ν^t ⊗ (V^∨)^{⊗m}` with `2t-m=-w`. Their two operators are the factorwise
degree-one selector and an expression in the endomorphism algebra of the
abelian family and the symmetric group. The Tate twist is `+t`.
The registered source ID is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Harris 1999, proof of Theorem 5.7(i), printed pp. 313–314, invokes the
geometric origin of these coefficient systems for the Hodge–Tate comparison.
The registered source ID is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

`HarrisCMGeometricCoefficientProjectorStatement` is at a fixed small level
with the actual choice of representing scheme, for the division-algebra
data and an absolutely irreducible algebraic coefficient representation `ρ`
whose scalars act by `u^{-w}` for `u ∈ Kˣ`. The source of the isomorphism is the finite
completion realization `cmHarrisLambdaCohomology`, extended from `K_λ`
to its algebraic closure `Λ`. The rational prime of that completion
agrees with the prime used by the original Harris coefficient system.
The construction uses `q`, the representability hypothesis for all
small levels, together with the PEL moduli and base-change inputs used
to define those levels. The coefficient system also uses relative dual
existence and geometry and geometric coarse-level rigidity. The Lean
parameters give localization choices for derived categories of the two
coefficient rings and their small-étale module sheaves.

In the right frame convention of Harris–Taylor III.2, printed pp. 94–96,
the coefficient representation `ξ` is read from the section law
`f(ηg) = ξ(g)⁻¹ f(η)`. In the Library the left deck map sends the frame
`η` to `ηg⁻¹`. The residual action on coefficients is
`ρ((unop g)⁻¹)`. Invariance under this action and inverse deck pullback
gives `f(ηg⁻¹) = ρ((unop g)⁻¹) f(η)`. Thus on the frame group
`ξ(g) = ρ((unop g)⁻¹)`. A scalar `u` on the frame acts by `u^w` in `ξ`.
The standard covariant frame representation has scalar degree one, so
its dual has degree minus one. The similitude character `ν` has scalar
degree two. The relation in Lean is therefore `2t-m=w`.

The universal class specifies on each actual connected component a
chosen abelian scheme with its rational PEL action. Its powers and the
permutations are the actual relative constructions. The selector is
evaluated on multiplication-by-two pullbacks with bound `2*d*n²`, where
`d = [E:ℚ]` for the totally real subfield `E` of the CM field. To express
the remaining geometric operator, a free-algebra expression uses the
PEL-algebra elements on the factors and factor permutations, with
coefficients in `Λ`. The PEL-algebra elements are evaluated by clearing
denominators in the actual abelian-scheme endomorphism group and
scaling the resulting pullback by the inverse integer in `Λ`. Permutations are evaluated on geometric cohomology,
which includes the signs from permuting the degree-one cup products.
One expression is evaluated on every component and in every
total degree. The proposition asserts that its composition with the
selector is idempotent. It then identifies degree `i` of the given
coefficient cohomology with the product of the projected images in
constant-coefficient degree `i+m` on the componentwise powers. The
isomorphism intertwines the actual Galois action on the source with
geometric pullback on the target, multiplied by the cyclotomic
character to power `t`.

A proof uses the relative degree-one comparison with the dual Tate
module and the compatible coefficient sheaves made from its level
trivializations. The multiplier of the transporter from a marked Tate
module to its Galois translate is the cyclotomic character by the
polarization's Weil pairing. This identifies the `ν^t` factor of the
frame representation with the positive Tate twist on cohomology. For
example, the ordinary representation `ρ = ν` has `w = -2`. Its
transported coefficient character is `ν⁻¹`, giving cyclotomic power
minus one and scalar exponent `-2` in the relation `2t-m=w`.
The relative Künneth formula isolates the tensor powers.
The idempotent of the representation gives the
remaining projection and the single projected Leray row gives the
shift in degree. The statement concerns Galois-equivariant realization
at the specified level. Compatibility for the Hecke correspondences
requires comparison of these projectors and trace maps across levels.

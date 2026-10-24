# Involution compatibility and rational-unit multiples

This module isolates the compatibility equation and rational-unit scaling
used in Harris--Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Section III.1, printed p.91 (PDF p.99). The third bullet
in the definition of the moduli quadruple requires

`λ ∘ i(b) = i(b*)^∨ ∘ λ`

for every `b`. The following paragraph uses nonzero rational multiples of
polarizations in the equivalence relation. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

## Actual rational maps and the equation

Fix an abelian scheme `A` over any scheme `S`. Its dual `DA` is the existing
`dualAbelianSchemeFromEvaluation`, with an actual universal rigidified
Picard-zero family, geometry of its parameter scheme, and an inverse
line bundle with evaluation. The seven tensor/pullback coherence and
stability statements remain explicit inputs. The additional pointwise
input `DualSchemeMapAdditivity preservation stability A A hA hA`
permits the existing `dualHom0` on rational endomorphisms.

For a ring `R` with `StarRing R` and a unital ring homomorphism
`i : R →+* End0 A`, `IsInvolutionCompatible i lam` means

`∀ b, comp0 A A DA (i b) lam = comp0 A DA DA lam (dualHom0 (i (star b)))`.

Here `lam : Hom0 A DA`, `Hom0` is the actual rationalized Hom group
`ℚ ⊗[ℤ] (A ⟶ DA)`, and `comp0 f g` means first `f`, then `g`.
Thus the left side is `λ ∘ i(b)` and the right side is
`i(b*)^∨ ∘ λ`. The dual map is the existing rational extension of
the map constructed by Poincare pullback. An arbitrary function on
endomorphisms is not supplied as dualization.

Mathlib's `StarRing` expresses an additive, multiplicatively reversing
involution. The equation makes sense for any such ring, and hence for
the rational algebra with involution in Harris--Taylor. Neither a
rational-algebra structure nor positivity of the involution is needed
to state this particular equation. If `lam` is an integral polarization,
apply this predicate to `homToHom0 lam`. The predicate itself imposes
only the equation, so that it is also meaningful on rational multiples.

## Rational-unit scaling and implemented proofs

`rationalUnitMultiple q f` is `(q : ℚ) • f` for `q : ℚˣ` and an
actual `f : Hom0 A B`. The unit group enforces a nonzero scalar.
`rationalUnitMultiple_homToHom0` identifies the result for an integral
homomorphism with the pure tensor `(q : ℚ) ⊗ f`.

The one, product, and inverse formulas follow from the module action.
`IsRationalUnitMultiple f g` means that `f` equals such a multiple
of `g`. Its reflexivity, symmetry, and transitivity are proved using,
respectively, the unit `1`, the inverse unit, and the product of units.

`IsInvolutionCompatible.smul` proves that every rational scalar
preserves the equation, by bilinearity of `comp0`.
`isInvolutionCompatible_rationalUnitMultiple_iff` proves preservation
and reflection for a unit: the reverse implication scales by its
inverse. Consequently
`isInvolutionCompatible_iff_of_isRationalUnitMultiple` makes the
equation independent of the representative of a rational-unit orbit.

## Scope and provenance

The equation and the choice of rational units come from the cited
page. Their extension to arbitrary bases and arbitrary rational
homomorphisms is an internal algebraic generalization using the
existing conditional dual construction. The source's connected,
locally noetherian base, dimension, additional action-compatibility
condition, and level structure belong to its full moduli problem;
this module does not define that moduli problem or its equivalence
relation between different abelian schemes.

Rational scaling takes place in `Hom0`. No claim is made that every
rational multiple is an integral homomorphism or is a polarization.
The equation alone does not imply ampleness or the isogeny condition.
No dual-existence, additivity, or tensor-coherence theorem is proved
here; the named hypotheses above remain explicit.

# Actual finite-order determinant multiplication on automorphic forms

Author: Worker 2. This internal construction restricts actual multiplication
by a finite-order Hecke determinant character to the existing complex automorphic
forms. The number field `F : Type u` and natural rank are arbitrary, including
rank zero. All function carriers and their inherited topologies are unchanged.

`mem_automorphic_determinantMultiplier` combines the existing preservation
arguments on the actual finite-smooth functions. Smoothness and a common open
finite stabilizer are already built into their multiplier. Whole enveloping
commutation gives simultaneous center finiteness. The exact subgroup-orbit
image formula gives finiteness under the standard infinite compact. Pointwise
norm equality gives precisely the original polynomial-growth bound on each
finite slice. These are all conditions defining the existing
`automorphicSubrepresentation`; none is supplied as an assumption.

The inverse character gives an actual automorphic preimage of every form.
This proves submodule image equality and defines
`AutomorphicForms.finiteOrderDeterminantMultiplier` by restriction of the
existing continuous complex-linear equivalence. Its inverse is actual
multiplication by the inverse character. The forward and inverse evaluation
formulas and the finite right-action identity retain the convention
`R(d) Mχ = χ(det(ofFinite d)) Mχ R(d)`.

The enveloping formula is an equality in the existing finite-smooth ambient
space: differentiating the multiplied form gives the multiplier of the
differentiated original function. This unit does not assume or assert that
every such differentiated function belongs to the full automorphic space.

With the explicit `CompactSpace (AdeleQuotient F)` instance required by the
existing normalized constant terms, the published actual constant-term
multiplier formula preserves cuspidality in both character directions.
Restricting the automorphic equivalence therefore defines
`CuspidalAutomorphicForms.finiteOrderDeterminantMultiplier` on the existing
cuspidal automorphic carrier. Its underlying automorphic form, evaluation,
and finite right-translation identities are proved.

The provenance is direct internal assembly of `SmoothDeterminantMultiplier`,
`DifferentialDeterminantMultiplier`, `FiniteGrowthDeterminantMultiplier`,
`Forms`, `CuspidalForms`, and `CuspidalDeterminantMultiplier`. No new
original-literature comparison is claimed. The stable operator core,
full operator realizations, their irreducibility and isomorphism classes,
specified central-character transport, and total twists on those objects
remain subsequent constructions.

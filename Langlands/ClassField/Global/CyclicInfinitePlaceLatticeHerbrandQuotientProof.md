# The cyclic Herbrand formula for the infinite-place integer lattice

The theorem
`Langlands.ClassField.Global.cyclicInfinitePlaceLatticeHerbrandQuotient.{u,v}`
proves the published proposition
`CyclicInfinitePlaceLatticeHerbrandQuotient.{u,v}`.
For number fields `F : Type u` and `E : Type v`, with an `F`-algebra
structure on `E`, a Galois extension and cyclic group `G = E ≃ₐ[F] E`,
it asserts finiteness of both ordinary cohomology groups
`infinitePlaceLatticeCohomology F E 1` and
`infinitePlaceLatticeCohomology F E 2`, and the equality

\[
 |H^2(G,N)|=\operatorname{archimedeanHerbrandFactor}(F,E)\,|H^1(G,N)|.
\]

Here `N` is the actual `infinitePlaceLatticeRepresentation F E`, over
`NormalizedTwoCocycle.CoefficientScalars.{v} = ULift.{v} ℤ`.
Its finite function realization has the arithmetic action
`(g f)(w) = f(g⁻¹ • w)`. The factor is the product of stabilizer orders,
one per orbit of actual infinite places. The universes `u` and `v`
are independent. The theorem includes degree-one extensions.

## Implemented proof

The proof specializes
`Langlands.Cohomology.Herbrand.hasHerbrandQuotient_ofMulAction`
from `Langlands.Cohomology.HerbrandPermutation` to
`G = E ≃ₐ[F] E` and `X = NumberField.InfinitePlace E`.
First, `Module.Finite.of_restrictScalars_finite ℚ F E` supplies
finite dimensionality of `E` over `F`, allowing typeclass inference
to establish finiteness of its automorphism group. The set of
infinite places is finite because `E` is a number field; cyclicity
is an explicit hypothesis of the target.

The generic permutation representation is definitionally the
published infinite-place representation, and its
`orbitStabilizerProduct` is definitionally
`archimedeanHerbrandFactor F E`. Thus the specialization uses the
existing arithmetic action, coefficient ring, cohomology and factor
directly. Finally, `hasHerbrandQuotient_natCast_iff` converts the
rational cardinal equality in `HasHerbrandQuotient` to the required
natural-number equality while retaining both finiteness conclusions.

The imported permutation calculation uses a generator `g` of the
finite cyclic group and its norm operator. Orbit sums and telescoping
show that `ker(norm) / range(ρ(g) - 1)` is zero. Residues at orbit
representatives identify `ker(ρ(g) - 1) / range(norm)` with a finite
product of integer cyclic quotients whose moduli are the stabilizer
orders. The cyclic cohomology comparisons then give ordinary `H¹`
and `H²`. Positivity of the stabilizer product establishes finiteness
of `H²`; the cardinal equality is not being inferred from cardinal
values of possibly infinite groups.

## Provenance

This is a derived specialization of Milne, *Class Field Theory*,
v4.03 (2020), Chapter VII, proof of Proposition 3.1, printed p.209
(PDF p.218). Milne takes `N = Hom(T, ℤ)` with inverse-precomposition
action and computes its Herbrand quotient by orbit decomposition,
Shapiro's lemma and the trivial-integer calculation. Here `T` is
the set of all infinite places. The imported Lean calculation uses
the direct norm and generator argument described above.

The specialization adapter was supplied by Worker 269 and checked
and documented by Worker 53. It uses no global idele-class
cohomology theorem and proves only the infinite-place permutation
lattice formula.

Registered source: `milne-2020-class-field-theory`,
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`,
SHA256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

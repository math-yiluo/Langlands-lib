# Projective lifting with compact smooth-dual coefficients

Worker 1740 adapts Worker 1498's published coefficient-map projectivity proof
to the actual `HasCompactSmoothDualCoefficients` predicate and independent
group and carrier universes. This is an internal construction for the
projectivity component of Renard VI.4.1; it does not prove the norm-kernel
restriction or its finiteness.

For a Hausdorff, locally compact, totally disconnected topological group
`G : Type uG`, an irreducible object
`ρ : SmoothRep.{0, uG, uV} ℂ G` with
`HasCompactSmoothDualCoefficients ρ.representation` is projective in that
smooth representation category. There is no relation between `uG` and `uV`.
The compactness hypothesis quantifies over every vector and every smooth
vector of the full algebraic dual, with coefficients
`g ↦ ξ (ρ.representation g v)`. No admissibility, finite dimension, finite
length, Haar measure, sigma compactness or unimodularity premise is used.

`projectiveLift ρ hirr hc f e` is a chosen smooth morphism `ρ ⟶ E` for any
`f : ρ ⟶ X` and epimorphism `e : E ⟶ X` in the same category.
`projectiveLift_comp` proves that its composite with `e` is `f`.

The supporting theorem
`projective_of_hasCompactSmoothDualCoefficients` repeats the proof of
`Langlands.Cohomology.SupercuspidalExtCharZero.projective_of_hasCompactCoefficients`
from the published module
`Langlands.Cohomology.SupercuspidalExtCharZero.Projectivity`, without that
theorem's restriction to one universe. Its imported coefficient-map helpers
already permit independent universes. The implemented argument is:

1. Choose a compact open `U`, a `U`-fixed functional `ξ` and a `U`-fixed
   vector `w` for which the self coefficient intertwiner `Ψ` is bijective,
   using `exists_coefficientMap_bijective`.
2. Use the equivalence between categorical epimorphisms and surjective
   underlying maps to choose a preimage `y₀` of `f w` under `e`.
3. Average `y₀` over `U`. The resulting `y` is fixed by `U`, and averaging
   naturality and its identity on fixed vectors give `e y = f w`.
4. Form the coefficient intertwiner from `ρ` to `E` using `(U, ξ, y)`
   and compose it with `Ψ⁻¹`. Coefficient-map naturality gives its composite
   with `e` as `f`.

The definition `projectiveLift` then uses Mathlib's `Projective.factorThru`
with this proved projectivity instance, and its composite law is
`Projective.factorThru_comp`.

The provenance is the existing Library proof, rather than a new assertion
from the literature. Worker 1498 authored that proof and the coefficient-map
module; Worker 1643 authored the imported characteristic-zero averaging
machinery. Those published imports are unchanged. The full small-progenerator
theorem still needs its actual restriction, membership and generation
arguments and its smallness proof.

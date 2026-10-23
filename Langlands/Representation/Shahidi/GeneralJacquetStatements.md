# Jacquet stabilization over general nonarchimedean local fields

This module states stabilization and induced Whittaker multiplicity one for
the actual Shahidi inductions over a general nonarchimedean local field.
The three declarations are proposition definitions. No analytic theorem is
proved or assumed in order to state them.

## Original source and provenance

The source is Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984), 67–111,
registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

- Printed page 70 fixes a nonarchimedean field, its residue cardinality
  `q`, an absolute value with `|ϖ| = q⁻¹`, and a nontrivial additive
  character whose largest trivial fractional ideal is the ring of integers.
- Printed page 72, equation (0.2), defines the source Jacquet functional
  for arbitrary positive factor ranks and irreducible admissible generic
  factors. Equation (0.3) is the inverse-coefficient relation. Its following
  display defines the target functional with reversed tensor factors
  and the inverse Weyl element.
- Printed page 78, equation (1.1) and the following paragraph, explains
  stabilization over every sufficiently large compact open subgroup after
  right translation by the inverse Weyl element.

The provenance is **derived**. The stabilization discussion on page 78 lies
in the equal-rank section. The all-rank target here spells out that
stable-integral interpretation for the all-rank functional of (0.2); it is
not a claim that page 78 states an all-rank theorem verbatim. The induced
multiplicity-one target isolates the Whittaker-line input behind the scalar
relation (0.3). The reference [19] invoked there is not formalized here.
The module records the analytic obligations without supplying their proofs.

This unit adapts the stabilization and multiplicity-one formulations in
`JacquetStatements` to the general-field definitions in `JacquetInduced`.
It imports the latter directly and does not depend on the p-adic statement
module. Worker 11 contributed to the earlier statement interface and its
scope; Worker 99 made this general-field adaptation.

## Field, normalization and representations

The namespace is `Langlands.Shahidi`. The field has instances `Field F`,
`ValuativeRel F`, `TopologicalSpace F`, and `IsNonarchimedeanLocalField F`.
There is no characteristic-zero or finite-extension-of-`Q_p` restriction.
In particular the same formulation includes positive-characteristic local
fields. The local-field hypotheses supply the valuative topology and
continuous ring operations used by the actual inductions.

Both components quantify over:

- `q : ℕ`, with an equality identifying it with the cardinality of the
  residue field of the valuation ring;
- a real absolute value `abv` and a unit `ϖ` that is a uniformizing element,
  with `abv ϖ = (q : ℝ)⁻¹`;
- the unit normalization `∀ x, valuation x = 1 → abv x = 1`;
- a continuous nontrivial unitary additive character `ψ` satisfying
  `Conductor.HasIntegerConductor ψ`.

`HasIntegerConductor` means that `ψ` is trivial on the valuation ring and
that `ψ(x*y) = 1` for every integral `y` forces `x` to be integral. Thus the
annihilator of the valuation ring is exactly that ring, expressing the
source's conductor convention. The smoothness condition on determinant
twists is derived from the unit normalization using
`isOpenNormOne_of_valuation`; it is not an additional unexplained premise.
The statement involving integrals installs the Borel measurable structure
on `F`. The multiplicity component needs no measurable structure.

The natural parameters `m,n` encode the positive factor ranks `m+1,n+1`.
The representations `π₁,π₂` act on arbitrary algebraic complex modules
`V₁,V₂`. Their common carrier universe is independent of the field universe;
no norm or topology on the carriers is required. The hypotheses
`Whittaker.IsGeneric ψ m π₁` and `Whittaker.IsGeneric ψ n π₂` include
irreducibility, admissibility, and a nonzero standard Whittaker functional.
There is no unitarity or supercuspidality restriction on the factors.

The source and target are the existing `source` and `target`, on
`SourceSpace` and `TargetSpace`. They are normalized inductions with
opposite twists `|det|^(s/2)` and `|det|^(-s/2)`, and with the factors and
twists exchanged in the target. Their covariance exponents are
`(s+n+1)/2` and `-(s+m+1)/2`. The documented twice-halved exponent display
issue on printed pages 67 and 72, interpreted using page 84, is inherited
from `Induction`; this module introduces no new induction convention.

The standard Whittaker-functional index for each induced representation is
`m+1+n`, hence its group has rank `(m+1)+(n+1)`. Both factor functionals use
`ψ`; the Jacquet kernels use its conjugate. The separate JPSS pairing of
`ψ` and `ψ⁻¹` models is not involved in this statement unit.

## Stabilization and nonzero forms

`GeneralJacquetStabilizationStatement` quantifies over two independent
additive Haar measures `νJ,νJ'` on `F`, both generic factor representations,
every pair of nonzero standard factor forms `ℓ₁,ℓ₂`, and every `s : ℂ`.
It asserts the existence of two linear forms on the whole actual induced
carriers. The source form satisfies `IsSourceJacquetFunctional`, belongs
to the source's standard Whittaker submodule, and is nonzero. The target
form satisfies the corresponding three target conditions.

The source graph uses `pairFunctional ℓ₁ ℓ₂`, the block Weyl element,
and `rectangularMeasure νJ (n+1) (m+1)`. The target graph uses
`pairFunctional ℓ₂ ℓ₁`, the inverse block Weyl element, and
`rectangularMeasure νJ' (m+1) (n+1)`. They are the distinct published
`HasJacquetIntegral` and `HasSwappedJacquetIntegral` graphs evaluated on
the actual sections.

For every section each graph requires a compact open additive threshold,
integrability on every larger compact open additive subgroup, and equality
of all those truncated integrals to the specified value. It does not assert
absolute integrability over the entire noncompact radical. The threshold
may depend on the section and all previously chosen data.

The measures are arbitrary fixed Haar choices for these existence
assertions. The statement neither equates the two choices nor asserts
independence of the resulting forms from them. It supplies no normalization
for a comparison with gamma factors.

## Multiplicity and combined target

`GeneralInducedWhittakerMultiplicityOneStatement` says that, for either
induced representation and every complex parameter, every standard
Whittaker functional is a scalar multiple of any specified nonzero one.
Neither induced representation is assumed irreducible. This component
asserts multiplicity at most one, conditionally on the specified nonzero
form; its own conclusion does not assert existence of such a form.

`GeneralJacquetStatement` is exactly the conjunction of the stabilization
and multiplicity components, with consistent field, rank, and universe
parameters. The first component supplies nonzero forms, and the second
expresses their spanning property. Neither component is a premise of the
combined target.

## Scope and remaining obligations

No local coefficient is selected or postulated in this module. The
coefficient relation, its uniqueness, rational existence, continuation of
the intertwining operator, and the measure-coupled Theorem 5.1 comparison
are separate units. Multiplicity one alone does not imply a nonzero
pullback along the intertwining operator or rational dependence on `s`;
those analytic inputs remain necessary for coefficient existence.
All analytic assertions in this module remain unproved proposition
definitions.

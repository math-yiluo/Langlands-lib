# Coefficient finiteness of actual universal normalized induction

Worker 1761.

This module states the flatness and admissibility consequences of Renard
VI.8.1–2 for the existing universal normalized induction. It supplies
Prop-valued statements, without proofs of these consequences.

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed pp.187–191 / PDF pp.193–197 were read in full. VI.8.1's
Proposition and Remark, pp.187–188, identify admissible flat coefficient
modules with those whose compact-open fixed modules are finite projective.
The universal unramified example on p.189 supplies the inducing coefficient
module. VI.8.2, pp.189–190, gives normalized induction flatness, the finite
double-coset description (VI.8.2.1), and preservation of admissibility.
The specialization corollary is on p.191.

## Actual models and targets

For a supplied actual parabolic root presentation `r`, the coefficient
algebra is exactly `RegularAlgebra r`, the existing concrete
evaluation-generated algebra for `parabolicLeviRationalNormCharacters r`.
This family is indexed by every rational character of the Levi scheme.
There is no chosen finite norm subfamily or replacement common kernel.

The inducing action is the published action on
`RegularAlgebra r ⊗[ℂ] E`, inflated along the supplied actual semidirect
projection and multiplied by the positive half-modulus on the full
parabolic. The carrier is exactly `Induced r h hU σ`, and its group action
is exactly `inducedRepresentation r h hU σ` from
[`UnramifiedRationalNormalizedModels`](UnramifiedRationalNormalizedModels.md).
This is the full space of covariant functions with a uniform open right
stabilizer. The coefficient action is pointwise multiplication on the
function values. The local module instance merely exposes the existing
submodule module structure.

`UniversalInducedFlatness r h hU σ` is
`Module.Flat (RegularAlgebra r) (Induced r h hU σ)`.
`UniversalInducedFixedFiniteProjectivity r h hU σ` asks, for every open
subgroup `K` of the actual ambient rational-point group with compact
underlying set, for both `Module.Finite` and `Module.Projective` over
`RegularAlgebra r` of
`fixedVectors (inducedRepresentation r h hU σ) K.toSubgroup`.
`UniversalInducedCoefficientFiniteness` is the conjunction of those two
targets.

The finite-projectivity conclusion is the permitted finiteness consequence
of the source's finite double-coset formula. No finite representatives or
isomorphism are supplied as assumptions. The source first establishes
flatness from the finite fixed-space description and then admissibility;
VI.8.1 converts flat admissibility to finite projectivity. This module
packages that consequence for the specific existing universal inducing
tensor.

## Scope and retained structural comparisons

`UniversalInducedCoefficientFinitenessStatement.{u, uV}` quantifies over
every nonarchimedean local field `F : Type u`, every connected reductive
group scheme `G` over `F`, the supplied actual parabolic, Levi, split
component and geometric unipotent radical, and every admissible
`π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)`.
The representation carrier universe `uV` is independent of `u`. There is
no finite-dimensionality, finite-length, splitness, characteristic-zero or
matrix-group assumption.

Connected reductivity supplies ambient affineness. The statement explicitly
retains affineness of the supplied Levi, local compactness and the
nonarchimedean group structure for the canonical ambient rational-point
topology. It also retains:

- the semidirect decomposition of the literal parabolic image into the
  literal Levi and unipotent images;
- closedness of that actual unipotent image;
- continuity of the actual semidirect projection;
- `CompactSpace (Induction.LeftQuotient (ParabolicPoints p))`, compactness
  of the literal left coset space of the actual parabolic image.

These are explicit structural comparisons in the Library formulation.
This module does not prove them from connected reductivity. The
geometric-unipotent-radical hypothesis identifies the supplied `n` with the
intended radical; its point-level decomposition and closedness are still
displayed separately. The quotient premise is about the existing literal
quotient, rather than an unrelated supplied compact space.

The only representation hypothesis is `π.IsAdmissible`; smoothness is
already part of `SmoothRep`. Flatness, finite generation of induced fixed
spaces and projectivity all occur in the conclusion. No model record
assumes any of them. Smoothness and covariance of the actual model are
already proved in the imported module. The actual function-evaluation
specialization map is published in
[`UnramifiedRationalNormalizedSpecialization`](UnramifiedRationalNormalizedSpecialization.md);
its scalar-extension comparison and bijectivity target are a separate unit.
This statement makes no assumption of comparison bijectivity.

## Provenance boundary

The adaptation to literal scheme-point subgroups, the existing concrete
function algebra, the tensor-factor order `B ⊗[ℂ] E`, and the independent
representation universe is internal. The source uses `E ⊗[ℂ] B`; this
changes only the tensor order, not the inducing action or normalization.
The module does not state a general theorem for every coefficient algebra,
the Jacquet-family assertion VI.8.3, generic irreducibility VI.8.5, or
uniform compression VI.9.1–2.

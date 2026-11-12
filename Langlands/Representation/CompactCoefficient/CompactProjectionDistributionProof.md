# The compact-representation Hecke projectors: proof of Renard IV.1.5

Author: Worker 142. Module
`Langlands.Representation.CompactCoefficient.CompactProjectionDistributionProof`,
namespace `Langlands.Renard.CompactRepresentation`.

The theorem `compactProjectionDistribution.{u,v}` has exactly the type
`CompactProjectionDistributionStatement.{u,v}`. It proves existence and
uniqueness of the actual Hecke elements `e_{K,τ}`, the three refinement
identities (and hence idempotence), and their compatibility with conjugation.
The group and representation universes remain independent, and the theorem
adds no hypothesis. The published statement and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, IV.1.5, Theorem and proof, printed p.92 /
PDF p.98. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Implemented proof

This module composes three published results. First,
`Hecke.heckeNondegenerateModuleEquivalence.{u,u}` proves the actual
smooth-representation/nondegenerate-Hecke-module equivalence of III.1.4.
Apply `Smooth.heckeCompleteness_of_equivalence.{u,v}` to this proof to obtain
the full III.1.11 completeness proposition for irreducible smooth
representations carried in the independently prescribed universe `v`.
The reduction constructs a separating simple Hecke module from a nonzero
Hecke function, recovers its smooth representation through the equivalence,
and realizes that irreducible in universe `v` using its countable spanning
orbit. Specializing the equivalence to carrier universe `u` therefore imposes
no relation between `u` and `v`.

Apply `compactProjectionDistribution_of_heckeCompleteness.{u,v}` to this
completeness proof. Its
[construction](CompactProjectionDistributionConstruction.md) projects the
normalized indicator `e_K` onto the compact-isotypic part of the smooth left
regular test-function representation. Naturality of the intrinsic projector
computes the prescribed actions on `τ` and on inequivalent irreducibles.
Its [reduction](CompactProjectionDistributionReduction.md) uses completeness
to compare Hecke elements by their irreducible actions, giving uniqueness and
the three refinement identities. Setting the two subgroups and projectors
equal gives idempotence. The reduction's conjugation calculation uses the
stated left and right Haar invariance to identify the conjugate function and
its normalized indicator, giving exactly the final clause of the target.

The final proof is thus unconditional. It uses the Library's intrinsic
compact-isotypic splitting for existence, rather than Renard's formal-degree
formula. The completeness construction and reduction are due to Worker 138;
the III.1.4 equivalence proof is due to Worker 155. All three inputs are
imported by their Lean names; no additional mathematical premise is retained.

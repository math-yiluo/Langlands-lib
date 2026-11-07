# Uniform detection of all induced unramified twists

This module states the uniform compact-open detection assertion used in the
proof of Renard's VI.8.4 Proposition. It contains the closed proposition
`Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement.{u,v}`.
It contains no proof.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.8.4 Proposition proof,
printed pp. 192–193, PDF pp. 198–199, especially the first paragraph of
printed p. 193. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The formulation extracts an assertion from that proof as a separate proof
target. It does not replace either VI.8.4 or VI.8.5.

For a connected reductive group over any nonarchimedean local field `k`,
an actual rational parabolic `P = MU`, and an irreducible smooth complex
representation `ρ` of the rational points of `M`, there exists a single
compact open subgroup `K` of the rational points of `G` such that every
irreducible subquotient of every normalized induced representation
`i_P^G(ρ ⊗ ψ)`, for `ψ` in the full unramified character group of `M`,
has a nonzero `K`-fixed vector. The choice of `K` precedes both `ψ` and
the irreducible subquotient `D`.

The field, group-scheme, rational-point topology, parabolic, Levi, radical,
and irreducibility hypotheses are exactly those of the published
`InducedIrreducibilityOpenStatement`. They include independent field and
input-carrier universes `u` and `v`, all residue characteristics, every
rational parabolic including `P = G`, and the canonical Levi topology.
There is no admissibility, finite-length, supercuspidality, splitness,
characteristic, or countability hypothesis. The topology, local
compactness and nonarchimedean-group instances on the Levi points are the
same derived instances as in that statement.

The unramified character group is the published
`Plancherel.unramifiedCharacters` for the rational-character norm maps on
`M`. Twisting is the actual `SmoothRep.twist`; induction is the actual
`leviInductionFunctor`. The induced carrier universe is `max u v`.
`D` ranges over smooth representations in this same carrier universe, so
it includes the actual invariant-subspace quotients of each induced
representation. `SmoothRep.IsSubquotient` is the published relation
given by an invariant subrepresentation and a quotient up to isomorphism.
The conclusion uses the actual fixed submodule
`fixedVectors D.representation K.toSubgroup`.

Renard proves a stronger assertion in the cited paragraph: one compact
open subgroup detects all irreducible representations in the common
inertial support of the induced twists. He uses the proof of VI.7.2,
the finitely many Levi inertial classes above that support, a sufficiently
small subgroup with an Iwahori decomposition, invariance of its
Levi-fixed spaces under unramified twists, and the Jacquet lemma VI.6.1.
The proposition here records only the consequence needed for the full
induced family. Those structural results are proof obligations, not
premises of this statement.

The published fixed-vector detection consequences and the actual
compact-compression matrix comparison can consume this assertion after
it has been proved. They do not supply the existence or uniformity of
`K`. A proof of the closed VI.8.4 target must discharge this assertion
with a published proof or prove the corresponding fact directly; it may
not add it as a hypothesis.

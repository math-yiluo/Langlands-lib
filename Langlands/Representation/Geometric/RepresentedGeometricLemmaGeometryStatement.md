# Geometric prerequisites of the represented geometric lemma

This module states the geometric existence result needed before the
representation-theoretic filtration in Renard VI.5.1. Its namespace is
`Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
2026 version: V.4.5, printed pp.119–120 / PDF pp.125–126, for finiteness of
parabolic double cosets; V.4.6–V.4.7, printed pp.120–122 / PDF pp.126–128,
for representatives with the two parabolic intersection decompositions; and
VI.5.1, printed pp.161–162 / PDF pp.167–168, for their use in the geometric
lemma. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`.

`RepresentedGeometricLemmaGeometryStatement` retains exactly the field,
ambient group, topology and represented-parabolic hypotheses of the published
`RepresentedGeometricLemmaStatement`. It concludes the existence of a natural
number `m`, an equivalence from `Fin m` to the actual double-coset quotient
`P(F) \ G(F) / Q(F)`, representatives `z i` of those classes, and a family
of `GeometricLemmaIntersectionDatum` at these same representatives. It makes
no assertion about a representation, functor or filtration. There is just one
universe parameter `u`, since the conclusion has no representation carrier.
The ambient locally compact and nonarchimedean group instances remain the
same binders as in the full statement.

The intersection datum is imported unchanged from
`RepresentedGeometricLemmaStatement`. In particular, this target retains all
six scheme-level subgroup-functor identities, both represented parabolic
triples with their Levi, geometric radical and multiplication-isomorphism
properties, the conjugation isomorphism `L' ≅ M'`, its actual rational-point
homeomorphism, and a maximal split torus of `G` factoring through `M'`.
No datum, representative, minimal parabolic or standardness proof is supplied
as a hypothesis of this closed statement.

The maximal split torus is a derived strengthening explained in the imported
statement's Markdown. For Renard's representatives `z = g⁻¹ w h`, the
standard Levi groups `M₁` and `L₁` contain the fixed maximal split torus
`A_∅`, and `w` normalizes it. Thus `M ∩ zLz⁻¹` contains `g⁻¹ A_∅ g`.
The assertion includes this conclusion, rather than adding it as a premise.
The canonical topologies and the rational-point homeomorphism are the
Library's represented-group formulation of the algebraic conjugation.

`exists_enumerated_geometricLemmaIntersectionDatum` is an internal assembly
lemma. It takes finiteness of the actual double-coset quotient and, for each
class, existence of a representative together with its intersection datum.
It equips the finite quotient with a `Fintype`, inverts
`Fintype.equivFin` to enumerate it, chooses a suitable representative in each
enumerated class, and chooses the corresponding intersection data. Choosing
these jointly keeps each datum indexed by its chosen representative. This
lemma does not prove either geometric input and does not use the full
geometric lemma.

`representedGeometricLemmaGeometry_of_geometricLemma` records that the
geometric target is a consequence of the full published statement: it
specializes the representation carrier universe to `u` and discards only
the filtration witness. This logical implication is not a proof of the
geometric existence result. It identifies the prerequisite's precise
relationship to the consumer.

This is a focused prerequisite statement and an elementary assembly proof.
It does not prove V.4.5, V.4.7, or VI.5.1. The full geometric lemma still
requires a proof of this geometric target and a natural normalized
Jacquet–induction filtration. Its published statement and imported closure
are unchanged.

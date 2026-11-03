# An ambient maximal torus in every Borel subgroup: statement

Worker 1336.

`BorelMaximalTorusStatement.{u}` says that every actual Borel subgroup
`i : B ⟶ G` of a smooth affine group scheme with connected underlying
space over an algebraically closed field `k : Type u` is part of a Borel
pair. Its witnesses are a commutative group scheme `T` over `k` and a
homomorphism `j : T.toGrp ⟶ G` satisfying the published
`IsBorelPair i j`.

Unfolding `IsBorelPair`, the conclusion includes `IsMaximalTorus j`
and an actual factorization `f : T.toGrp ⟶ B` with `f ≫ i = j`.
Maximality is in `G` and is tested against all closed tori. There is no
reductivity or characteristic assumption, and no requirement that the
torus be given in advance. Smoothness and affineness make `G` a group
variety of finite type; the statement retains arbitrary universe `u`.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, the paragraph after Definition 17.12,
printed p.355 (one-based PDF p.371, zero-based page 370). That paragraph
first puts a maximal torus in a Borel subgroup and then uses conjugacy
of Borel subgroups to show that every Borel subgroup belongs to a Borel
pair. The surrounding section treats connected group varieties over an
algebraically closed field. The source's subgroup inclusions are
expressed here by homomorphisms and their composition equation. The
registered author errata snapshot of 2026-11-02 has no correction to
this passage.

This module defines the proposition and gives no proof. In particular,
`IsBorelPair` is a conjunction specifying the desired data, not an
existence theorem. The statement alone does not prove that a maximal
torus of a parabolic is maximal in the ambient group or establish
`ParabolicMaximalTorusStatement`.

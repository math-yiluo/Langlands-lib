# Rigidity of polarized automorphisms implies the Zariski sheaf property

`Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafOfRigidityStatement` is a
proposition definition. It is a statement only; this module proves nothing.

## The statement

For every `P : Prerequisites.{0}`, all natural numbers `g d n`, and proofs `hd : 0 < d`
and `hn : 3 ≤ n`, the following implication holds.

- Hypothesis (rigidity at level `n`): for every level base `S : LevelBase n`, every
  datum `a : Datum P S.obj g d n` and every polarized isomorphism
  `α : PolarizedIso a a`, `α = PolarizedIso.refl a`.
- Conclusion: the published moduli functor `moduliFunctor P g d n hd hn` satisfies
  `LevelBase.IsZariskiSheaf` (the sheaf condition for open covers of level bases, from
  `LevelBaseZariski`).

Concretely, under the rigidity hypothesis: given a level base `S`, an open cover
`(U_i)` of `S` and isomorphism classes of data over the `U_i` that agree on the overlaps
`U_i ∩ U_j`, exactly one class over `S` restricts to each of them.

Only the hypothesis at the fixed level `n` and fixed `P, g, d` is assumed; nothing about
other levels.

## Why this is the gluing half

Classes are data up to polarized isomorphism. Under rigidity, any two polarized
isomorphisms between the same two data are equal (compose one with the inverse of the
other). Hence local isomorphisms between restrictions are unique; they agree on overlaps
and satisfy the cocycle condition automatically. Uniqueness of the glued class is the
gluing of these isomorphisms. Existence is the gluing of the data themselves: the
abelian schemes along the unique transition isomorphisms, then the dual witness,
polarization, degree and level sections. This statement isolates that gluing from the
rigidity, which `GeometricPointRigidity` proves at large level from Lefschetz's theorem.

## Relation to other statements

Together with `PolarizedIso.eq_refl_of_cubicFieldEmbedding` it gives
`EventualModuliZariskiSheafStatement`; see `eventualModuliZariskiSheaf_of_rigidity` in
`EventualModuliZariskiSheafReduction`. With rigidity at every level `n ≥ 3` (Serre's
lemma, which the Library lacks) it would give `ModuliZariskiSheafStatement`; that is
not recorded here.

## Provenance

Internal. Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition
(1994), obtain the fine moduli scheme at large level directly as a quotient
(Theorem 7.9, printed p.139, PDF p.152, from Theorem 3.8, Propositions 7.1, 7.4, 7.6 and
Corollary 7.8); the sheaf property of the represented functor is then automatic. The
Library separates the sheaf property from representability, and this statement isolates
its gluing step: a functor of isomorphism classes of objects without nontrivial
automorphisms, which glue along open covers, is a Zariski sheaf. That is the standard
gluing argument (schemes and morphisms glue along open covers once the transition
isomorphisms satisfy the cocycle condition), stated here in the Library's vocabulary.

# Admissible original nonunital modules

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, I.5.1, the unnumbered definition on printed
page 26 / PDF page 32. Its registered identifier is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read, including the subsequent proposition and corollary.
The first two pages of the registered 2010 corrections were also read: the
correction to the reflexivity argument on that edition's printed page 29
appears in the 2026 text and does not change this definition. Those corrections
are registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`;
the relevant correction is on PDF page 2.

Let `A` be a possibly nonunital complex algebra with local idempotents, and let
`M` be an original nondegenerate left `A`-module. The ring hypotheses are
`NonUnitalRing A`, `Module ℂ A`, `IsScalarTower ℂ A A`, and
`SMulCommClass ℂ A A`. The original module has only its additive group and
`NonUnitalModule A M` action as supplied structures. Idempotentedness and
nondegeneracy are the explicit witnesses `hA` and `hM`. The universes of `A`
and `M` are independent.

`Langlands.Algebra.NonUnitalModuleAdmissible.IsAdmissible hA hM` means that for
every `e : Idempotent A`, the actual subgroup
`NonUnitalModuleCorner.FixedPart e M` is finite-dimensional over the complex
numbers. This subgroup consists of the elements `m` with `e • m = m`; by
idempotence it is exactly the source's image `e · M`. Its scalar structure is
exactly `NonUnitalModuleCorner.complexModule hA hM e`, inherited from the
canonical ambient scalar recovery. There is no separately supplied complex
module on `M` or on its fixed spaces.

The predicate uses Mathlib's `FiniteDimensional` with that exact scalar
instance. It quantifies over all idempotents of the original ring, allows the
zero module, and assumes no finite dimension for the whole module.
`isAdmissible_iff` is the definitional unfolding of this predicate, proved by
reflexivity. The complete unapplied type example checks the independent
universes and the absence of an extra ambient coefficient structure.

This unit supplies the admissibility definition and its intrinsic unfolding.
The canonical bidual reflexivity proposition and the corollary about admissible
duals and simplicity require separate statement and proof units.

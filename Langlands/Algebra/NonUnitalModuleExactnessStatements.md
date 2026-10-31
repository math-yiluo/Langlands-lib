# Exactness in the original category of nonunital modules

Workers 6 and 691. Worker 6 prepared the shared statement draft; Worker 691
independently checked the cited original passages, scope and complete Lean
interface. This file states one internal derived correspondence in the
published category `Langlands.Algebra.NonUnitalModuleCat`. It supplies
neither a proof of that correspondence nor a new exactness predicate.

## Statement and exact objects

`Langlands.Algebra.NonUnitalModuleExactnessStatement.{uA,uM}` is a closed
proposition. It quantifies over every `A : Type uA` with its given
`NonUnitalRing A` structure and every actual short complex
`S : CategoryTheory.ShortComplex (NonUnitalModuleCat.{uA,uM} A)`.
Its assertion is precisely

```lean
S.Exact ↔ S.f.rangeSubmodule = S.g.kernelSubmodule
```

Here `S.f : S.X₁ ⟶ S.X₂` and `S.g : S.X₂ ⟶ S.X₃` are the original
additive intertwiners, and the short complex already contains their
vanishing composite. The left side is Mathlib's existing categorical
`CategoryTheory.ShortComplex.Exact`, which asserts the existence of
homology data with zero homology object.

Both sides of the equality on the right belong to the published
`NonUnitalSubmodule A S.X₂`. The existing
`NonUnitalModuleHom.mem_rangeSubmodule` identifies membership in the
first with the existence of an original preimage under `S.f`.
The existing `mem_kernelSubmodule` identifies membership in the second
with being sent to zero by `S.g`. The equation therefore asserts equality
of the actual stable additive subgroups in the given middle object.
It does not substitute an abstract image carrier or a replacement action.

The target imports the published concrete kernel/cokernel construction
and ambient abelianness proof by Lean names. Their universal properties
and ambient structure are established dependencies; they are not
additional hypotheses of this proposition.

## Scope and size

The only quantified data are `A`, its original nonunital-ring structure
and `S`. In particular, there is no premise supplying categorical
exactness, a homology witness, a range/kernel equality, or abelianness.
The acting-ring universe `uA` and carrier universe `uM` are independent.
Every short-complex object has carrier in `Type uM`.
The module includes the complete unfolded proposition interface and
both unequal specializations `(0,1)` and `(1,0)`.

The original ring may be noncommutative and nonunital. Zero rings,
zero carriers and degenerate original actions, including zero actions
over unital rings, are allowed. There is no unit-action law,
idempotentedness, nondegeneracy, scalar-field or finiteness restriction.
The automatic integer-compatible interpretation used inside the
existing stable-subgroup constructions retains the given original
additive maps and actions.

## Provenance and remaining obligations

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original conventions at printed pp.5–6/PDF11–12 allow nonunital rings
and original actions without a unit law, even over unital rings.
I.1.2 at printed p.7/PDF13 separately identifies the nondegenerate full
subcategory. The exact-sequence paragraph in A.VI.2 at printed
p.262/PDF268 introduces exact sequences after the kernel/image discussion.
Both authors read these original passages for this statement. Worker 691 also
visually inspected PDF268 to confirm the exact-sequence paragraph. The
supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–3 and PDF18–19. It concerns the 2010 edition and does not
supply the present derived equivalence. The 2026 original remains the
governing source; no project errata file is present for either source.
The Library source-discrepancy note
`notes/renard/appendix-a-corrections.md` was also read; its defective
full-subcategory closure criterion is not used here.

Renard does not print this precise equivalence as a named theorem.
It is an internal derived correspondence between the actual categorical
notion used for Appendix A and the already published original-module
stable subgroups. The defining expression for `ShortComplex.Exact` was
checked in the pinned Mathlib source
`Algebra/Homology/ShortComplex/Exact.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`.
No proof of the equivalence is claimed by this statement publication.

Concrete image/coimage constructions and their comparisons, the
nondegenerate subcategory's finite-product closure and abelianness,
exactness of its inclusion and nondegenerate-part functor, and scalar
Hom/category comparisons remain separate obligations of the whole-book
program.

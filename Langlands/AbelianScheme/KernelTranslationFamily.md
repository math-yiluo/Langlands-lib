# Translation of relative families by kernel points

This module derives actual scheme maps from the published shear maps and
scheme-theoretic kernels. For a homomorphism `f : A ⟶ B` of abelian schemes,
`a : U ⟶ T` over the base, and an actual point `k : U ⟶ ker(f)`,
`kernelShear f a k` sends `(u,x)` in `U ×_S A` to
`(a(u), k(u) + x)` in `T ×_S A`, with the kernel point read through its actual
inclusion in `A`. The multiplicative notation in Lean is the existing group
law on scheme-valued points.

`kernelShear_homFamilySpaceMap` proves that this map and the ordinary map
`U ×_S A → T ×_S A` have identical composites to `T ×_S B`. Consequently,
pullback-composition isomorphisms can canonically compare the two pullbacks
of an actual module on `T ×_S B`.

The module proves the parameter projection formula, the unit action, naturality
under a further parameter map, and the composition formula
`(a,k)` followed by `(b,l)` equals `(b ∘ a, (l ∘ a) k)`.
It also proves the more general composition and homomorphism compatibility
for shears. These proofs use the two projections of the actual scheme fibre
products and the existing group law on morphisms in `Over S`.

The provenance is internal and derived: the inputs are the current Library's
`PoincareSquare`, `HomFamilyPullback`, and actual `GroupScheme.kernel`.
This is the geometric part of the canonical kernel action used in the
construction motivated by Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
Chapter VII, §§7.1–7.4. The module does not yet define a module action, a scalar
or a character, and makes no descent or duality assertion.

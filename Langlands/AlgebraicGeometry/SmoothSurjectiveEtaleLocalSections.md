# Etale local sections of smooth surjective scheme morphisms: proof

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSections`.
It imports the statement module
`Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSectionsStatement`
(Worker 59) and the Library module
`Langlands.AlgebraicGeometry.SmoothEtaleLocalSections` (Worker 766).

`smoothSurjectiveEtaleLocalSections : SmoothSurjectiveEtaleLocalSectionsStatement.{u}`
proves the statement at every universe `u`: for arbitrary schemes
`W T : Scheme.{u}` and a smooth surjective `f : W ⟶ T` there are
`V : Scheme.{u}`, an etale surjective `e : V ⟶ T` and `s : V ⟶ W` with
`s ≫ f = e`. The proof applies `hasEtaleLocalSections_of_smooth f`, whose
conclusion `HasEtaleLocalSections f` is literally this existential. That
theorem chooses, through each point of `T`, an affine etale neighborhood
mapping to `W` over `T`, and takes their disjoint union over the points of
`T`. The neighborhoods come from Mathlib's local structure theorem for smooth
algebras (standard etale over a polynomial ring) and an algebraic argument with
separable points explained in the Markdown of
`Langlands.CommutativeAlgebra.EtaleLocalSections`. The route differs from both
proofs of The Stacks Project, Tag 055U
(`stacks-055U-smooth-etale-local-sections-2026-11-02`), which is the source
of the statement only.

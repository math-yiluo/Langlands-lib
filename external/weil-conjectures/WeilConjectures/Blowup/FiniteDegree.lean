/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.Algebra
public import WeilConjectures.Blowup.FiniteDegree.ChartIdeal
public import WeilConjectures.Blowup.FiniteDegree.ChartProbe
public import WeilConjectures.Blowup.FiniteDegree.Generation
public import WeilConjectures.Blowup.FiniteDegree.LocalAlgebra
public import WeilConjectures.Blowup.FiniteDegree.Main
public import WeilConjectures.Blowup.FiniteDegree.UniformNumerator
public import WeilConjectures.Blowup.Proper
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!

# Finite-degree approximation on the blow-up (Stacks Project Tag 0803)

This module only re-exports its parts, which live in `WeilConjectures.Blowup.FiniteDegree`; it
was split to keep the compilation of each part cheap.

This module proves the finite-degree approximation of a finite-type center on a blow-up:
for finite-type centers `I` on a qcqs scheme `X` and `J` on the blow-up of `I`, there
are `d ≥ 1` and a finite-type `L ≤ I^d` whose inverse image ideal on the blow-up is
`I_E^d · J` (`Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup`, Stacks
Project Tag 0803; blueprint: `blueprint/finite_degree_approximation_blowup.tex`,
`lemma:nagata-proj-closed-center-finite-degree-exists`).

The proof is organized around the maximal degree-`d` candidate
`I^d ⊓ π₎(I_E^d·J)`: over an affine open `V` of the base, the blow-up is covered by
the charts at the degree-one Rees elements of a finite generating set of `I(V)`, and
each finite chart-ideal generator `μ = g/aᵉ` of `J` is cleared into a numerator
`m = aᴺ·g ∈ I(V)^d` with `m/aᵈ = μ` whose fractions `m/bᵈ` lie in the chart ideals of
every chart of the same Rees algebra (`AffineBlowup.exists_uniform_numerator`, the
denominator-clearing core). A finite-type subsheaf through the finitely many
numerators is then extracted with the Tag 01PF machinery
(`Scheme.IdealSheafData.exists_finiteType_le_ideal_eq`), and generates `I_E^d · J`
chart by chart (`Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators`).

Elaboration-performance conventions: the chart rings of the blow-up are large
`HomogeneousLocalization` types, so all `Finset` bookkeeping over generating sets is
done by the abstract combinators `exists_uniform_ge₂`/`exists_finset_forall_mem` over
variable types, chart probes keep their ring abstract
(`Scheme.IdealSheafData.ideal_comap_comap_of_probe`), and memberships are transported
along morphism equalities by `mem_of_ringHom_eq` instead of `▸`-rewrites.

-/

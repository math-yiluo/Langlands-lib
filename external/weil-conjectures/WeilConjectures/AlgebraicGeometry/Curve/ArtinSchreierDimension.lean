/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.ArtinSchreierSequence
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Artin–Schreier vanishing on a smooth connected curve

Source: blueprint, `sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-artin-schreier-dimension`;
Stacks Project, Tag 0A3N, dimension one (blueprint: proposition-p-torsion-smooth-proper-curve--3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: blueprint
`sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-artin-schreier-dimension`; Stacks Project, Tag
0A3N (blueprint: proposition-p-torsion-smooth-proper-curve--3). For a smooth separated connected
curve over an algebraically closed field of positive characteristic `p`, the constant étale sheaf
`ℤ/p` has zero cohomology in degrees above one.

Proof: The Artin–Schreier short exact sequence `0 → ℤ/p → G_a → G_a → 0`
(lemma-p-torsion-affine-curve-characteristic--3) gives the long exact sequence for derived global
sections, by proposition-p-torsion-smooth-proper-curve--3,
proposition-p-torsion-smooth-proper-curve--3, proposition-p-torsion-smooth-proper-curve--3 and
proposition-p-torsion-smooth-proper-curve--3. By proposition-p-torsion-smooth-proper-curve--3, the
cohomology of `G_a` vanishes in degrees at least two. Thus degrees at least three vanish, and degree
two is the cokernel of `F - 1` on `H¹(C, G_a)`. Compactification (lemma-proper-smooth-model--1) and
proposition-p-torsion-smooth-proper-curve--3 show that the curve is either proper or affine. In the
affine case, lemma-p-torsion-affine-curve-characteristic--4 makes `H¹(C, G_a)` zero, so its cokernel
is zero. In the proper case, multiplication by field elements on `G_a` induces a vector-space
structure on `H¹(C, G_a)`, since cohomology is additive. Frobenius induces a `p`-linear
endomorphism, and the Artin–Schreier map induces this endomorphism minus the identity.
The structure sheaf is coherent, and proposition-p-torsion-smooth-proper-curve--3 and
proposition-p-torsion-smooth-proper-curve--3 give finite-dimensional Zariski `H¹(C, O_C)`. The
comparison of proposition-p-torsion-smooth-proper-curve--3 is natural in multiplication by scalars,
so identifies it linearly with `H¹(C, G_a)`. Finally proposition-p-torsion-smooth-proper-curve--3
makes `F - 1` surjective, so the degree-two cokernel vanishes as well. -/
theorem isZero_etaleCohomology_constantZMod_of_one_lt_of_charP
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        (C.constantZMod p))) := by
  obtain ⟨G, e, a, wp, iota, hzero, ha, hwp, _, hS⟩ :=
    artinSchreier_shortExact f p (Nat.Prime.pos (Fact.out : p.Prime))
  let R := (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor
  let T := R.mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang _ :=
    R.map_distinguished _ hS.singleTriangle_distinguished
  have hstep : ((q - 1 : ℕ) : ℤ) + 1 = (q : ℤ) := by omega
  have hepi : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1}
      ((q - 1 : ℕ) : ℤ)).map T.mor₂) := by
    by_cases hq2 : q = 2
    · subst q
      exact epi_etaleCohomology_artinSchreier_one f p G a wp ha hwp
    · have hG := isZero_etaleCohomology_additive_of_two_le f G e (q - 1) (by omega)
      exact hG.epi _
  have hδ := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
    T hT ((q - 1 : ℕ) : ℤ) (q : ℤ) hstep).mp hepi
  have hG := isZero_etaleCohomology_additive_of_two_le f G e q (by omega)
  exact (DerivedCategory.HomologySequence.exact₁
    T hT ((q - 1 : ℕ) : ℤ) (q : ℤ) hstep).isZero_of_both_zeros
      hδ (hG.eq_zero_of_tgt _)

end AlgebraicGeometry

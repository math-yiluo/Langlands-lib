/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension

/-!
# Etale cohomological dimension of a smooth connected curve

Source: blueprint sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-cohomological-dimension.md;
Stacks Project, Tag 03SC (1) (blueprint: theorem-cohomology-curves--1).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a smooth separated connected curve over an algebraically closed field, every torsion
abelian etale sheaf has zero cohomology above degree two. Cohomology is the homology of derived
global sections, applied to the sheaf in degree zero.
Source: blueprint sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-cohomological-dimension.md,
and Stacks Project, Tag 03SC (1) (blueprint: theorem-cohomology-curves--1).

Proof (the nine steps of the node):
1. Choose an affine open U with finite complement of closed points using
   lem-sc-affine-open-finite-complement. Their residue fields are the base field by
   lem-weil-pbc-closed-point-residue-field-base, hence separably closed. The inclusion j is
   affine by lem-weil-pbc-separated-affine-open-intersection, and U is an affine curve by
   lem-sc-etale-affine-over-curve.
2. First suppose n kills F, with n positive. The unit F -> j_*j^{-1}F is an isomorphism over U
   by lem-sc-open-immersion-pushforward-fully-faithful. Thus
   lem-sc-iso-off-finite-set-cohomology identifies their cohomology in degrees at least two.
3. For G = j^{-1}F, apply lem-sc-torsion-acyclic-envelope twice, obtaining exact sequences
   0 -> G -> J -> G' -> 0 and 0 -> G' -> J' -> G'' -> 0. Both envelopes and both quotients
   are killed by n; J and J' are acyclic on U, after j_*, and after etale inverse image.
4. The long exact sequence and lem-sc-affine-curve-h2-vanishing give H^1(U,G'') = 0.
   Injectivity of the edge map (lem-sc-edge-map-h1-injective) gives H^1(C,j_*G'') = 0.
5. The sequence 0 -> j_*G' -> j_*J' -> j_*G'' -> 0 is exact: left exactness gives the first
   two terms. On affine etale pieces V over C, V times_C U is an affine curve. Exact inverse
   image, the first envelope and affine H^2 vanishing give H^1(V times_C U,G') = 0.
   Then lem-sc-lift-sections-h1-vanishing lifts sections locally, giving epimorphy by
   lem-weil-pbc-abelian-sheaf-epi-locally-surjective.
6. The long exact sequence of step 5 gives H^2(C,j_*G') = 0, using step 4 and acyclicity
   of j_*J'.
7. Set N = coker(j_*G -> j_*J); it embeds into j_*G'. Its cokernel R restricts to zero
   on U, since inverse image is exact and j^{-1}j_* is the identity. Therefore
   lem-sc-finite-support-acyclic makes R acyclic. The sequences
   0 -> N -> j_*G' -> R -> 0 and 0 -> j_*G -> j_*J -> N -> 0 give H^2(C,N) = 0 and
   H^3(C,j_*G) = 0. Step 2 gives H^3(C,F) = 0.
8. Apply lem-sc-torsion-acyclic-envelope on C and dimension shift in the long exact
   sequence, inductively obtaining vanishing in every degree at least three for n-killed F.
9. By lemma-weil-pbc-torsion-filtered-union, an arbitrary torsion F is the filtered union
   of its integer-torsion subsheaves. The curve is quasi-compact and quasi-separated, so
   lemma-finiteness-small-etale-topoi--2 identifies its cohomology with the colimit of
   the zero groups from step 8. This proves vanishing for all q > 2. -/
theorem IsConnectedCurve.subsingleton_etaleCohomology_of_two_lt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] [IsConnectedCurve (C ↘ Spec (.of k))]
    [Smooth (C ↘ Spec (.of k))]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) := by
  let f : C ⟶ Spec (.of k) := C ↘ Spec (.of k)
  have hq' : 3 ≤ q := by omega
  have h := IsCurve.subsingleton_sheafH_of_three_le_of_forall f
    (fun _ f' _ _ F' hF' ↦ IsCurve.subsingleton_sheafH_two_of_isAffine f' F' hF')
    F hF q hq'
  have : Subsingleton ((Sheaf.functorH C.smallEtaleTopology q).obj F) := h
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C q
  exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.Compactification.Defs

/-! # The projective line is a genus-zero smooth proper connected curve

Source: Stacks Project, varieties.tex, Tag 0B2P, lemma-projective-space-smooth;
curves.tex, Tag 0C6U, proposition-projective-line, (1) implies (2) and (7)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The base-change projective line is a smooth proper connected curve, has genus zero,
and has vanishing first cohomology of its structure sheaf.
Source: Stacks Project, Tag 0B2P, lemma-projective-space-smooth, and Tag 0C6U,
proposition-projective-line, (1) implies (2) and (7)
(auxiliary; not a blueprint node).

Proof plan:
1. Identify the two degree-zero localization charts of the integral Proj with Z[t]
   and Z[s] by homogeneous monomial fractions (definition-admissible-blow-up--1). Base change
   gives k[t] and k[s] (lem-weil-pbc-fibre-product-affine-spectra), with overlap
   s = t inverse. They give the standard projective-line model (def-sc-p1-standard).
2. Each chart is affine one-space. Apply sbc-lem-affine-space-smooth and the
   affine-local criterion of def-sbc-smooth-morphisms to obtain smoothness of
   relative dimension one.
3. Both polynomial charts are irreducible because their coordinate rings are domains.
   Their overlap contains t = 1, so their union is nonempty and connected.
   lem-sbc-smooth-fixed-dimension-over-field gives dimension one.
4. lemma-nagata-projective-space-base-change-proper gives properness, including
   separatedness and finite type (def-weil-proper-morphism). Together with steps
   2 and 3 this gives the connected-curve clauses of def-sc-curves.
5. Apply theorem-riemann-roch-coherent-serre-duality(ii) at twist zero. The two local generators of
O(0)
   have identity transition, identifying it with the structure sheaf. Transport
   vanishing of H1 to module cohomology. By prose-C-05 (equivalently Serre
   duality for the recorded differential-form genus), its genus is zero. -/
theorem isConnectedCurve_smooth_proper_genus_zero (k : Type u) [Field k] [IsAlgClosed k] :
    IsConnectedCurve (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    Smooth (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    IsProper (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)).genus = 0 ∧
    Subsingleton ((RingedSpace.moduleCohomology
      (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k))).toRingedSpace 1).obj
      (Scheme.Modules.unit (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k))))) := by
  have hs : SmoothOfRelativeDimension 1
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  have hdim : topologicalKrullDim (ProjectiveLine (Spec (.of k))) = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) 1
  have hc : IsConnectedCurve (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    { krullDim_le_one := hdim.le
      connectedSpace := inferInstance
      krullDim_eq_one := hdim }
  refine ⟨hc, SmoothOfRelativeDimension.smooth 1 _, inferInstance, ?_, ?_⟩
  · obtain ⟨e⟩ := ProjectiveLine.nonempty_relativeDifferentials_iso_twist k
    have : Subsingleton ((twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).H 0) :=
      ProjectiveLine.subsingleton_H_zero_twist_of_neg k (-2) (by decide)
    have : Subsingleton
        ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.H 0) :=
      Scheme.Modules.subsingleton_H_of_iso e.symm 0
    rw [Scheme.Hom.genus_eq_finrankH_zero, Scheme.Modules.finrankH]
    exact Module.finrank_zero_of_subsingleton
  · have : Subsingleton ((twist (ULift.{u} (Fin 2)) (Spec (.of k)) 0).H 1) :=
      ProjectiveLine.subsingleton_H_one_twist k 0 (by decide)
    have : Subsingleton ((Scheme.Modules.unit (ProjectiveLine (Spec (.of k)))).H 1) :=
      Scheme.Modules.subsingleton_H_of_iso
        (unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k))).symm 1
    obtain ⟨e, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison
      (ProjectiveLine (Spec (.of k))) 1
    exact (e _).toEquiv.subsingleton

end AlgebraicGeometry.ProjectiveSpace

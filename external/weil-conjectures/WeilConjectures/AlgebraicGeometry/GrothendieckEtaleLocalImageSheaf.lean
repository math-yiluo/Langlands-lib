/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImage
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImageDescent
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit

/-! # The categorical local image is a subsheaf
Source: Stacks Project, Tag 00WL, image subsheaves; finite affine refinements on the
small étale site, Tag 03Q4.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- The presheaf obtained by extending the local image from qcqs étale objects is a sheaf.
This statement concerns an arbitrary morphism of sheaves, with no epimorphism assumption.

Source: Stacks Project, Tag 00WL, image subsheaves, and Tag 03Q4, finite affine refinements.
Proof: test the sheaf condition on Hom(B,-) for each coefficient object B. A compatible
family maps to one in G, so it has a unique amalgamation x in G. For every map from a qcqs
étale object V to the object being covered, pull the covering sieve back and refine it to a
finite affine covering of V. On each member the restriction of x is the given local map,
so it factors through the local image. Finite-cover descent shows that x restricted to V
factors through the local image on V. These factorizations give the defining inequalities
for the qcqs local image. Thus x factors through this subobject and is the required
amalgamation. Uniqueness follows from monicity of the inclusion and uniqueness in G.
Empty objects and empty finite covering families are included by the same proof.
(auxiliary; not a blueprint node). -/
theorem qcqsLocalImage_isSheaf
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) :
    Presheaf.IsSheaf X.smallEtaleTopology (qcqsLocalImagePresheaf p) := by
  intro B W R hR s hs
  let a := Functor.whiskerRight (qcqsLocalImageι p) (coyoneda.obj (op B))
  obtain ⟨x, hx, huniq⟩ := G.property B R hR (s.map a) (hs.map a)
  have hfac' (V : X.Etale) [CompactSpace V.left] [QuasiSeparatedSpace V.left]
      (f : V ⟶ W) : (localImage p V).Factors (x ≫ G.obj.map f.op) := by
    obtain ⟨n, U, g, hg, hU, hcover⟩ :=
      (AlgebraicGeometry.Etale.exists_affine_refinement _)
        (X.smallEtaleTopology.pullback_stable f hR)
    have hcov : Sieve.ofArrows U g ∈ X.smallEtaleTopology V :=
      (Scheme.ofArrows_mem_smallEtaleTopology_iff g).2 hcover
    apply localImage_factors_of_finite_cover A p V B (x ≫ G.obj.map f.op) n U g hcov
    intro i
    have := hU i
    rw [← qcqsLocalImage_eq p (U i)]
    have hi : (x ≫ G.obj.map f.op) ≫ G.obj.map (g i).op =
        s (g i ≫ f) (hg i) ≫ (qcqsLocalImage p (U i)).arrow := by
      simpa [a, qcqsLocalImageι, Presieve.FamilyOfElements.map, Category.assoc]
        using hx (g i ≫ f) (hg i)
    rw [hi]
    exact Subobject.factors_comp_arrow _
  have hfac : (qcqsLocalImage p W).Factors x := by
    apply (Subobject.imageSubobject_le_iff _ _).1
    refine le_iInf fun V ↦ le_iInf fun hV ↦ le_iInf fun hV' ↦ le_iInf fun f ↦ ?_
    have := hV
    have := hV'
    apply (Subobject.imageSubobject_le_iff _ _).2
    exact (Subobject.factors_pullback_obj_iff _ _ _).2 (hfac' V f)
  refine ⟨(qcqsLocalImage p W).factorThru x hfac, ?_, ?_⟩
  · intro Z f hf
    apply (cancel_mono (qcqsLocalImage p Z).arrow).1
    simpa [qcqsLocalImagePresheaf, qcqsLocalImageι, a, Presieve.FamilyOfElements.map,
      Category.assoc] using hx f hf
  · intro y hy
    apply (cancel_mono (qcqsLocalImage p W).arrow).1
    rw [Subobject.factorThru_arrow]
    exact huniq _ (hy.map a)

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

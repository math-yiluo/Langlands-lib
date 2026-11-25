/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityOn
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ExactSequence

import WeilConjectures.AlgebraicGeometry.PerfectHomStageColimit
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The five-term comparison diagram for perfect Hom continuity

Source: Stacks Project, Tag 09RE, Mayer--Vietoris induction step, and Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Construct the exact comparison diagram, without asserting invertibility of its
middle map. The central source is a filtered Hom colimit; its presentation is pinned
both to stage transport and to limit transport. The four adjacent comparisons are
invertible by open-local continuity, in degrees -1 and 0.

Source: Stacks Project, Tag 09RE, proof's Mayer--Vietoris step, using Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-comparison).

Proof:
1. Pull U and V back along t. Their union is top on Y. The open immersion identifies
   these opens with U and V; compactness of U and affineness of V give compactness,
   while quasi-separatedness makes the intersection compact. Pull this cover back
   to every stage and the limit. All transition morphisms are affine. Restriction
   and derived pullback preserve perfect complexes and their shifts, by pulling
   back their bounded finite locally free models. Perfect Q has quasi-coherent
   cohomology, as do all its pullbacks.
2. At each stage and at the limit use schemeDerived_mayerVietoris_triangle for Q.
   Apply the represented homological functor Hom(P,-). Open derived adjunction
   identifies the local terms. Take the five consecutive terms
   Hom(P_U,Q_U[-1]) plus Hom(P_V,Q_V[-1]), Hom(P_UV,Q_UV[-1]),
   Hom(P,Q), Hom(P_U,Q_U) plus Hom(P_V,Q_V), Hom(P_UV,Q_UV).
   They form exact five-term rows of abelian groups.
3. For a transition h, apply schemeDerived_mayerVietoris_directImage to Lh*Q.
   Its pinned direct-image composition comparisons identify the pushed triangle
   with the triangle of Rh*Lh*Q. Naturality of the connecting map applied to the
   adjunction unit Q -> Rh*Lh*Q gives a triangle morphism. Applying Hom(P,-) and
   derived adjunction gives every commuting square, including the boundary square.
   The local vertical maps are canonical restriction transports. At the central
   term they are perfectStageMap and perfectLimitMap: compose the pinned
   adjunction units/counits, then cancel the counit-pinned composition comparisons.
4. Form H from these central stage Hom sets on the tail above i; if necessary use
   ULift to place them in Type (max u w). Its functor laws follow from the unit and
   associativity laws of derived pullback composition. Its canonical cocone gives
   the limit maps. Take the filtered abelian-group colimit of the stage rows.
   Filtered colimits preserve exactness and their underlying sets are filtered
   set colimits. This gives d, hd, a and the two exact rows. The transition and
   central equations are precisely those from step 3, not arbitrary comparisons.
5. Apply hcontU, hcontV and hcontUV to the restricted perfect pairs, including
   Q[-1]. Their representative and eventual equality clauses give bijectivity of
   the corresponding filtered comparisons. The first and fourth comparisons are
   products of two such bijections. Thus the four neighbouring components of phi
   are isomorphisms. No five lemma or global continuity is used here. Empty opens
   give zero Hom groups and zero local rows, so the construction includes them. -/
theorem perfect_hom_mayerVietoris_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hcontU : PerfectHomContinuityOn R c i X s₀ U)
    (hcontV : PerfectHomContinuityOn R c i X s₀ V)
    (hcontUV : PerfectHomContinuityOn R c i X s₀ (U ⊓ V))
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) :
    ∃ (H : Set.Ici i ⥤ Type (max u w)) (d : Cocone H),
      Nonempty (IsColimit d) ∧
      ∃ (ident : ∀ j : Set.Ici i, H.obj j ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q)),
        (∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : H.obj j),
          ident k (H.map (homOfLE hjk) f) =
            perfectStageMap R s j.property hjk (ident j f)) ∧
        ∃ (A B : ComposableArrows AddCommGrpCat.{max u w} 4) (φ : A ⟶ B)
          (a : d.pt ≃ A.obj' 2)
          (b : B.obj' 2 ≃
            ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
             (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
          A.Exact ∧ B.Exact ∧
          IsIso (ComposableArrows.app' φ 0) ∧ IsIso (ComposableArrows.app' φ 1) ∧
          IsIso (ComposableArrows.app' φ 3) ∧ IsIso (ComposableArrows.app' φ 4) ∧
          ∀ (j : Set.Ici i) (f : H.obj j),
            b ((ComposableArrows.app' φ 2) (a (d.ι.app j f))) =
              perfectLimitMap R c s j.property (ident j f) := by
  obtain ⟨H, d, ⟨hd⟩, ident, htransition⟩ := perfect_hom_stage_colimit R i Y s P Q
  obtain ⟨A, B, φ, a, b, hA, hB, h0, h1, h3, h4, hpin⟩ :=
    perfect_hom_mayerVietoris_local_rows R c i X s₀ U V hU hV
      Y t ht s hs P Q hP hQ H d hd ident htransition
  have hbij {α β : Type (max u w)} {m : α → β}
      (hm : PerfectHomLocalMap R c i X s₀ U V m) : Function.Bijective m :=
    PerfectHomLocalMap.bijective R c i X s₀ U V hm hcontU hcontV hcontUV
  refine ⟨H, d, ⟨hd⟩, ident, htransition, A, B, φ, a, b, hA, hB, ?_, ?_, ?_, ?_, hpin⟩
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h0)
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h1)
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h3)
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h4)

end AlgebraicGeometry

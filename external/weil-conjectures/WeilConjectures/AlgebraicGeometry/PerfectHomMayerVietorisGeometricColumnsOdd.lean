/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisDiagram
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
public import WeilConjectures.AlgebraicGeometry.PerfectHomTriangleRow
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStagePresentation

/-! # Local comparisons for the outer columns of geometric triangle diagrams

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-odd).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem localComparison_of_stage_presentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens) (Z : Scheme.{u}) (k : Z ⟶ X) [IsOpenImmersion k]
    (hk : k.opensRange = W) (s' : Z ⟶ Spec (R.obj i)) (hs' : s' = k ≫ s₀)
    [LocallyOfFinitePresentation s'] [QuasiCompact s'] [QuasiSeparated s']
    [∀ T : Z.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over T))]
    (P' Q' : schemeDerivedCategory Z) (hP' : Z.IsPerfect P') (hQ' : Z.IsPerfect Q')
    (K : Set.Ici i ⥤ AddCommGrpCat.{max u w}) (dK : Cocone K)
    (e : ∀ j : Set.Ici i, K.obj j ≃
      ((derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj P' ⟶
       (derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj Q'))
    (b : dK.pt ≃
      ((derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj P' ⟶
       (derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj Q'))
    (he : ∀ (j l : Set.Ici i) (hjl : j ≤ l) (f : K.obj j),
      e l (K.map (homOfLE hjl) f) = perfectStageMap R s' j.property hjl (e j f))
    (hb : ∀ (j : Set.Ici i) (f : K.obj j),
      b (dK.ι.app j f) = perfectLimitMap R c s' j.property (e j f)) :
    PerfectHomLocalComparison R c i X s₀ W (colimit.desc K dK) := by
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j l ↦ by
    obtain ⟨a, hja, hla⟩ := exists_ge_ge j.val l.val
    exact ⟨⟨a, j.property.trans hja⟩, hja, hla⟩⟩
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : CategoryTheory.IsFiltered (Set.Ici i) := inferInstance
  let G := forget AddCommGrpCat.{max u w}
  have : PreservesFilteredColimitsOfSize.{max u w, max u w} G := inferInstance
  have : PreservesFilteredColimitsOfSize.{u, u} G :=
    preservesFilteredColimitsOfSize_shrink G
  have : PreservesColimit K G := inferInstance
  let D := G.mapCocone (colimit.cocone K)
  refine ⟨Z, k, inferInstance, hk, s', hs', inferInstance, inferInstance,
    inferInstance, inferInstance, P', Q', hP', hQ', K ⋙ G, D,
    isColimitOfPreserves G (colimit.isColimit K), e, he, Equiv.refl _, b, ?_⟩
  intro j f
  change b ((colimit.desc K dK) ((colimit.ι K j) f)) = _
  rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
  exact hb j f

set_option backward.isDefEq.respectTransparency false in
/-- Outer-column recognition for the actual geometric Mayer--Vietoris construction.
The input consists of a representing cocone natural in every testing object and a
family whose outer objects and maps are explicitly open direct images and restrictions.
In particular this statement does not apply to arbitrary distinguished triangle cocones.
It asserts nothing about distinguishedness or the central Hom comparison.

Source: Stacks Project, perfect.tex Tag 09RE, Mayer--Vietoris induction;
cohomology.tex Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-odd).

Proof:
1. Quasi-separatedness of s₀ over the affine base makes X quasi-separated.
   Hence U intersection V is compact. It lies in the image U union V of t.
2. The single-open stage presentation supplies perfect local objects, natural
   stage and apex Hom equivalences, and the two canonical transport equations.
   Apply it with shift -1 for column 1 and shift 0 for column 4.
3. The definition of the Hom row identifies both columns with the intersection
   direct image. The map_hom₃ equation identifies transitions and cocone legs
   with the corresponding restriction/direct-image maps, independently of boundary
   and of the chosen restriction adjunctions. Compose the stage and apex
   equivalences with ULift.down.
4. The tail is nonempty and directed. The forgetful functor from abelian groups
   preserves its colimit, after shrinking the filtered-colimit universe. Thus the
   underlying canonical group-colimit cocone is a set-colimit cocone. Use it for H
   and d in PerfectHomLocalComparison; the source equivalence is the identity.
   The colimit inclusion/desc equation reduces its pinning equation to the apex
   equation of step 2. Apply PerfectHomLocalMap.basic on U intersection V.
5. Equality of Fin values reduces the supplied index to 1 or 4. The preceding
   construction covers both cases, including an empty intersection. -/
theorem perfect_hom_mayerVietoris_geometric_columns_odd
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (A : PerfectHomMVFamily Y (t ⁻¹ᵁ U) (t ⁻¹ᵁ V)) :
    ∀ (r : Fin 5), r.val = 1 ∨ r.val = 4 →
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj r)
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj r,
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app r⟩) := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s₀
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) :=
    hU.inter_of_isOpen hV.isCompact U.isOpen V.isOpen
  have hWt : U ⊓ V ≤ t.opensRange := by
    rw [ht]
    exact inf_le_left.trans le_sup_left
  intro r hr
  have hr' : r = 1 ∨ r = 4 := by
    rcases hr with hr | hr
    · left; exact Fin.ext hr
    · right; exact Fin.ext hr
  rcases hr' with rfl | rfl
  · obtain ⟨Z, k, hkI, hk, s', hs', hsL, hsC, hsQ, hD, P', Q', hP', hQ',
      e, b, he, hb⟩ := perfect_hom_open_stage_presentation R c i X s₀ (U ⊓ V) hW
        Y t hWt s hs P Q hP hQ F d h (-1 : ℤ)
    apply PerfectHomLocalMap.basic (U ⊓ V) (Or.inr (Or.inr rfl))
    apply localComparison_of_stage_presentation R c i X s₀ (U ⊓ V)
      Z k hk s' hs' P' Q' hP' hQ'
      ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj 1)
      ⟨_, (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
        (A.cocone F d h.stageQCoh h.limitQCoh)).app 1⟩
      (fun j ↦ Equiv.ulift.trans (e j)) (Equiv.ulift.trans b)
    · intro j l hjl f
      change e l (f.down ≫ (A.map (h.stageQCoh j) (h.stageQCoh l)
        (F.map (homOfLE hjl))).hom₃⟦(-1 : ℤ)⟧') =
          perfectStageMap R s' j.property hjl (e j f.down)
      rw [A.map_hom₃]
      simpa only [Scheme.Hom.preimage_inf, Functor.comp_map] using he j l hjl f.down
    · intro j f
      change b (f.down ≫ (A.map (h.stageQCoh j) h.limitQCoh
        (d.ι.app j)).hom₃⟦(-1 : ℤ)⟧') =
          perfectLimitMap R c s' j.property (e j f.down)
      rw [A.map_hom₃]
      simpa only [Scheme.Hom.preimage_inf, Functor.comp_map] using hb j f.down
  · obtain ⟨Z, k, hkI, hk, s', hs', hsL, hsC, hsQ, hD, P', Q', hP', hQ',
      e, b, he, hb⟩ := perfect_hom_open_stage_presentation R c i X s₀ (U ⊓ V) hW
        Y t hWt s hs P Q hP hQ F d h (0 : ℤ)
    apply PerfectHomLocalMap.basic (U ⊓ V) (Or.inr (Or.inr rfl))
    apply localComparison_of_stage_presentation R c i X s₀ (U ⊓ V)
      Z k hk s' hs' P' Q' hP' hQ'
      ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj 4)
      ⟨_, (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
        (A.cocone F d h.stageQCoh h.limitQCoh)).app 4⟩
      (fun j ↦ Equiv.ulift.trans (e j)) (Equiv.ulift.trans b)
    · intro j l hjl f
      change e l (f.down ≫ (A.map (h.stageQCoh j) (h.stageQCoh l)
        (F.map (homOfLE hjl))).hom₃⟦(0 : ℤ)⟧') =
          perfectStageMap R s' j.property hjl (e j f.down)
      rw [A.map_hom₃]
      simpa only [Scheme.Hom.preimage_inf, Functor.comp_map] using he j l hjl f.down
    · intro j f
      change b (f.down ≫ (A.map (h.stageQCoh j) h.limitQCoh
        (d.ι.app j)).hom₃⟦(0 : ℤ)⟧') =
          perfectLimitMap R c s' j.property (e j f.down)
      rw [A.map_hom₃]
      simpa only [Scheme.Hom.preimage_inf, Functor.comp_map] using hb j f.down

end AlgebraicGeometry

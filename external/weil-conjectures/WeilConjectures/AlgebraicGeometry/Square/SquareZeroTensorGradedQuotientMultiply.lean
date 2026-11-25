/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- The closed-immersion unit is locally surjective, also for the adjunction
chosen in the graded presentation. Source: Stacks Project, Tag 08KS. -/
private theorem unit_locallySurjective {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (M : X.Modules) :
    TopCat.Presheaf.IsLocallySurjective (tensorGradedUnit j M).mapPresheaf := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
    have : Epi (adj.unit.app M) := closedImmersion_unit_epi j M
    have : Epi (tensorGradedUnit j M) := by
      unfold tensorGradedUnit
      rw [← adj.unit_leftAdjointUniq_hom_app
        (Classical.choose (exists_tensorPullbackAdjunction j)) M]
      infer_instance
    exact (TopCat.Sheaf.isLocallySurjective_iff_epi
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (tensorGradedUnit j M))).mpr
        (Functor.map_epi (SheafOfModules.toSheaf X.ringCatSheaf) _)

/-- Transport the fixed pullback cotensorator formula through the unique
comparison of left adjoints. Source: Stacks Project, Tags 0096 and 01CD. -/
private theorem unit_tensor {X Z : Scheme.{u}} (j : Z ⟶ X)
    (M N : X.Modules) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
      ((tensorGradedUnit j (M ⊗ N)).app U (tmulSection s t)) =
    tmulSection (M := (tensorPullback j).obj M) (N := (tensorPullback j).obj N)
      (U := j ⁻¹ᵁ U) ((tensorGradedUnit j M).app U s) ((tensorGradedUnit j N).app U t) := by
  have he (P : X.Modules) (z : Γ(P, U)) :
      ((boundaryPullbackComparison j).app P).hom.app (j ⁻¹ᵁ U)
        ((tensorGradedUnit j P).app U z) = pullbackUnitApp j P U z := by
    exact congrArg (fun φ : P ⟶ (pushforward j).obj ((pullback j).obj P) ↦ φ.app U z)
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit_leftAdjointUniq_hom_app
        (pullbackPushforwardAdjunction j) P)
  have hei (P : X.Modules) (z : Γ(P, U)) :
      ((boundaryPullbackComparison j).app P).inv.app (j ⁻¹ᵁ U)
        (pullbackUnitApp j P U z) = (tensorGradedUnit j P).app U z := by
    rw [← he P z]
    exact inv_app_hom_app_apply_of_iso _ _
  change (((boundaryPullbackComparison j).app M).inv ⊗ₘ
    ((boundaryPullbackComparison j).app N).inv).app (j ⁻¹ᵁ U)
      ((Functor.OplaxMonoidal.δ (pullback j) M N).app (j ⁻¹ᵁ U)
        (((boundaryPullbackComparison j).app (M ⊗ N)).hom.app (j ⁻¹ᵁ U)
          ((tensorGradedUnit j (M ⊗ N)).app U (tmulSection s t)))) = _
  rw [he, pullback_δ_app_unit_tmulSection, tensorHom_app_tmulSection, hei, hei]

/-- The underlying module map and algebra map agree on sections.
Source: Stacks Project, Tag 09MS, the quotient algebra morphism. -/
private theorem algebraMap_section {X : Scheme.{u}} {B C : X.CommAlgebraSheaf}
    (p : B ⟶ C) (U : X.Opens) (z : Γ(commAlgebraSheafModule X.sheaf B, U)) :
    tensorGradedAlgebraSection C U (Hom.app (X := X) (tensorGradedAlgebraMap p) U z) =
      p.right.hom.app (op U) (tensorGradedAlgebraSection B U z) := rfl

/-- Multiplication compatibility for sections in the image of the unit.
Source: Stacks Project, Tag 09MS, the graded direct-sum quotient. -/
private theorem multiply_lifts {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (T : TensorGradedPresentation j L)
    (a d : ℕ) (U : X.Opens) (s : Γ(L.tensorPow a, U)) (t : Γ(L.tensorPow d, U)) :
    tensorGradedAlgebraSection T.C U
        ((T.c a).app U ((tensorGradedUnit j (L.tensorPow a)).app U s)) *
      tensorGradedAlgebraSection T.C U
        ((T.c d).app U ((tensorGradedUnit j (L.tensorPow d)).app U t)) =
    tensorGradedAlgebraSection T.C U
      ((T.c (a + d)).app U
        (((tensorPullback j).map (L.tensorPowAddIso a d).inv).app (j ⁻¹ᵁ U)
          ((boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow d)).inv.app
            (j ⁻¹ᵁ U) (tmulSection (M := (tensorPullback j).obj (L.tensorPow a))
              (N := (tensorPullback j).obj (L.tensorPow d)) (U := j ⁻¹ᵁ U)
              ((tensorGradedUnit j (L.tensorPow a)).app U s)
              ((tensorGradedUnit j (L.tensorPow d)).app U t))))) := by
  have hq (e : ℕ) (z : Γ(L.tensorPow e, U)) :
      tensorGradedAlgebraSection T.C U
          ((T.c e).app U ((tensorGradedUnit j (L.tensorPow e)).app U z)) =
        T.p.right.hom.app (op U) (tensorGradedAlgebraSection T.B U ((T.b e).app U z)) := by
    rw [← algebraMap_section]
    exact (congrArg (fun φ : L.tensorPow e ⟶ commAlgebraSheafModule X.sheaf T.C ↦
      tensorGradedAlgebraSection T.C U (Hom.app (X := X) φ U z)) (T.b_quotient e)).symm
  have hten := unit_tensor j (L.tensorPow a) (L.tensorPow d) U s t
  have hinv :
      (boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow d)).inv.app (j ⁻¹ᵁ U)
        (tmulSection (M := (tensorPullback j).obj (L.tensorPow a))
          (N := (tensorPullback j).obj (L.tensorPow d)) (U := j ⁻¹ᵁ U)
          ((tensorGradedUnit j (L.tensorPow a)).app U s)
          ((tensorGradedUnit j (L.tensorPow d)).app U t)) =
      (tensorGradedUnit j (L.tensorPow a ⊗ L.tensorPow d)).app U (tmulSection s t) := by
    rw [← hten]
    exact inv_app_hom_app_apply_of_iso _ _
  rw [hq, hq, ← map_mul, T.b_multiply, hinv]
  have hn := congrArg
    (fun φ : L.tensorPow a ⊗ L.tensorPow d ⟶
      (pushforward j).obj ((tensorPullback j).obj (L.tensorPow (a + d))) ↦
      φ.app U (tmulSection s t))
    ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.naturality
      (L.tensorPowAddIso a d).inv)
  change (T.p.right.hom.app (op U))
      (tensorGradedAlgebraSection T.B U
        ((T.b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))) = _
  rw [← hq]
  apply congrArg
  apply congrArg
  exact hn

/-- Multiplication descends from the homogeneous algebra to the quotient.
Source: Stacks Project, Tag 09MS, the graded algebra quotient.
(blueprint: lem-sc-square-zero-tensor-graded-quotient-multiply).
Proof: The closed-immersion adjunction unit on each tensor power is locally surjective:
on stalks it is the quotient by the immersion ideal, transported by the unique
adjunction comparison. Locally lift s and t through these units, refining their
covers to a common cover. The equation b_quotient identifies their images under c
with p applied to their b-images. Since p is an algebra morphism, their product is
p applied to the product of those b-images. Apply b_multiply and b_quotient in degree
a+d. Naturality and the monoidal adjunction comparison identify the image of the
tensor product of the lifts with the tensor product of s and t transported through
boundaryPullbackTensorIso. This proves the displayed equality on the common cover;
sheaf separation proves it globally. The argument also works in degree zero, where
tensorPowAddIso and the pullback tensor comparison use the unitors. -/
theorem tensorGradedQuotient_multiply {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (T : TensorGradedPresentation j L)
    (a d : ℕ) (s : Γ((tensorPullback j).obj (L.tensorPow a), ⊤))
    (t : Γ((tensorPullback j).obj (L.tensorPow d), ⊤)) :
    tensorGradedAlgebraSection T.C ⊤ ((T.c a).app ⊤ s) *
      tensorGradedAlgebraSection T.C ⊤ ((T.c d).app ⊤ t) =
      tensorGradedAlgebraSection T.C ⊤ ((T.c (a + d)).app ⊤
        (((tensorPullback j).map (L.tensorPowAddIso a d).inv).app ⊤
          ((boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow d)).inv.app ⊤
            (tmulSection s t)))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let A := (tensorPullback j).obj (L.tensorPow a)
    let D := (tensorPullback j).obj (L.tensorPow d)
    let m : A ⊗ D ⟶ (tensorPullback j).obj (L.tensorPow (a + d)) :=
      (boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow d)).inv ≫
        (tensorPullback j).map (L.tensorPowAddIso a d).inv
    let f : (pushforward j).obj (A ⊗ D) ⟶ commAlgebraSheafModule X.sheaf T.C :=
      (pushforward j).map m ≫ T.c (a + d)
    change tensorGradedAlgebraSection T.C ⊤ ((T.c a).app ⊤ s) *
      tensorGradedAlgebraSection T.C ⊤ ((T.c d).app ⊤ t) =
      tensorGradedAlgebraSection T.C ⊤ (f.app ⊤ (tmulSection (M := A) (N := D) s t))
    apply TopCat.Presheaf.IsSheaf.section_ext T.C.right.property
    intro x hx
    obtain ⟨V, hV, ⟨s', hs⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff
        (tensorGradedUnit j (L.tensorPow a)).mapPresheaf).mp
          (unit_locallySurjective j (L.tensorPow a)) ⊤ s x hx
    obtain ⟨W, hW, ⟨t', ht⟩, hxW⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff
        (tensorGradedUnit j (L.tensorPow d)).mapPresheaf).mp
          (unit_locallySurjective j (L.tensorPow d)) ⊤ t x hx
    change (tensorGradedUnit j (L.tensorPow a)).app V s' =
      ((pushforward j).obj A).presheaf.map (homOfLE hV).op s at hs
    change (tensorGradedUnit j (L.tensorPow d)).app W t' =
      ((pushforward j).obj D).presheaf.map (homOfLE hW).op t at ht
    let O := V ⊓ W
    let iV : O ⟶ V := homOfLE inf_le_left
    let iW : O ⟶ W := homOfLE inf_le_right
    let i : O ⟶ (⊤ : X.Opens) := homOfLE le_top
    let r := (L.tensorPow a).presheaf.map iV.op s'
    let q := (L.tensorPow d).presheaf.map iW.op t'
    have hsO : (tensorGradedUnit j (L.tensorPow a)).app O r =
        ((pushforward j).obj A).presheaf.map i.op s := by
      dsimp only [r]
      rw [Hom.app_presheaf_map, hs, presheaf_map_map_apply]
      rfl
    have htO : (tensorGradedUnit j (L.tensorPow d)).app O q =
        ((pushforward j).obj D).presheaf.map i.op t := by
      dsimp only [q]
      rw [Hom.app_presheaf_map, ht, presheaf_map_map_apply]
      rfl
    refine ⟨O, le_top, ⟨hxV, hxW⟩, ?_⟩
    have hm := multiply_lifts j L T a d O r q
    rw [hsO, htO] at hm
    rw [map_mul]
    let H : X.Modules := commAlgebraSheafModule X.sheaf T.C
    change tensorGradedAlgebraSection T.C O
        (H.presheaf.map i.op ((T.c a).app ⊤ s)) *
      tensorGradedAlgebraSection T.C O
        (H.presheaf.map i.op ((T.c d).app ⊤ t)) =
      tensorGradedAlgebraSection T.C O
        (H.presheaf.map i.op
          (f.app ⊤ (tmulSection (M := A) (N := D) s t)))
    rw [← Hom.app_presheaf_map (T.c a) i s,
      ← Hom.app_presheaf_map (T.c d) i t, ← Hom.app_presheaf_map f i]
    have hten : ((pushforward j).obj (A ⊗ D)).presheaf.map i.op
        (tmulSection (M := A) (N := D) s t) =
      tmulSection (M := A) (N := D) (U := j ⁻¹ᵁ O)
        (((pushforward j).obj A).presheaf.map i.op s)
        (((pushforward j).obj D).presheaf.map i.op t) := by
      exact tmulSection_map (show j ⁻¹ᵁ O ≤ j ⁻¹ᵁ ⊤ from
        leOfHom ((Opens.map j.base).map i)) s t
    rw [hten]
    exact hm

end
end AlgebraicGeometry.Scheme.Modules

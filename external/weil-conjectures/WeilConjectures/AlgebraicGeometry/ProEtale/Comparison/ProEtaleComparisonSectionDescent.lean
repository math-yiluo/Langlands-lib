/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonMatchingTransport

/-! # Descent for the terminal sections of etale inverse images

## References

* Stacks Project, Tag 0GLZ, first (proof) paragraph
* Tag 09XN
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private lemma terminalLift_isIso {S T : Scheme.{u}} (f : T ⟶ S) :
    IsIso (MorphismProperty.Over.homMk
      (pullback.lift f (𝟙 T) ((Category.comp_id _).trans (Category.id_comp _).symm))
      (by simp) : Scheme.Etale.mk (𝟙 T) ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 S))) := by
  let j : Scheme.Etale.mk (𝟙 T) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 S)) :=
    MorphismProperty.Over.homMk
      (pullback.lift f (𝟙 T) ((Category.comp_id _).trans (Category.id_comp _).symm))
      (by simp)
  let i : (MorphismProperty.Over.pullback @Etale ⊤ f).obj
      (Scheme.Etale.mk (𝟙 S)) ≅ Scheme.Etale.mk (𝟙 T) :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) f)) (Category.comp_id _)
  have hj : j = i.inv := by
    apply (cancel_mono i.hom).1
    exact (MorphismProperty.Over.mkIdTerminal (P := @Etale) T).hom_ext _ _
  change IsIso j
  rw [hj]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A presheaf `P` on the pro-étale site whose sections over `Y` are compatibly identified with
the terminal sections of the étale pullback of `F` to `Y` is a sheaf. -/
theorem proEtaleComparisonSectionDescent
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (P : X.ProEtᵒᵖ ⥤ Type (u + 1))
    (e : ∀ Y : X.ProEt, P.obj (op Y) ≃
      ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (Y Z : X.ProEt) (g : Z ⟶ Y) (s : P.obj (op Y)),
      e Z (P.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
          (Y.left.smallGrothendieckTopology @Etale)
          (Z.left.smallGrothendieckTopology @Etale)).unit.app
            ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
          (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e Y s)) :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) P := by
  classical
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange _).2
  intro Y R hR
  obtain ⟨I, Z, g, rfl⟩ := R.exists_eq_ofArrows
  apply (Presieve.isSheafFor_arrows_iff _ _).2
  intro s hs
  obtain ⟨t, ht, hcompat⟩ := proEtaleComparisonMatchingTransport X F P e hres Y Z g s hs
  have hcover : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage Y.left := by
    apply Scheme.proetalePrecoverage_le_fpqcPrecoverage
    have hh := (Scheme.ProEt.mem_precoverage_iff).1 hR
    rw [Presieve.map_ofArrows] at hh
    convert hh using 1 <;> rfl
  obtain ⟨a, ha, hau⟩ := existsUnique_etaleSection_of_fpqc_cover
    (fun i ↦ (Z i).left) (fun i ↦ (g i).left) hcover
    ((Scheme.etaleSetPullback Y.hom).obj F) t hcompat
  let j (i : I) : Scheme.Etale.mk (𝟙 (Z i).left) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (g i).left).obj
        (Scheme.Etale.mk (𝟙 Y.left)) :=
    MorphismProperty.Over.homMk
      (pullback.lift (g i).left (𝟙 (Z i).left)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp)
  have hj (i : I) : IsIso (j i) := terminalLift_isIso (g i).left
  let H := (Scheme.etaleSetPullback Y.hom).obj F
  let r (i : I) := ((Scheme.etaleSetPullback (g i).left).obj H).obj.map (j i).op
  let τ (i : I) := etaleSetTerminalTransport Y.hom (g i).left (Z i).hom
    (MorphismProperty.Over.w (g i)) F
  let η (i : I) := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ (g i).left) (Type (u + 1))
    (Y.left.smallGrothendieckTopology @Etale)
    ((Z i).left.smallGrothendieckTopology @Etale)).unit.app H).hom.app
      (op (Scheme.Etale.mk (𝟙 Y.left)))
  have hr (i : I) : Function.Injective (r i) :=
    (ConcreteCategory.bijective_of_isIso (r i)).injective
  have hglue (i : I) (a' : P.obj (op Y)) :
      P.map (g i).op a' = s i ↔ r i (η i (e Y a')) = t i := by
    rw [ht i]
    change P.map (g i).op a' = s i ↔
      r i (η i (e Y a')) = r i ((τ i).hom (e (Z i) (s i)))
    rw [(hr i).eq_iff]
    have hh := hres Y (Z i) (g i) a'
    change e (Z i) (P.map (g i).op a') = (τ i).inv (η i (e Y a')) at hh
    rw [← (e (Z i)).injective.eq_iff, hh]
    exact (τ i).toEquiv.symm_apply_eq
  refine ⟨(e Y).symm a, ?_, ?_⟩
  · intro i
    apply (hglue i _).2
    simpa only [Equiv.apply_symm_apply] using ha i
  · intro a' ha'
    apply (e Y).injective
    rw [Equiv.apply_symm_apply]
    apply hau
    intro i
    exact (hglue i a').1 (ha' i)

end AlgebraicGeometry

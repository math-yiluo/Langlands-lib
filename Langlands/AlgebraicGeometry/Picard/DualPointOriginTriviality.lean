import Langlands.AlgebraicGeometry.Picard.DualKernelPullback
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Recognizing the origin of a chosen dual by triviality of the Poincaré pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard
open Langlands.SchemeModule Langlands.Scheme.Modules

section Origin

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- A `T`-point of the dual whose Poincaré pullback is trivial as a line bundle is the origin
over `T`. -/
theorem dualPoint_eq_origin_of_forget_iso' {T : Over S} (p : T ⟶ dualScheme A hA)
    (e : (RigidifiedLineBundle.forget _).obj (dualPointFamily A hA p) ≅
      LineBundle.trivial ((relativeSpace A.X.hom).obj T)) :
    p = (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  obtain ⟨r⟩ := RigidifiedLineBundle.nonempty_iso_of_forget_iso pullbackTensorComparisonIsIso
    ((relativeProjection A.X.hom).app T)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) _)
    (L := dualPointFamily A hA p)
    (M := RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A) T) e
  have hclass : dualPointClass picardZeroPullback A hA p =
      dualPointClass picardZeroPullback A hA
        ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) := by
    rw [dualPointClass_origin]
    apply Subtype.ext
    exact Quotient.sound ⟨r⟩
  exact dualPointClass_injective picardZeroPullback A hA _ hclass

/-- A base point of the dual whose Poincaré pullback is trivial as a line bundle is the
origin. -/
theorem dualPoint_eq_origin_of_forget_iso (p : Over.mk (𝟙 S) ⟶ dualScheme A hA)
    (e : (RigidifiedLineBundle.forget _).obj (dualPointFamily A hA p) ≅
      LineBundle.trivial ((relativeSpace A.X.hom).obj (Over.mk (𝟙 S)))) :
    p = dualOrigin A hA := by
  rw [dualPoint_eq_origin_of_forget_iso' A hA p e]
  have hid : (Over.homMk (Over.mk (𝟙 S)).hom : Over.mk (𝟙 S) ⟶ Over.mk (𝟙 S)) =
      𝟙 (Over.mk (𝟙 S)) := by
    apply Over.OverMorphism.ext
    rfl
  rw [hid, Category.id_comp]

/-- The comparison map from the relative space over a `T`-point to the fibre of the
Poincaré projection over that point. -/
def dualPointFibreComparison {T : Over S} (p : T ⟶ dualScheme A hA) :
    (relativeSpace A.X.hom).obj T ⟶
      pullback (pullback.snd A.X.hom (dualScheme A hA).hom) p.left :=
  pullback.lift
    (pullback.lift (pullback.snd T.hom A.X.hom)
      (pullback.fst T.hom A.X.hom ≫ p.left) (by
        rw [Category.assoc, show p.left ≫ (dualScheme A hA).hom = T.hom from Over.w p]
        exact (pullback.condition (f := T.hom) (g := A.X.hom)).symm))
    (pullback.fst T.hom A.X.hom) (pullback.lift_snd _ _ _)

lemma dualPointFibreComparison_comp {T : Over S} (p : T ⟶ dualScheme A hA) :
    dualPointFibreComparison A hA p ≫
        pullback.fst (pullback.snd A.X.hom (dualScheme A hA).hom) p.left ≫
          (pullbackSymmetry (dualScheme A hA).hom A.X.hom).inv =
      (relativeSpace A.X.hom).map p := by
  apply pullback.hom_ext
  · simp only [dualPointFibreComparison, Category.assoc, pullbackSymmetry_inv_comp_fst]
    erw [pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_fst]
  · simp only [dualPointFibreComparison, Category.assoc, pullbackSymmetry_inv_comp_snd]
    erw [pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd]

/-- A `T`-point of the dual whose actual Poincaré fibre bundle is trivial is the origin over
`T`. -/
theorem dualPoint_eq_origin_of_fibre_iso' {T : Over S} (p : T ⟶ dualScheme A hA)
    (e : fibreLineBundle ((baseChange (dualScheme A hA).hom).obj A) (poincareLineBundle A hA)
        p.left ≅ LineBundle.trivial _) :
    p = (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  apply dualPoint_eq_origin_of_forget_iso' A hA p
  let ψ := dualPointFibreComparison A hA p
  let b := pullback.fst (pullback.snd A.X.hom (dualScheme A hA).hom) p.left ≫
    (pullbackSymmetry (dualScheme A hA).hom A.X.hom).inv
  let L₀ := (RigidifiedLineBundle.forget _).obj (poincareFamily A hA)
  have h : (relativeSpace A.X.hom).map p = ψ ≫ b :=
    (dualPointFibreComparison_comp A hA p).symm
  exact eqToIso (congrArg (fun q ↦ (LineBundle.pullback q).obj L₀) h) ≪≫
    ((LineBundle.pullbackComp ψ b).app L₀).symm ≪≫
    (LineBundle.pullback ψ).mapIso
      (((LineBundle.pullbackComp _ _).app L₀).symm ≪≫ e) ≪≫
    LineBundle.pullbackTrivialIso ψ

/-- A base point of the dual whose actual Poincaré fibre bundle is trivial is the origin. -/
theorem dualPoint_eq_origin_of_fibre_iso (p : Over.mk (𝟙 S) ⟶ dualScheme A hA)
    (e : fibreLineBundle ((baseChange (dualScheme A hA).hom).obj A) (poincareLineBundle A hA)
        p.left ≅ LineBundle.trivial _) :
    p = dualOrigin A hA := by
  rw [dualPoint_eq_origin_of_fibre_iso' A hA p e]
  have hid : (Over.homMk (Over.mk (𝟙 S)).hom : Over.mk (𝟙 S) ⟶ Over.mk (𝟙 S)) =
      𝟙 (Over.mk (𝟙 S)) := by
    apply Over.OverMorphism.ext
    rfl
  rw [hid, Category.id_comp]

/-- Let `t : T ⟶ D` be a point of the dual over `S`, and let `X` be any fibre product of the
Poincaré projection `p : A ×_S D ⟶ D` with `t`, with projection `q : X ⟶ A ×_S D`. If the
pulled-back sheaf `q^* P` is isomorphic to the structure sheaf of `X`, then `t` factors
through the origin of the dual. -/
theorem dualPoint_eq_origin_of_isPullback {T : Over S} (t : T ⟶ dualScheme A hA)
    {X : Scheme.{u}} (q : X ⟶ ((baseChange (dualScheme A hA).hom).obj A).X.left)
    (f : X ⟶ T.left)
    (h : IsPullback q f ((baseChange (dualScheme A hA).hom).obj A).X.hom t.left)
    (e : (Scheme.Modules.pullback q).obj (poincareLineBundle A hA).obj ≅
      SheafOfModules.unit X.ringCatSheaf) :
    t = (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  apply dualPoint_eq_origin_of_fibre_iso' A hA t
  let i := h.isoPullback
  have hq : i.inv ≫ q = pullback.fst _ _ := h.isoPullback_inv_fst
  refine ObjectProperty.isoMk _ ?_
  exact (Scheme.Modules.pullbackCongr hq).symm.app _ ≪≫
    ((Scheme.Modules.pullbackComp i.inv q).app _).symm ≪≫
    (Scheme.Modules.pullback i.inv).mapIso e ≪≫
    Langlands.Scheme.Modules.pullbackUnitIso i.inv

end Origin

end Langlands.AbelianScheme

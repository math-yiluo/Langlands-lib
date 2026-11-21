import Langlands.Geometry.FormalGroup.DeligneStructuralBaseChange
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The sheaf of a split cyclic operator on an affine scheme -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

variable {R : CommRingCat.{u}} {M : ModuleCat.{u} R}

set_option backward.isDefEq.respectTransparency false in
private theorem tilde_scalar (a : R) :
    tilde.map (ModuleCat.ofHom (a • (LinearMap.id : Module.End R M))) =
      structuralScalarEnd (tilde M) ((Scheme.ΓSpecIso R).inv a) := by
  apply (tilde.adjunction.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  change tilde.toOpen M ⊤ ≫
    (modulesSpecToSheaf.map (tilde.map (ModuleCat.ofHom (a • LinearMap.id)))).1.app (op ⊤) =
      tilde.toOpen M ⊤ ≫
        (modulesSpecToSheaf.map
          (structuralScalarEnd (tilde M) ((Scheme.ΓSpecIso R).inv a))).1.app (op ⊤)
  rw [tilde.toOpen_map_app]
  apply ModuleCat.hom_ext
  ext x
  change (tilde.toOpen M ⊤).hom (a • x) =
    (show (Spec R).presheaf.obj (op ⊤) from
      (schemeScalar (Spec R) ((Scheme.ΓSpecIso R).inv a)).val (op ⊤)) •
        (show (tilde M).val.obj (op ⊤) from (tilde.toOpen M ⊤).hom x)
  rw [LinearMap.map_smul]
  rfl

variable {d : ℕ} (a : R) (P : End M)
  (hP : P ^ d = ModuleCat.ofHom (a • (LinearMap.id : Module.End R M)))

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification of an actual module operator preserves its power relation. -/
def affinePiSheaf : PiSheaf d (Spec R).sheaf (schemeScalar (Spec R) ((Scheme.ΓSpecIso R).inv a)) where
  module := tilde M
  pi := tilde.map P
  pi_pow U := by
    have h : (End.of (tilde.map P)) ^ d =
        End.of (structuralScalarEnd (tilde M) ((Scheme.ΓSpecIso R).inv a)) := by
      calc
        _ = (tilde.functor R).mapEnd M (P ^ d) :=
          ((tilde.functor R).mapEnd M).map_pow P d |>.symm
        _ = _ := by rw [hP]; exact tilde_scalar a
    have hU := congrArg (sectionEndHom (tilde M) U) h
    rw [map_pow] at hU
    exact hU

variable [NeZero d] {W : ZMod d → ModuleCat.{u} R}
  (j : ∀ i, W i ⟶ M) (p : ∀ i, M ⟶ W i)
  (hdiag : ∀ i, j i ≫ p i = 𝟙 (W i))
  (hoff : ∀ {i k}, k ≠ i → j k ≫ p i = 0)
  (hsum : ∑ i : ZMod d, p i ≫ j i = 𝟙 M)
  (step : ∀ i, W i ⟶ W (i + 1))
  (hstep : ∀ i, j i ≫ P = step i ≫ j (i + 1))

include hdiag in
omit [NeZero d] in
private theorem tilde_splitting (i : ZMod d) : tilde.map (j i) ≫ tilde.map (p i) = 𝟙 _ := by
  rw [← tilde.map_comp, hdiag, tilde.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- The associated affine sheaf preserves a split grading and the cyclic operator. -/
def affineGradedPiSheaf :
    GradedPiSheaf d (Spec R).sheaf (schemeScalar (Spec R) ((Scheme.ΓSpecIso R).inv a)) where
  toPiSheaf := affinePiSheaf a P hP
  component i := splitRange (tilde.map (j i)) (tilde.map (p i)) (tilde_splitting j p hdiag i)
  isInternal U := by
    classical
    apply isInternal_of_finite_splitting (O := (Spec R).presheaf.obj U)
      (fun i => ((tilde.map (j i)).val.app U).hom)
      (fun i => ((tilde.map (p i)).val.app U).hom)
    · intro i x
      exact congrArg (fun g => g.val.app U x) (tilde_splitting j p hdiag i)
    · intro i k hk x
      have h : tilde.map (j k) ≫ tilde.map (p i) = 0 := by
        rw [← tilde.map_comp, hoff hk, tilde.map_zero]
      exact congrArg (fun g => g.val.app U x) h
    · intro x
      have htotal : (∑ i : ZMod d, tilde.map (p i) ≫ tilde.map (j i)) = 𝟙 (tilde M) := by
        change (∑ i : ZMod d, (tilde.functor R).map (p i) ≫
          (tilde.functor R).map (j i)) = _
        simp only [← Functor.map_comp, ← Functor.map_sum, hsum]
        exact tilde.map_id
      let E := SheafOfModules.forget (Spec R).ringCatSheaf ⋙
        PresheafOfModules.evaluation (Spec R).ringCatSheaf.obj U
      have h := congrArg (fun g : tilde M ⟶ tilde M =>
        (E.map g).hom (show E.obj (tilde M) from x)) htotal
      rw [E.map_sum, E.map_id] at h
      simp only [ModuleCat.hom_sum, LinearMap.sum_apply, Functor.map_comp,
        ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
      exact h
  pi_mem U i x hx := by
    obtain ⟨t, rfl⟩ := hx
    refine ⟨(tilde.map (step i)).val.app U t, ?_⟩
    have h := congrArg (fun g => (tilde.map g).val.app U t) (hstep i).symm
    rw [tilde.map_comp, tilde.map_comp] at h
    exact h

/-- Each homogeneous subsheaf is the actual associated sheaf of its source summand. -/
def affineGradedPiSheafComponentIso (i : ZMod d) :
    tilde (W i) ≅ (affineGradedPiSheaf a P hP j p hdiag (@hoff) hsum step hstep).componentSheaf i :=
  splitRangeIso (tilde.map (j i)) (tilde.map (p i)) (tilde_splitting j p hdiag i)

end Langlands.DeligneFormalSpace

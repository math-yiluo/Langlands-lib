import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.IdealSheaf
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof

/-! # The pushforward of the ideal sheaf embeds into the module -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal Scheme.IdealSheafData

variable {X : Scheme.{u}} {Q : X.Modules}

namespace Witness

variable (w : Witness Q)

/-- The function underlying a section of the pushforward of the ideal sheaf. -/
def val {W : X.Opens} (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    Γ(w.Z, w.i ⁻¹ᵁ W) :=
  (show ↥(w.idealSub.obj (op (w.i ⁻¹ᵁ W))) from a).1

lemma val_mem {W : X.Opens} (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.Mem (w.i ⁻¹ᵁ W) (w.val a) :=
  (show ↥(w.idealSub.obj (op (w.i ⁻¹ᵁ W))) from a).2

lemma val_injective {W : X.Opens} :
    Function.Injective (w.val (W := W)) := fun _ _ h =>
  Subtype.ext (p := fun x => x ∈ w.idealSub.obj (op (w.i ⁻¹ᵁ W))) h

lemma val_add {W : X.Opens} (a b : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.val (a + b) = w.val a + w.val b := rfl

lemma val_zero {W : X.Opens} : w.val (0 : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) = 0 :=
  rfl

lemma val_smul {W : X.Opens} (r : Γ(X, W)) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.val (r • a) = w.i.app W r * w.val a := rfl

lemma val_res {W W' : X.Opens} (h : W' ≤ W)
    (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.val (Cech.res h a) = rres (w.pre_le h) (w.val a) := rfl

lemma inT_val {W : X.Opens} (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.InT W (w.val a) :=
  (w.mem_iff_inT W _).1 (w.val_mem a)

/-- The unique killed extension of the multiple of `s` by an admissible function. -/
def phiApp (W : X.Opens) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) : Γ(Q, W) :=
  (w.inT_val a).choose

lemma phiApp_killed (W : X.Opens) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    Killed w.J (w.phiApp W a) :=
  (w.inT_val a).choose_spec.1

lemma phiApp_agrees (W : X.Opens) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.Agrees W (w.val a) (w.phiApp W a) :=
  (w.inT_val a).choose_spec.2

lemma phiApp_eq (W : X.Opens) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W))
    (t : Γ(Q, W)) (ht : Killed w.J t) (hag : w.Agrees W (w.val a) t) : w.phiApp W a = t :=
  agrees_unique (w.phiApp_killed W a) ht (w.phiApp_agrees W a) hag

/-- The abelian-presheaf map underlying the embedding. -/
def phiPresheaf : ((Scheme.Modules.pushforward w.i).obj w.I).presheaf ⟶ Q.presheaf where
  app V := AddCommGrpCat.ofHom
    { toFun := w.phiApp V.unop
      map_zero' := w.phiApp_eq _ _ 0 (killed_zero _) (by rw [w.val_zero]; exact agrees_zero _)
      map_add' := fun a b => w.phiApp_eq _ _ _
        ((w.phiApp_killed _ a).add (w.phiApp_killed _ b))
        (by rw [w.val_add]; exact (w.phiApp_agrees _ a).add (w.phiApp_agrees _ b)) }
  naturality {V V'} f := by
    have hle : V'.unop ≤ V.unop := leOfHom f.unop
    have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
    subst hf
    ext a
    change w.phiApp V'.unop (Cech.res hle a) = Cech.res hle (w.phiApp V.unop a)
    refine w.phiApp_eq _ _ _ ((w.phiApp_killed _ a).res hle) ?_
    rw [w.val_res]
    exact (w.phiApp_agrees _ a).res hle

lemma phiPresheaf_app (W : X.Opens) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.phiPresheaf.app (op W) a = w.phiApp W a := rfl

/-- The embedding of the pushforward of the ideal sheaf into the module. -/
def phi : (Scheme.Modules.pushforward w.i).obj w.I ⟶ Q :=
  ⟨PresheafOfModules.homMk w.phiPresheaf fun V r a => by
    let r' : Γ(X, V.unop) := r
    change w.phiApp V.unop (r' • a) = r' • w.phiApp V.unop a
    refine w.phiApp_eq _ _ _ ((w.phiApp_killed _ a).smul r) ?_
    rw [w.val_smul]
    exact (w.phiApp_agrees _ a).smul r'⟩

lemma phi_app (W : X.Opens) (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.phi.app W a = w.phiApp W a := rfl

lemma phiApp_sub (W : X.Opens) (a b : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) :
    w.phiApp W (a - b) = w.phiApp W a - w.phiApp W b :=
  map_sub (w.phiPresheaf.app (op W)).hom a b

lemma eq_zero_of_phiApp_eq_zero [Q.IsQuasicoherent] (W : X.Opens)
    (a : Γ((Scheme.Modules.pushforward w.i).obj w.I, W)) (ha : w.phiApp W a = 0) : a = 0 := by
  have hag := w.phiApp_agrees W a
  rw [ha] at hag
  by_cases hmeet : ∃ y ∈ W, y ∈ w.Zc
  · obtain ⟨y, hyW, hyZ⟩ := hmeet
    have hptW : w.pt ∈ W := w.pt_mem_of_mem_Zc hyW hyZ
    obtain ⟨g, hgW, hpg⟩ := w.U.2.exists_basicOpen_le (V := W) ⟨w.pt, hptW⟩ w.pt_mem_U
    have hV : (X.affineBasicOpen g).1 ≤ W ⊓ w.U.1 := le_inf hgW (X.basicOpen_le g)
    have h0 := hag (X.affineBasicOpen g) hV
    rw [map_zero] at h0
    obtain ⟨r, hr⟩ := w.app_surjective (X.affineBasicOpen g)
      (rres (w.pre_le (hV.trans inf_le_left)) (w.val a))
    rw [w.mu_eq _ _ _ r hr] at h0
    have hrJ := w.mem_J_of_smul_eq_zero g r h0.symm
    rw [← w.app_eq_zero_iff, hr] at hrJ
    have hpt : w.pt ∈ Set.range w.i := by rw [w.range_i]; exact w.pt_mem_Zc
    obtain ⟨z, hz⟩ := hpt
    have : Nonempty (w.i ⁻¹ᵁ (X.affineBasicOpen g).1) := ⟨⟨z, by
      change w.i z ∈ X.basicOpen g
      rw [hz]
      exact hpg⟩⟩
    apply w.val_injective
    rw [w.val_zero]
    apply map_injective_of_isIntegral (X := w.Z) (homOfLE (w.pre_le (hV.trans inf_le_left)))
    change rres _ (w.val a) = rres _ 0
    rw [map_zero]
    exact hrJ
  · push Not at hmeet
    have hbot : w.i ⁻¹ᵁ W = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hz
      exact hmeet (w.i z) hz (by
        show w.i z ∈ (w.Zc : Set X)
        rw [← w.range_i]
        exact ⟨z, rfl⟩)
    have := ClosedImmersionHigherDirectImageVanishing.subsingleton_sections_of_eq_bot w.I hbot
    exact Subsingleton.elim (α := Γ(w.I, w.i ⁻¹ᵁ W)) a 0

lemma phiApp_injective [Q.IsQuasicoherent] (W : X.Opens) :
    Function.Injective (w.phiApp W) := fun a b h =>
  sub_eq_zero.1 (w.eq_zero_of_phiApp_eq_zero W _ (by rw [w.phiApp_sub, h, sub_self]))

instance [Q.IsQuasicoherent] : Mono w.phi := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V
  exact w.phiApp_injective V.unop

/-- The admissible function `1` over `U`. -/
def oneU : Γ((Scheme.Modules.pushforward w.i).obj w.I, w.U.1) :=
  let one : Γ(w.Z, w.i ⁻¹ᵁ w.U.1) := 1
  (show ↥(w.idealSub.obj (op (w.i ⁻¹ᵁ w.U.1))) from
    ⟨one, (w.mem_iff_inT w.U.1 1).2 inT_one_U⟩)

lemma val_oneU : w.val w.oneU = 1 := rfl

lemma oneU_ne_zero : w.oneU ≠ 0 := by
  intro h
  have hpt : w.pt ∈ Set.range w.i := by rw [w.range_i]; exact w.pt_mem_Zc
  obtain ⟨z, hz⟩ := hpt
  have : Nonempty (w.i ⁻¹ᵁ w.U.1) := ⟨⟨z, by
    change w.i z ∈ w.U.1
    rw [hz]
    exact w.pt_mem_U⟩⟩
  have h1 := congrArg w.val h
  rw [w.val_oneU, w.val_zero] at h1
  exact one_ne_zero h1

lemma not_isZero_pushforward : ¬ IsZero ((Scheme.Modules.pushforward w.i).obj w.I) := by
  intro h
  apply w.oneU_ne_zero
  have := congrArg (fun g : (Scheme.Modules.pushforward w.i).obj w.I ⟶ _ => g.app w.U.1 w.oneU)
    (h.eq_of_src (𝟙 _) 0)
  exact this

lemma not_isZero_I : ¬ IsZero w.I := fun h =>
  w.not_isZero_pushforward ((Scheme.Modules.pushforward w.i).map_isZero h)

end Witness

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules

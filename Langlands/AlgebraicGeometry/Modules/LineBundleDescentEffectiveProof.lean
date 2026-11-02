import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentCore
import Langlands.AlgebraicGeometry.Picard.LineBundleOpenCoverGluing

/-! # Effective descent of line bundles along affine faithfully flat morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

noncomputable section

namespace Langlands.Scheme.Modules.LineBundleFlatDescent

section Gluing

/-- The overlap condition of isomorphism gluing follows from equality of transports to a
common composite. -/
lemma square_compat_of_tr_eq {W A B C : Scheme.{u}} (f : W ⟶ A) (g : W ⟶ B) (a : A ⟶ C)
    (b : B ⟶ C) (h : f ≫ a = g ≫ b) {M N : C.Modules}
    (e₁ : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback a).obj N)
    (e₂ : (Scheme.Modules.pullback b).obj M ⟶ (Scheme.Modules.pullback b).obj N)
    (H : tr f rfl rfl e₁ = tr g h.symm h.symm e₂) :
    (Scheme.Modules.pullback f).map e₁ ≫ (squarePullbackIso b f g a h N).hom =
      (squarePullbackIso b f g a h M).hom ≫ (Scheme.Modules.pullback g).map e₂ := by
  have square (L : C.Modules) : (squarePullbackIso b f g a h L).hom =
      (compIso f a (f ≫ a) rfl L).hom ≫ (compIso g b (f ≫ a) h.symm L).inv :=
    UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso
      b f g a h (f ≫ a) rfl h.symm L
  rw [square N, square M]
  unfold tr at H
  rw [← cancel_epi (compIso f a (f ≫ a) rfl M).inv,
    ← cancel_mono (compIso g b (f ≫ a) h.symm N).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact H

/-- A square comparison followed by composition comparisons to a common composite. -/
lemma square_compIso_coherence {Z C T₁ T₂ S : Scheme.{u}} (f₁ : C ⟶ T₁) (f₂ : C ⟶ T₂)
    (t₁ : T₁ ⟶ S) (t₂ : T₂ ⟶ S) (hsq : f₁ ≫ t₁ = f₂ ≫ t₂) (d : Z ⟶ C) (h₁ : Z ⟶ T₁)
    (h₂ : Z ⟶ T₂) (hd₁ : d ≫ f₁ = h₁) (hd₂ : d ≫ f₂ = h₂) (z : Z ⟶ S) (hz₁ : h₁ ≫ t₁ = z)
    (hz₂ : h₂ ≫ t₂ = z) (M : S.Modules) :
    (Scheme.Modules.pullback d).map (squarePullbackIso t₂ f₁ f₂ t₁ hsq M).hom ≫
        (compIso d f₂ h₂ hd₂ _).hom ≫ (compIso h₂ t₂ z hz₂ M).hom =
      (compIso d f₁ h₁ hd₁ _).hom ≫ (compIso h₁ t₁ z hz₁ M).hom := by
  have hz : d ≫ (f₁ ≫ t₁) = z := by rw [← Category.assoc, hd₁, hz₁]
  have square : (squarePullbackIso t₂ f₁ f₂ t₁ hsq M).hom =
      (compIso f₁ t₁ (f₁ ≫ t₁) rfl M).hom ≫
        (compIso f₂ t₂ (f₁ ≫ t₁) hsq.symm M).inv :=
    UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso
      t₂ f₁ f₂ t₁ hsq (f₁ ≫ t₁) rfl hsq.symm M
  rw [square,
    compIso_assoc d f₂ t₂ h₂ (f₁ ≫ t₁) z hd₂ hsq.symm hz hz₂,
    compIso_assoc d f₁ t₁ h₁ (f₁ ≫ t₁) z hd₁ rfl hz hz₁, Functor.map_comp_assoc,
    ← Functor.map_comp_assoc (Scheme.Modules.pullback d) (compIso f₂ t₂ (f₁ ≫ t₁) _ M).inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

namespace Str

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} {D : Datum p F} {T : Scheme.{u}}

/-- Uniqueness of compatible morphisms, stated for isomorphisms given by their forward
maps. -/
lemma hom_ext' [QuasiCompact p] [Flat p] [Surjective p] {t t' : T ⟶ Y} (ht : t = t')
    {N N' : T.Modules} (hN : IsLocallyFreeRankOne N) (hN' : IsLocallyFreeRankOne N')
    {S : Str D t N} {S' : Str D t' N'} {f g : N ⟶ N'} [IsIso f] [IsIso g]
    (hf : Hom S S' f) (hg : Hom S S' g) : f = g :=
  congrArg Iso.hom (hom_ext (φ := asIso f) (ψ := asIso g) ht hN hN' hf hg)

end Str

end Gluing

section Assembly

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} {D : Datum p F}
  [IsAffineHom p] [Flat p] [Surjective p]

/-- Transitions between descended structures on the members of an open cover satisfy the
cocycle condition. -/
lemma cocycle_of_str (𝒰 : Y.OpenCover.{u}) {N : ∀ i, (𝒰.X i).Modules}
    (hN : ∀ i, IsLocallyFreeRankOne (N i)) (S : ∀ i, Str D (𝒰.f i) (N i))
    (φ : ∀ i j, (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (N i) ≅
      (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (N j))
    (hφ : ∀ i j, Str.Hom ((S i).restrict (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl)
        ((S j).restrict (pullback.snd (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm) (φ i j).hom) :
    OpenCoverModuleGluing.CocycleCondition 𝒰 N φ := by
  intro i j k
  apply OpenCoverModuleGluing.CompEq4.of_eq
  let a := pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k))
  let b := pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k))
  let l : _ ⟶ pullback (𝒰.f j) (𝒰.f k) := pullback.lift (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    (b ≫ pullback.snd (𝒰.f i) (𝒰.f k))
    (by simp only [a, b, Category.assoc, ← pullback.condition, pullback.condition_assoc])
  let tW := a ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
  have hl : l ≫ pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j = tW := by
    simp only [l, tW]
    rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]
  have hb : b ≫ pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i = tW := by
    simp only [b, tW, a, ← pullback.condition_assoc]
  have H1 := Str.Hom.restrict (hφ i j) a tW tW rfl rfl
  have H2 := Str.Hom.square (S j) (pullback.fst (𝒰.f j) (𝒰.f k)) a l
    (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.lift_fst _ _ _).symm
    (pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) tW tW
    rfl pullback.condition.symm rfl hl
  have H3 := Str.Hom.restrict (hφ j k) l tW tW hl hl
  have H4 := Str.Hom.square (S k) (pullback.snd (𝒰.f i) (𝒰.f k)) l b
    (pullback.snd (𝒰.f j) (𝒰.f k)) (pullback.lift_snd _ _ _)
    (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) (pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j) tW tW
    pullback.condition.symm pullback.condition.symm hl hb
  have H5 := Str.Hom.square (S i) (pullback.fst (𝒰.f i) (𝒰.f k)) a b
    (pullback.fst (𝒰.f i) (𝒰.f j)) pullback.condition
    (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) tW tW
    rfl rfl rfl hb
  have H6 := Str.Hom.restrict (hφ i k) b tW tW hb hb
  exact Str.hom_ext' rfl (((hN i).pullback _).pullback _) (((hN k).pullback _).pullback _)
    (Str.Hom.comp rfl H1 (Str.Hom.comp rfl H2 (Str.Hom.comp rfl H3 H4)))
    (Str.Hom.comp rfl H5 H6)

omit [IsAffineHom p] [Flat p] [Surjective p] in
/-- Glued comparisons give compatibilities of the transferred structures on overlaps. -/
lemma hom_overlap_of_compat (𝒰 : Y.OpenCover.{u}) {N : ∀ i, (𝒰.X i).Modules}
    (S : ∀ i, Str D (𝒰.f i) (N i))
    (φ : ∀ i j, (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (N i) ≅
      (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (N j))
    (hφ : ∀ i j, Str.Hom ((S i).restrict (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl)
        ((S j).restrict (pullback.snd (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm) (φ i j).hom)
    (M : Y.Modules) (ψ : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj M ≅ N i)
    (hψ : ∀ i j, (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).map (ψ i).hom ≫
        (φ i j).hom =
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom ≫
        (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).map (ψ j).hom)
    (i j : 𝒰.I₀) :
    Str.Hom (((S i).transfer (ψ i)).restrict (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl)
      (((S j).transfer (ψ j)).restrict (pullback.snd (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm)
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom := by
  have K1 := Str.Hom.restrict (Str.Hom.transfer (S i) (ψ i)) (pullback.fst (𝒰.f i) (𝒰.f j))
    (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl rfl
  have K3 := Str.Hom.inv (φ := (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).mapIso
    (ψ j)) (Str.Hom.restrict (Str.Hom.transfer (S j) (ψ j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
      pullback.condition.symm pullback.condition.symm)
  have e' : (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
      (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom =
      (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).map (ψ i).hom ≫
        (φ i j).hom ≫ ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).mapIso
          (ψ j)).inv := by
    rw [← Category.assoc, hψ i j]
    simp
  rw [e']
  exact Str.Hom.comp rfl K1 (Str.Hom.comp rfl (hφ i j) K3)

omit [IsAffineHom p] [Flat p] [Surjective p] in
/-- Comparison of the descended comparisons of two transferred structures over an
overlap. -/
lemma overlap_comparison (𝒰 : Y.OpenCover.{u}) (M : Y.Modules)
    (S' : ∀ i, Str D (𝒰.f i) ((Scheme.Modules.pullback (𝒰.f i)).obj M))
    (hW : ∀ i j, Str.Hom ((S' i).restrict (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl)
      ((S' j).restrict (pullback.snd (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm)
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom)
    (i j : 𝒰.I₀) {Z : Scheme.{u}} (c : Z ⟶ X) (h₁ : Z ⟶ 𝒰.X i) (h₂ : Z ⟶ 𝒰.X j)
    (z : Z ⟶ Y) (hz₁ : h₁ ≫ 𝒰.f i = z) (hz₂ : h₂ ≫ 𝒰.f j = z)
    (hs₁ : h₁ ≫ 𝒰.f i = c ≫ p) (hs₂ : h₂ ≫ 𝒰.f j = c ≫ p) :
    (compIso h₁ (𝒰.f i) z hz₁ M).inv ≫ ((S' i).γ Z c h₁ hs₁).hom =
      (compIso h₂ (𝒰.f j) z hz₂ M).inv ≫ ((S' j).γ Z c h₂ hs₂).hom := by
  let d := pullback.lift h₁ h₂ (hz₁.trans hz₂.symm)
  have hd₁ : d ≫ pullback.fst (𝒰.f i) (𝒰.f j) = h₁ := pullback.lift_fst _ _ _
  have hd₂ : d ≫ pullback.snd (𝒰.f i) (𝒰.f j) = h₂ := pullback.lift_snd _ _ _
  have hs : d ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = c ≫ p := by
    rw [← Category.assoc, hd₁, hs₁]
  have W := hW i j Z c d hs hs
  rw [Str.restrict_γ (S' j) _ _ _ c d hs h₂ hd₂ hs₂,
    Str.restrict_γ (S' i) _ _ _ c d hs h₁ hd₁ hs₁] at W
  have coh := square_compIso_coherence (pullback.fst (𝒰.f i) (𝒰.f j))
    (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) (𝒰.f j) pullback.condition d h₁ h₂ hd₁ hd₂ z
    hz₁ hz₂ M
  rw [← cancel_epi (compIso h₁ (𝒰.f i) z hz₁ M).hom, Iso.hom_inv_id_assoc,
    ← cancel_epi (compIso d (pullback.fst (𝒰.f i) (𝒰.f j)) h₁ hd₁ _).hom, ← W,
    ← reassoc_of% coh]
  simp

omit [IsAffineHom p] [Flat p] [Surjective p] in
/-- Compatible descended structures on an open cover of the base give an isomorphism of the
pullback of the glued module with `F`. -/
lemma nonempty_iso_of_overlap (𝒰 : Y.OpenCover.{u}) (M : Y.Modules)
    (S' : ∀ i, Str D (𝒰.f i) ((Scheme.Modules.pullback (𝒰.f i)).obj M))
    (hW : ∀ i j, Str.Hom ((S' i).restrict (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl)
      ((S' j).restrict (pullback.snd (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm)
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom) :
    Nonempty ((Scheme.Modules.pullback p).obj M ≅ F) := by
  have hc : ∀ i, pullback.fst p (𝒰.f i) ≫ p = pullback.snd p (𝒰.f i) ≫ 𝒰.f i :=
    fun i ↦ pullback.condition
  let e : ∀ i, (Scheme.Modules.pullback (pullback.fst p (𝒰.f i))).obj
      ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst p (𝒰.f i))).obj F := fun i ↦
    compIso (pullback.fst p (𝒰.f i)) p (pullback.snd p (𝒰.f i) ≫ 𝒰.f i) (hc i) M ≪≫
      (compIso (pullback.snd p (𝒰.f i)) (𝒰.f i) (pullback.snd p (𝒰.f i) ≫ 𝒰.f i) rfl M).symm ≪≫
        (S' i).γ _ (pullback.fst p (𝒰.f i)) (pullback.snd p (𝒰.f i)) (hc i).symm
  suffices hov : ∀ i j,
      (Scheme.Modules.pullback (pullback.fst (pullback.fst p (𝒰.f i))
          (pullback.fst p (𝒰.f j)))).map (e i).hom ≫
          (squarePullbackIso (pullback.fst p (𝒰.f j))
            (pullback.fst (pullback.fst p (𝒰.f i)) (pullback.fst p (𝒰.f j)))
            (pullback.snd (pullback.fst p (𝒰.f i)) (pullback.fst p (𝒰.f j)))
            (pullback.fst p (𝒰.f i)) pullback.condition F).hom =
        (squarePullbackIso (pullback.fst p (𝒰.f j))
          (pullback.fst (pullback.fst p (𝒰.f i)) (pullback.fst p (𝒰.f j)))
          (pullback.snd (pullback.fst p (𝒰.f i)) (pullback.fst p (𝒰.f j)))
          (pullback.fst p (𝒰.f i)) pullback.condition ((Scheme.Modules.pullback p).obj M)).hom ≫
          (Scheme.Modules.pullback (pullback.snd (pullback.fst p (𝒰.f i))
            (pullback.fst p (𝒰.f j)))).map (e j).hom by
    obtain ⟨E, -, -⟩ := openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing
      X (𝒰.pullback₁ p) _ _ e hov
    exact ⟨E⟩
  intro i j
  apply square_compat_of_tr_eq
  let F₁ := pullback.fst (pullback.fst p (𝒰.f i)) (pullback.fst p (𝒰.f j))
  let F₂ := pullback.snd (pullback.fst p (𝒰.f i)) (pullback.fst p (𝒰.f j))
  have hF : F₂ ≫ pullback.fst p (𝒰.f j) = F₁ ≫ pullback.fst p (𝒰.f i) :=
    pullback.condition.symm
  let c := F₁ ≫ pullback.fst p (𝒰.f i)
  let h₁ := F₁ ≫ pullback.snd p (𝒰.f i)
  let h₂ := F₂ ≫ pullback.snd p (𝒰.f j)
  let z := h₁ ≫ 𝒰.f i
  have hm₁ : F₁ ≫ (pullback.snd p (𝒰.f i) ≫ 𝒰.f i) = z := (Category.assoc _ _ _).symm
  have hcz : c ≫ p = z := by
    simp only [c, z, h₁, Category.assoc, pullback.condition]
  have hm₂ : F₂ ≫ (pullback.snd p (𝒰.f j) ≫ 𝒰.f j) = z := by
    rw [← hcz, ← pullback.condition, ← Category.assoc, hF, Category.assoc]
  have hz₂ : h₂ ≫ 𝒰.f j = z := by rw [Category.assoc, hm₂]
  have hs₁ : h₁ ≫ 𝒰.f i = c ≫ p := hcz.symm
  have hs₂ : h₂ ≫ 𝒰.f j = c ≫ p := hz₂.trans hcz.symm
  simp only [e, Iso.trans_hom, Iso.symm_hom]
  rw [tr_comp F₁ rfl hm₁ rfl, tr_comp F₁ hm₁ rfl rfl,
    tr_compIso F₁ _ p _ (hc i) c z rfl hm₁ hcz,
    tr_compIso_inv F₁ _ (𝒰.f i) _ rfl h₁ z rfl hm₁ rfl,
    ← (S' i).nat _ _ F₁ _ _ (hc i).symm c h₁ hs₁ rfl rfl,
    tr_comp F₂ hF hm₂ hF, tr_comp F₂ hm₂ rfl hF,
    tr_compIso F₂ _ p _ (hc j) c z hF hm₂ hcz,
    tr_compIso_inv F₂ _ (𝒰.f j) _ rfl h₂ z rfl hm₂ hz₂,
    ← (S' j).nat _ _ F₂ _ _ (hc j).symm c h₂ hs₂ hF rfl,
    overlap_comparison 𝒰 M S' hW i j c h₁ h₂ z rfl hz₂ hs₁ hs₂]

end Assembly

end Langlands.Scheme.Modules.LineBundleFlatDescent

namespace Langlands.Scheme.Modules

open LineBundleFlatDescent

/-- Effective descent of line bundles along affine faithfully flat morphisms. -/
theorem lineBundleDescentEffective : LineBundleDescentEffectiveStatement.{u} := by
  intro X Y p hp hpf hps F hF θ hnat hcoc
  let D : Datum p F := ⟨θ, hnat, hcoc⟩
  choose N hN hS using fun i ↦ exists_str D hF (Y.affineCover.f i)
  have hφ := fun i j ↦ Str.exists_hom ((hN i).pullback _) ((hN j).pullback _)
    (((hS i).some).restrict (pullback.fst (Y.affineCover.f i) (Y.affineCover.f j))
      (pullback.fst (Y.affineCover.f i) (Y.affineCover.f j) ≫ Y.affineCover.f i) rfl)
    (((hS j).some).restrict (pullback.snd (Y.affineCover.f i) (Y.affineCover.f j))
      (pullback.fst (Y.affineCover.f i) (Y.affineCover.f j) ≫ Y.affineCover.f i)
      pullback.condition.symm)
  choose φ hφ using hφ
  let GD : LineBundleGluingData Y.affineCover :=
    { bundle := fun i ↦ ⟨N i, hN i⟩
      transition := φ
      cocycle := cocycle_of_str Y.affineCover hN (fun i ↦ (hS i).some) φ hφ }
  exact ⟨GD.gluedModule, GD.gluedModule_rankOne,
    nonempty_iso_of_overlap Y.affineCover GD.gluedModule
      (fun i ↦ ((hS i).some).transfer (GD.moduleIso i))
      (hom_overlap_of_compat Y.affineCover (fun i ↦ (hS i).some) φ hφ GD.gluedModule
        GD.moduleIso GD.moduleIso_compatible)⟩

end Langlands.Scheme.Modules

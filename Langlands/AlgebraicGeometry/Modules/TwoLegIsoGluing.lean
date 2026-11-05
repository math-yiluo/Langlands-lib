import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof

/-! # Gluing isomorphisms with two prescribed restrictions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.TwoLegIsoGluing

open UnitCocycleDescentUniqueness
open LineBundleIsoDescent

variable {Y₁ Y₂ Y : Scheme.{u}} (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)

/-- The actual unit maps from every open subscheme to its two inverse images
jointly distinguish global units. -/
def UnitsJointlyInjectiveOnOpens : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Y), IsOpenImmersion t →
    Function.Injective (fun s : Γ(T, ⊤)ˣ ↦
      (Units.map (pullback.snd j₁ t).appTop.hom.toMonoidHom s,
        Units.map (pullback.snd j₂ t).appTop.hom.toMonoidHom s))

/-- Joint injectivity on all open subschemes follows from joint injectivity on
open subschemes that are affine, by separation for an affine open cover. -/
lemma unitsJointlyInjectiveOnOpens_of_affine
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Y), IsAffine T → IsOpenImmersion t →
      Function.Injective (fun s : Γ(T, ⊤)ˣ ↦
        (Units.map (pullback.snd j₁ t).appTop.hom.toMonoidHom s,
          Units.map (pullback.snd j₂ t).appTop.hom.toMonoidHom s))) :
    UnitsJointlyInjectiveOnOpens j₁ j₂ := by
  intro T t ht s s' hss'
  simp only [Prod.mk.injEq] at hss'
  obtain ⟨h₁, h₂⟩ := hss'
  apply Units.ext
  apply T.affineCover.ext_elem
  intro k
  let v := T.affineCover.f k
  have hrestrict (V : Scheme.{u}) (j : V ⟶ Y)
      (hj : Units.map (pullback.snd j t).appTop.hom.toMonoidHom s =
        Units.map (pullback.snd j t).appTop.hom.toMonoidHom s') :
      Units.map (pullback.snd j (v ≫ t)).appTop.hom.toMonoidHom
          (Units.map v.appTop.hom.toMonoidHom s) =
        Units.map (pullback.snd j (v ≫ t)).appTop.hom.toMonoidHom
          (Units.map v.appTop.hom.toMonoidHom s') := by
    let q : pullback j (v ≫ t) ⟶ pullback j t :=
      pullback.map j (v ≫ t) j t (𝟙 _) v (𝟙 _) (by simp) (by simp)
    have hq : pullback.snd j (v ≫ t) ≫ v = q ≫ pullback.snd j t := by
      simp [q]
    have hv := congrArg (Units.map q.appTop.hom.toMonoidHom) hj
    apply Units.ext
    have hv' := congrArg Units.val hv
    simp only [Units.coe_map] at hv' ⊢
    show (pullback.snd j (v ≫ t)).appTop.hom (v.appTop.hom s.val) =
      (pullback.snd j (v ≫ t)).appTop.hom (v.appTop.hom s'.val)
    have e₁ := congrArg (fun φ ↦ φ.hom s.val) (Scheme.Hom.comp_appTop
      (pullback.snd j (v ≫ t)) v)
    have e₂ := congrArg (fun φ ↦ φ.hom s'.val) (Scheme.Hom.comp_appTop
      (pullback.snd j (v ≫ t)) v)
    have e₃ := congrArg (fun φ ↦ φ.hom s.val) (Scheme.Hom.comp_appTop q
      (pullback.snd j t))
    have e₄ := congrArg (fun φ ↦ φ.hom s'.val) (Scheme.Hom.comp_appTop q
      (pullback.snd j t))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e₁ e₂ e₃ e₄
    rw [← e₁, ← e₂, hq, e₃, e₄]
    exact hv'
  have hk := h _ (v ≫ t) inferInstance inferInstance
    (Prod.ext (hrestrict Y₁ j₁ h₁) (hrestrict Y₂ j₂ h₂))
  exact congrArg Units.val hk

variable {M N : Y.Modules}
  (e₁ : (Scheme.Modules.pullback j₁).obj M ≅ (Scheme.Modules.pullback j₁).obj N)
  (e₂ : (Scheme.Modules.pullback j₂).obj M ≅ (Scheme.Modules.pullback j₂).obj N)

/-- Compatible isomorphisms between trivial modules on an open subscheme
agree if their two unit restriction maps are jointly injective. -/
lemma compatible_unique
    (hU : UnitsJointlyInjectiveOnOpens j₁ j₂)
    {T : Scheme.{u}} (t : T ⟶ Y) (ht : IsOpenImmersion t)
    (τ : (Scheme.Modules.pullback t).obj M ≅ structureModule T)
    (σ : (Scheme.Modules.pullback t).obj N ≅ structureModule T)
    (φ ψ : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N)
    (hφ₁ : LineBundleIsoDescent.Compatible j₁ e₁ t φ.hom)
    (hφ₂ : LineBundleIsoDescent.Compatible j₂ e₂ t φ.hom)
    (hψ₁ : LineBundleIsoDescent.Compatible j₁ e₁ t ψ.hom)
    (hψ₂ : LineBundleIsoDescent.Compatible j₂ e₂ t ψ.hom) : φ = ψ := by
  have hpull (V : Scheme.{u}) (j : V ⟶ Y)
      (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
      (hφ : LineBundleIsoDescent.Compatible j e t φ.hom)
      (hψ : LineBundleIsoDescent.Compatible j e t ψ.hom) :
      (Scheme.Modules.pullback (pullback.snd j t)).mapIso φ =
        (Scheme.Modules.pullback (pullback.snd j t)).mapIso ψ := by
    apply Iso.ext
    have h₁ := hφ _ (pullback.fst j t) (pullback.snd j t) pullback.condition.symm
    have h₂ := hψ _ (pullback.fst j t) (pullback.snd j t) pullback.condition.symm
    unfold LineBundleIsoDescent.CompatibleAt at h₁ h₂
    rw [← h₂] at h₁
    exact (cancel_mono _).mp h₁
  have hscalar (V : Scheme.{u}) (j : V ⟶ Y)
      (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
      (hφ : LineBundleIsoDescent.Compatible j e t φ.hom)
      (hψ : LineBundleIsoDescent.Compatible j e t ψ.hom) :
      Units.map (pullback.snd j t).appTop.hom.toMonoidHom
          (structureAutScalar (τ.symm ≪≫ φ ≪≫ σ)) =
        Units.map (pullback.snd j t).appTop.hom.toMonoidHom
          (structureAutScalar (τ.symm ≪≫ ψ ≪≫ σ)) := by
    rw [← structureAutScalar_pullback, ← structureAutScalar_pullback,
      ← normalizeIso_pullback (pullback.snd j t) τ σ φ,
      ← normalizeIso_pullback (pullback.snd j t) τ σ ψ,
      hpull V j e hφ hψ]
  have hs := hU T t ht (Prod.ext
    (hscalar Y₁ j₁ e₁ hφ₁ hψ₁) (hscalar Y₂ j₂ e₂ hφ₂ hψ₂))
  have hd := structureAutScalar_injective hs
  apply Iso.ext
  apply (cancel_epi τ.inv).mp
  apply (cancel_mono σ.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using congrArg Iso.hom hd

/-- A global map is the prescribed restriction if it agrees on the base cover
with maps compatible with that restriction. -/
lemma pullback_eq_of_local_compatible
    {V : Scheme.{u}} (j : V ⟶ Y)
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
    (𝒰 : Y.OpenCover.{u})
    (E : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj M ≅
      (Scheme.Modules.pullback (𝒰.f i)).obj N)
    (hE : ∀ i, LineBundleIsoDescent.Compatible j e (𝒰.f i) (E i).hom)
    (E₀ : M ≅ N)
    (hE₀ : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map E₀.hom = (E i).hom) :
    (Scheme.Modules.pullback j).mapIso E₀ = e := by
  apply Iso.ext
  apply LineBundleIsoDescent.hom_ext_of_openCover (𝒰.pullback₁ j)
  intro i
  have hs : pullback.snd j (𝒰.f i) ≫ 𝒰.f i = pullback.fst j (𝒰.f i) ≫ j :=
    pullback.condition.symm
  have c := hE i _ (pullback.fst j (𝒰.f i)) (pullback.snd j (𝒰.f i)) hs
  unfold LineBundleIsoDescent.CompatibleAt at c
  have n := squarePullbackIso_naturality j (pullback.snd j (𝒰.f i))
    (pullback.fst j (𝒰.f i)) (𝒰.f i) hs E₀.hom
  rw [hE₀ i, c] at n
  exact ((cancel_epi _).mp n).symm

/-- Local compatible lifts between locally trivial modules glue to a unique
actual isomorphism with both prescribed ordinary pullbacks. -/
lemma existsUnique_iso_of_local
    (hU : UnitsJointlyInjectiveOnOpens j₁ j₂)
    (𝒰 : Y.OpenCover.{u})
    (hM : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj M ≅
      structureModule (𝒰.X i)))
    (hN : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj N ≅
      structureModule (𝒰.X i)))
    (hlocal : ∀ i, ∃ E : (Scheme.Modules.pullback (𝒰.f i)).obj M ≅
        (Scheme.Modules.pullback (𝒰.f i)).obj N,
      LineBundleIsoDescent.Compatible j₁ e₁ (𝒰.f i) E.hom ∧
        LineBundleIsoDescent.Compatible j₂ e₂ (𝒰.f i) E.hom) :
    ∃! E₀ : M ≅ N, (Scheme.Modules.pullback j₁).mapIso E₀ = e₁ ∧
      (Scheme.Modules.pullback j₂).mapIso E₀ = e₂ := by
  have huniq : ∀ E E' : M ≅ N,
      (Scheme.Modules.pullback j₁).mapIso E = e₁ →
      (Scheme.Modules.pullback j₂).mapIso E = e₂ →
      (Scheme.Modules.pullback j₁).mapIso E' = e₁ →
      (Scheme.Modules.pullback j₂).mapIso E' = e₂ → E = E' := by
    intro E E' h₁ h₂ h₁' h₂'
    apply Iso.ext
    apply LineBundleIsoDescent.hom_ext_of_openCover 𝒰
    intro i
    have heq := compatible_unique j₁ j₂ e₁ e₂ hU (𝒰.f i) inferInstance
      (hM i).some (hN i).some
      ((Scheme.Modules.pullback (𝒰.f i)).mapIso E)
      ((Scheme.Modules.pullback (𝒰.f i)).mapIso E')
      (compatible_pullback j₁ e₁ (𝒰.f i) E.hom (by rw [← h₁]; rfl))
      (compatible_pullback j₂ e₂ (𝒰.f i) E.hom (by rw [← h₂]; rfl))
      (compatible_pullback j₁ e₁ (𝒰.f i) E'.hom (by rw [← h₁']; rfl))
      (compatible_pullback j₂ e₂ (𝒰.f i) E'.hom (by rw [← h₂']; rfl))
    exact congrArg Iso.hom heq
  choose E hE using hlocal
  obtain ⟨E₀, hE₀, -⟩ := openCoverIsoGluing_of_homGluing
    OpenCoverHomGluing.openCoverHomGluing Y 𝒰 M N E (by
    intro i j
    let t := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have ht : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j = t :=
      pullback.condition.symm
    have hi₁ := LineBundleIsoDescent.Compatible.change_base j₁ e₁ (𝒰.f i)
      (pullback.fst (𝒰.f i) (𝒰.f j)) t rfl _ (hE i).1
    have hi₂ := LineBundleIsoDescent.Compatible.change_base j₂ e₂ (𝒰.f i)
      (pullback.fst (𝒰.f i) (𝒰.f j)) t rfl _ (hE i).2
    have hj₁ := LineBundleIsoDescent.Compatible.change_base j₁ e₁ (𝒰.f j)
      (pullback.snd (𝒰.f i) (𝒰.f j)) t ht _ (hE j).1
    have hj₂ := LineBundleIsoDescent.Compatible.change_base j₂ e₂ (𝒰.f j)
      (pullback.snd (𝒰.f i) (𝒰.f j)) t ht _ (hE j).2
    have heq := compatible_unique j₁ j₂ e₁ e₂ hU t inferInstance
      (nonempty_trivial_change_base (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j))
        t rfl (hM i)).some
      (nonempty_trivial_change_base (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j))
        t rfl (hN i)).some
      ((compIso _ _ t rfl M).symm ≪≫
        (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).mapIso (E i) ≪≫
          compIso _ _ t rfl N)
      ((compIso _ _ t ht M).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).mapIso (E j) ≪≫
          compIso _ _ t ht N)
      (by simpa using hi₁) (by simpa using hi₂)
      (by simpa using hj₁) (by simpa using hj₂)
    have heq' := congrArg Iso.hom heq
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at heq'
    rw [squarePullbackIso_hom_eq_compIso _ _ _ _ _ t rfl ht,
      squarePullbackIso_hom_eq_compIso _ _ _ _ _ t rfl ht]
    rw [← cancel_epi (compIso _ _ t rfl M).inv,
      ← cancel_mono (compIso _ _ t ht N).hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
      using heq')
  have h₁ := pullback_eq_of_local_compatible j₁ e₁ 𝒰 E (fun i ↦ (hE i).1) E₀ hE₀
  have h₂ := pullback_eq_of_local_compatible j₂ e₂ 𝒰 E (fun i ↦ (hE i).2) E₀ hE₀
  exact ⟨E₀, ⟨h₁, h₂⟩, fun E h ↦ huniq E E₀ h.1 h.2 h₁ h₂⟩

section Glue

variable (hU : UnitsJointlyInjectiveOnOpens j₁ j₂)
  (𝒰 : Y.OpenCover.{u})
  (hM : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj M ≅
    structureModule (𝒰.X i)))
  (hN : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj N ≅
    structureModule (𝒰.X i)))
  (hlocal : ∀ i, ∃ E : (Scheme.Modules.pullback (𝒰.f i)).obj M ≅
      (Scheme.Modules.pullback (𝒰.f i)).obj N,
    LineBundleIsoDescent.Compatible j₁ e₁ (𝒰.f i) E.hom ∧
      LineBundleIsoDescent.Compatible j₂ e₂ (𝒰.f i) E.hom)

/-- The unique actual isomorphism glued from compatible local lifts. -/
def glueIso : M ≅ N :=
  (existsUnique_iso_of_local j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal).exists.choose

/-- The glued isomorphism has the first prescribed ordinary pullback. -/
lemma glueIso_pullback₁ :
    (Scheme.Modules.pullback j₁).mapIso (glueIso j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal) = e₁ :=
  (existsUnique_iso_of_local j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal).exists.choose_spec.1

/-- The glued isomorphism has the second prescribed ordinary pullback. -/
lemma glueIso_pullback₂ :
    (Scheme.Modules.pullback j₂).mapIso (glueIso j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal) = e₂ :=
  (existsUnique_iso_of_local j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal).exists.choose_spec.2

/-- Every isomorphism with both prescribed ordinary pullbacks is the glued one. -/
lemma eq_glueIso (E : M ≅ N) (h₁ : (Scheme.Modules.pullback j₁).mapIso E = e₁)
    (h₂ : (Scheme.Modules.pullback j₂).mapIso E = e₂) :
    E = glueIso j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal :=
  (existsUnique_iso_of_local j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal).unique ⟨h₁, h₂⟩
    ⟨glueIso_pullback₁ j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal,
      glueIso_pullback₂ j₁ j₂ e₁ e₂ hU 𝒰 hM hN hlocal⟩

end Glue

end Langlands.Scheme.Modules.TwoLegIsoGluing

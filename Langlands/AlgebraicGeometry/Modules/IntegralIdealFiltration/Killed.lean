import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Filtered

/-! # Sections of a module killed by an ideal sheaf -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal

variable {X : Scheme.{u}}

section Locality

variable {M : X.Modules}

/-- A section whose restrictions to all affine opens of its domain vanish is zero. -/
lemma eq_zero_of_forall_affine {W : X.Opens} (t : Γ(M, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W), Cech.res hV t = 0) : t = 0 := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have key : ∀ x : W, ∃ (V : X.affineOpens) (hV : V.1 ≤ W), x.1 ∈ V.1 := by
    intro x
    obtain ⟨V, hV, hxV, hVW⟩ :=
      (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) x.2
    exact ⟨⟨V, hV⟩, hVW, hxV⟩
  choose V hV hxV using key
  refine TopCat.Sheaf.eq_of_locally_eq' (F := F) (U := fun x => (V x).1) W
    (fun x => homOfLE (hV x)) ?_ t 0 (fun x => ?_)
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  · rw [map_zero]
    exact h (V x) (hV x)

/-- A section which vanishes near every point of its domain is zero. -/
lemma eq_zero_of_local {W : X.Opens} (t : Γ(M, W))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧ Cech.res hV t = 0) : t = 0 := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  choose V hV hxV hres using fun x : W => h x.1 x.2
  refine TopCat.Sheaf.eq_of_locally_eq' (F := F) (U := V) W
    (fun x => homOfLE (hV x)) ?_ t 0 (fun x => ?_)
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  · rw [map_zero]
    exact hres x

/-- Two sections which agree near every point of their domain are equal. -/
lemma eq_of_local {W : X.Opens} (t t' : Γ(M, W))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧ Cech.res hV t = Cech.res hV t') :
    t = t' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_local _ fun x hx => ?_
  obtain ⟨V, hV, hxV, he⟩ := h x hx
  exact ⟨V, hV, hxV, by rw [map_sub, he, sub_self]⟩

/-- Two sections with the same restrictions to all affine opens of their domain are equal. -/
lemma eq_of_forall_affine {W : X.Opens} (t t' : Γ(M, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W), Cech.res hV t = Cech.res hV t') : t = t' := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_affine _ fun V hV => by rw [map_sub, h V hV, sub_self]

end Locality

variable (J : X.IdealSheafData) {Q : X.Modules}

/-- A section killed by the ideal sheaf `J` on every affine open inside its domain. -/
def Killed {W : X.Opens} (t : Γ(Q, W)) : Prop :=
  ∀ (V : X.affineOpens) (h : V.1 ≤ W), ∀ c ∈ J.ideal V, c • Cech.res h t = 0

variable {J}

lemma Killed.res {W W' : X.Opens} {t : Γ(Q, W)} (ht : Killed J t) (h : W' ≤ W) :
    Killed J (Cech.res h t) := fun V hV c hc => by
  rw [Cech.res_res]
  exact ht V (hV.trans h) c hc

lemma killed_zero (W : X.Opens) : Killed J (0 : Γ(Q, W)) := fun V hV c _ => by
  rw [map_zero, smul_zero]

lemma Killed.add {W : X.Opens} {t t' : Γ(Q, W)} (ht : Killed J t) (ht' : Killed J t') :
    Killed J (t + t') := fun V hV c hc => by
  rw [map_add, smul_add, ht V hV c hc, ht' V hV c hc, add_zero]

lemma Killed.sub {W : X.Opens} {t t' : Γ(Q, W)} (ht : Killed J t) (ht' : Killed J t') :
    Killed J (t - t') := fun V hV c hc => by
  rw [map_sub, smul_sub, ht V hV c hc, ht' V hV c hc, sub_zero]

lemma Killed.smul {W : X.Opens} {t : Γ(Q, W)} (ht : Killed J t) (r : Γ(X, W)) :
    Killed J (r • t) := fun V hV c hc => by
  rw [res_smul, smul_comm, ht V hV c hc, smul_zero]

/-- On an affine open, being killed by `J` only needs to be checked on the open itself. -/
lemma killed_of_affine {W : X.Opens} (hW : IsAffineOpen W) {t : Γ(Q, W)}
    (ht : ∀ c ∈ J.ideal ⟨W, hW⟩, c • t = 0) : Killed J t := by
  intro V hV c hc
  rw [← J.map_ideal (U := V) (V := ⟨W, hW⟩) hV] at hc
  let K : Ideal Γ(X, V.1) :=
    LinearMap.ker (LinearMap.toSpanSingleton Γ(X, V.1) Γ(Q, V.1) (Cech.res hV t))
  have hle : (J.ideal ⟨W, hW⟩).map (X.presheaf.map (homOfLE hV).op).hom ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro c' hc'
    change (rres hV c') • Cech.res hV t = 0
    rw [← res_smul, ht c' hc', map_zero]
  exact hle hc

lemma Killed.affine {W : X.Opens} (hW : IsAffineOpen W) {t : Γ(Q, W)} (ht : Killed J t) :
    ∀ c ∈ J.ideal ⟨W, hW⟩, c • t = 0 := fun c hc => by
  simpa using ht ⟨W, hW⟩ le_rfl c hc

/-- Being killed by `J` is a local property. -/
lemma killed_of_cover {W : X.Opens} {t : Γ(Q, W)}
    (h : ∀ x ∈ W, ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧ Killed J (Cech.res hW' t)) :
    Killed J t := by
  intro V hV c hc
  apply eq_zero_of_local
  intro x hx
  obtain ⟨W', hW', hxW', hk⟩ := h x (hV hx)
  obtain ⟨V', hV'a, hxV', hV'le⟩ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ V.1 ⊓ W' from ⟨hx, hxW'⟩)
  refine ⟨V', hV'le.trans inf_le_left, hxV', ?_⟩
  have hc' : rres (hV'le.trans inf_le_left) c ∈ J.ideal ⟨V', hV'a⟩ :=
    J.ideal_le_comap_ideal (U := ⟨V', hV'a⟩) (V := V) (hV'le.trans inf_le_left) hc
  have := hk ⟨V', hV'a⟩ (hV'le.trans inf_le_right) _ hc'
  rw [Cech.res_res] at this
  rw [res_smul, Cech.res_res]
  exact this

/-- A killed section vanishes on opens where the ideal is the unit ideal on all affine opens. -/
lemma Killed.eq_zero_of_ideal_eq_top {W : X.Opens} {t : Γ(Q, W)} (ht : Killed J t)
    (htop : ∀ (V : X.affineOpens), V.1 ≤ W → J.ideal V = ⊤) : t = 0 := by
  apply eq_zero_of_forall_affine
  intro V hV
  have := ht V hV 1 (by rw [htop V hV]; trivial)
  rwa [one_smul] at this

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules

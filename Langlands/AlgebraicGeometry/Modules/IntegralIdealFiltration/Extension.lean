import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Witness

/-! # Killed sections extending multiples of the witness section -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal Scheme.IdealSheafData

variable {X : Scheme.{u}} {Q : X.Modules}

namespace Witness

variable (w : Witness Q)

/-- On every affine open of `W ∩ U`, the section `t` is the multiple of `s` by `a`. -/
def Agrees (W : X.Opens) (a : Γ(w.Z, w.i ⁻¹ᵁ W)) (t : Γ(Q, W)) : Prop :=
  ∀ (V : X.affineOpens) (hV : V.1 ≤ W ⊓ w.U.1),
    Cech.res (hV.trans inf_le_left) t =
      w.mu V (hV.trans inf_le_right) (rres (w.pre_le (hV.trans inf_le_left)) a)

/-- The multiple of `s` by `a` extends to a section over `W` killed by the ideal sheaf. -/
def InT (W : X.Opens) (a : Γ(w.Z, w.i ⁻¹ᵁ W)) : Prop :=
  ∃ t : Γ(Q, W), Killed w.J t ∧ w.Agrees W a t

variable {w}

lemma agrees_unique {W : X.Opens} {a : Γ(w.Z, w.i ⁻¹ᵁ W)} {t t' : Γ(Q, W)}
    (ht : Killed w.J t) (ht' : Killed w.J t') (h : w.Agrees W a t) (h' : w.Agrees W a t') :
    t = t' := by
  rw [← sub_eq_zero]
  refine w.tor W _ (ht.sub ht') fun V hV => ?_
  rw [map_sub, h V hV, h' V hV, sub_self]

lemma Agrees.res {W W' : X.Opens} (hW : W' ≤ W) {a : Γ(w.Z, w.i ⁻¹ᵁ W)} {t : Γ(Q, W)}
    (h : w.Agrees W a t) : w.Agrees W' (rres (w.pre_le hW) a) (Cech.res hW t) := by
  intro V hV
  have hV' : V.1 ≤ W ⊓ w.U.1 :=
    le_inf ((hV.trans inf_le_left).trans hW) (hV.trans inf_le_right)
  rw [Cech.res_res, rres_rres]
  exact h V hV'

lemma InT.res {W W' : X.Opens} (hW : W' ≤ W) {a : Γ(w.Z, w.i ⁻¹ᵁ W)} (h : w.InT W a) :
    w.InT W' (rres (w.pre_le hW) a) := by
  obtain ⟨t, ht, hag⟩ := h
  exact ⟨_, ht.res hW, hag.res hW⟩

lemma Agrees.add {W : X.Opens} {a b : Γ(w.Z, w.i ⁻¹ᵁ W)} {t t' : Γ(Q, W)}
    (h : w.Agrees W a t) (h' : w.Agrees W b t') : w.Agrees W (a + b) (t + t') := by
  intro V hV
  rw [map_add, map_add, w.mu_add, h V hV, h' V hV]

lemma InT.add {W : X.Opens} {a b : Γ(w.Z, w.i ⁻¹ᵁ W)} (ha : w.InT W a) (hb : w.InT W b) :
    w.InT W (a + b) := by
  obtain ⟨t, ht, hag⟩ := ha
  obtain ⟨t', ht', hag'⟩ := hb
  exact ⟨_, ht.add ht', hag.add hag'⟩

lemma agrees_zero (W : X.Opens) : w.Agrees W 0 0 := fun V hV => by
  rw [map_zero, map_zero, w.mu_zero]

lemma inT_zero (W : X.Opens) : w.InT W 0 := ⟨0, killed_zero W, agrees_zero W⟩

lemma Agrees.smul {W : X.Opens} (r : Γ(X, W)) {a : Γ(w.Z, w.i ⁻¹ᵁ W)} {t : Γ(Q, W)}
    (h : w.Agrees W a t) : w.Agrees W (w.i.app W r * a) (r • t) := by
  intro V hV
  rw [res_smul, map_mul, ← app_rres w.i (hV.trans inf_le_left) r, w.mu_mul, h V hV]

lemma InT.smul {W : X.Opens} (r : Γ(X, W)) {a : Γ(w.Z, w.i ⁻¹ᵁ W)} (h : w.InT W a) :
    w.InT W (w.i.app W r * a) := by
  obtain ⟨t, ht, hag⟩ := h
  exact ⟨_, ht.smul r, hag.smul r⟩

/-- Away from the closed set every function is admissible, with zero extension. -/
lemma inT_of_disjoint {W : X.Opens} (hW : ∀ y ∈ W, y ∉ w.Zc) (a : Γ(w.Z, w.i ⁻¹ᵁ W)) :
    w.InT W a := by
  refine ⟨0, killed_zero W, fun V hV => ?_⟩
  obtain ⟨r, hr⟩ := w.app_surjective V (rres (w.pre_le (hV.trans inf_le_left)) a)
  rw [map_zero, w.mu_eq V _ _ r hr]
  have hs : Cech.res (hV.trans inf_le_right) w.s = 0 :=
    (w.s_killed.res (hV.trans inf_le_right)).eq_zero_of_ideal_eq_top fun V' hV' =>
      w.ideal_eq_top fun y hy => hW y ((hV'.trans (hV.trans inf_le_left)) hy)
  rw [hs, smul_zero]

/-- Admissibility is local: the local extensions glue by uniqueness. -/
lemma inT_of_local {W : X.Opens} {a : Γ(w.Z, w.i ⁻¹ᵁ W)}
    (h : ∀ x ∈ W, ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧ w.InT W' (rres (w.pre_le hW') a)) :
    w.InT W a := by
  choose W' hW' hxW' hin using fun x : W => h x.1 x.2
  choose t ht hag using hin
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨Q.presheaf, Q.isSheaf⟩
  have hcomp : TopCat.Presheaf.IsCompatible F.1 W' t := by
    intro x y
    have h1 := (hag x).res (inf_le_left : W' x ⊓ W' y ≤ W' x)
    have h2 := (hag y).res (inf_le_right : W' x ⊓ W' y ≤ W' y)
    rw [rres_rres] at h1 h2
    exact agrees_unique ((ht x).res _) ((ht y).res _) h1 h2
  have hcov : W ≤ iSup W' := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxW' ⟨y, hy⟩⟩
  obtain ⟨t₀, ht₀, -⟩ :=
    TopCat.Sheaf.existsUnique_gluing' F W' W (fun x => homOfLE (hW' x)) hcov t hcomp
  have ht₀' : ∀ x, Cech.res (hW' x) t₀ = t x := ht₀
  refine ⟨t₀, killed_of_cover fun y hy => ⟨W' ⟨y, hy⟩, hW' _, hxW' _, by
    rw [ht₀']; exact ht _⟩, ?_⟩
  intro V hV
  apply eq_of_local
  intro y hy
  let yy : W := ⟨y, (hV.trans inf_le_left) hy⟩
  obtain ⟨V', hV'a, hyV', hV'le⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y ∈ V.1 ⊓ W' yy from ⟨hy, hxW' yy⟩)
  refine ⟨V', hV'le.trans inf_le_left, hyV', ?_⟩
  have hV'2 : V' ≤ W' yy ⊓ w.U.1 :=
    le_inf (hV'le.trans inf_le_right) ((hV'le.trans inf_le_left).trans (hV.trans inf_le_right))
  have key := hag yy ⟨V', hV'a⟩ hV'2
  rw [rres_rres] at key
  calc Cech.res (hV'le.trans inf_le_left) (Cech.res (hV.trans inf_le_left) t₀)
      = Cech.res (hV'2.trans inf_le_left) (Cech.res (hW' yy) t₀) := by
        rw [Cech.res_res, Cech.res_res]
    _ = _ := by rw [ht₀', key]
    _ = w.mu ⟨V', hV'a⟩ ((hV'le.trans inf_le_left).trans (hV.trans inf_le_right))
          (rres (w.pre_le (hV'le.trans inf_le_left))
            (rres (w.pre_le (hV.trans inf_le_left)) a)) := by
        rw [rres_rres]
    _ = _ := w.mu_res V ⟨V', hV'a⟩ (hV.trans inf_le_right) (hV'le.trans inf_le_left) _

/-- Admissibility over `W` is admissibility over every open with the same trace on the
closed subscheme or a smaller one. -/
lemma inT_iff_forall (W : X.Opens) (a : Γ(w.Z, w.i ⁻¹ᵁ W)) :
    w.InT W a ↔ ∀ (W' : X.Opens) (h : w.i ⁻¹ᵁ W' ≤ w.i ⁻¹ᵁ W), w.InT W' (rres h a) := by
  constructor
  · intro ha W' h
    apply inT_of_local
    intro x hx
    by_cases hxZ : x ∈ w.Zc
    · have hxW : x ∈ W := by
        have hx' : x ∈ Set.range w.i := by rw [w.range_i]; exact hxZ
        obtain ⟨z, rfl⟩ := hx'
        exact h hx
      refine ⟨W' ⊓ W, inf_le_left, ⟨hx, hxW⟩, ?_⟩
      have := ha.res (inf_le_right : W' ⊓ W ≤ W)
      rw [rres_rres]
      exact this
    · refine ⟨W' ⊓ w.Zc.compl, inf_le_left, ⟨hx, hxZ⟩, ?_⟩
      exact inT_of_disjoint (fun y (hy : y ∈ W' ⊓ w.Zc.compl) => hy.2) _
  · intro h
    have := h W le_rfl
    rwa [rres_self] at this

lemma inT_one_U : w.InT w.U.1 1 :=
  ⟨w.s, w.s_killed, fun V hV => by rw [map_one, w.mu_one]⟩

/-- Over a basic open of `U`, the annihilator of `s` lies in the ideal of the closed set. -/
lemma mem_J_of_smul_eq_zero [Q.IsQuasicoherent] (g : Γ(X, w.U.1)) (r : Γ(X, X.basicOpen g))
    (hr : r • Cech.res (X.basicOpen_le g) w.s = 0) :
    r ∈ w.J.ideal (X.affineBasicOpen g) := by
  have hloc := w.U.2.isLocalization_basicOpen g
  obtain ⟨⟨b, _, k, rfl⟩, hb⟩ := IsLocalization.surj (Submonoid.powers g) r
  have hb' : r * rres (X.basicOpen_le g) (g ^ k) = rres (X.basicOpen_le g) b := hb
  have h1 : Cech.res (X.basicOpen_le g) (b • w.s) = 0 := by
    rw [res_smul, ← hb', mul_comm, mul_smul, hr, smul_zero]
  obtain ⟨m, hm⟩ := (isLocalizingAt_of_isQuasicoherent w.U.2 Q).exists_pow_smul_eq_zero g _ h1
  have hgm : g ^ m * b ∈ w.p.asIdeal := (w.ann _).1 (by rw [mul_smul]; exact hm)
  have hunit : IsUnit (rres (X.basicOpen_le g) g) := X.toRingedSpace.isUnit_res_basicOpen g
  have hle : X.affineBasicOpen g ≤ w.U := X.basicOpen_le g
  rcases w.p.isPrime.mem_or_mem hgm with hg | hbp
  · have hg' : rres (X.basicOpen_le g) g ∈ w.J.ideal (X.affineBasicOpen g) :=
      Ideal.mem_comap.1 (w.J.ideal_le_comap_ideal hle
        (by rw [w.J_U]; exact w.p.isPrime.mem_of_pow_mem m hg))
    rw [Ideal.eq_top_of_isUnit_mem _ hg' hunit]
    trivial
  · have hb'' : rres (X.basicOpen_le g) b ∈ w.J.ideal (X.affineBasicOpen g) :=
      Ideal.mem_comap.1 (w.J.ideal_le_comap_ideal hle (by rw [w.J_U]; exact hbp))
    have hu : IsUnit (rres (X.basicOpen_le g) (g ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu⟩ := hu
    have : r = rres (X.basicOpen_le g) b * ↑u⁻¹ := by
      rw [← hb', ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hb''

end Witness

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules

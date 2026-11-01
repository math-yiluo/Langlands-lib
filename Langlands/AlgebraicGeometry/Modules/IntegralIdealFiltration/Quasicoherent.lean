import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Embedding

/-! # Quasi-coherence of the ideal sheaf of admissible functions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal Scheme.IdealSheafData

variable {X : Scheme.{u}} {Q : X.Modules}

set_option backward.defeqAttrib.useBackward true in
/-- Quasi-coherence can be checked on affine neighbourhoods of all points. -/
lemma isQuasicoherent_of_affine_nbhds {Y : Scheme.{u}} (M : Y.Modules) (V : Y → Y.Opens)
    (hV : ∀ y, IsAffineOpen (V y)) (hyV : ∀ y, y ∈ V y)
    (h : ∀ y, (M.restrict (hV y).fromSpec).IsQuasicoherent) : M.IsQuasicoherent := by
  have hcover : (_root_.Opens.grothendieckTopology Y).CoversTop V := by
    apply (_root_.Opens.coversTop_iff Y V).2
    apply top_le_iff.mp
    intro y _
    exact Opens.mem_iSup.2 ⟨y, hyV y⟩
  have (y : Y) : (M.restrict (V y).ι).IsQuasicoherent := by
    have := h y
    have hQ : ((M.restrict (hV y).fromSpec).restrict (hV y).isoSpec.hom).IsQuasicoherent :=
      inferInstance
    let e : (M.restrict (hV y).fromSpec).restrict (hV y).isoSpec.hom ≅
        M.restrict (V y).ι :=
      ((Scheme.Modules.restrictFunctorComp (hV y).isoSpec.hom (hV y).fromSpec).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by
          simp only [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc])).app M
    exact (SheafOfModules.isQuasicoherent (V y).toScheme.ringCatSheaf).prop_of_iso e hQ
  have (y : Y) : (M.over (V y)).IsQuasicoherent := isQuasicoherent_over_of_restrict M (V y)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M V hcover

/-- A section over an affine open which is killed by the ideal sheaf on a basic open becomes
killed after multiplication by a power of the function. -/
lemma exists_pow_smul_killed [IsNoetherian X] [Q.IsQuasicoherent] (J : X.IdealSheafData)
    (W : X.affineOpens) (g : Γ(X, W.1)) (t : Γ(Q, W.1))
    (ht : Killed J (Cech.res (X.basicOpen_le g) t)) : ∃ E : ℕ, Killed J (g ^ E • t) := by
  classical
  have := IsLocallyNoetherian.component_noetherian W
  have hL := isLocalizingAt_of_isQuasicoherent W.2 Q
  have hkill : ∀ c ∈ J.ideal W, ∃ e : ℕ, g ^ e • c • t = 0 := by
    intro c hc
    apply hL.exists_pow_smul_eq_zero g
    rw [res_smul]
    have := ht (X.affineBasicOpen g) le_rfl (rres (X.basicOpen_le g) c)
      (Ideal.mem_comap.1 (J.ideal_le_comap_ideal (X.affineBasicOpen_le g) hc))
    rw [Cech.res_res] at this
    exact this
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (J.ideal W) : (J.ideal W).FG)
  let e : Γ(X, W.1) → ℕ := fun c => if hc : c ∈ J.ideal W then (hkill c hc).choose else 0
  refine ⟨S.sup e, killed_of_affine W.2 fun c hc => ?_⟩
  let K : Ideal Γ(X, W.1) :=
    LinearMap.ker (LinearMap.toSpanSingleton Γ(X, W.1) Γ(Q, W.1) (g ^ S.sup e • t))
  have hSK : (S : Set Γ(X, W.1)) ⊆ K := by
    intro c hcS
    have hcJ : c ∈ J.ideal W := hS ▸ Ideal.subset_span hcS
    change c • g ^ S.sup e • t = 0
    have hle : e c ≤ S.sup e := Finset.le_sup hcS
    have hec : e c = (hkill c hcJ).choose := by simp [e, hcJ]
    have he : g ^ e c • c • t = 0 := by
      rw [hec]
      exact (hkill c hcJ).choose_spec
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, smul_comm c, smul_comm c, he, smul_zero]
  have : J.ideal W ≤ K := by
    rw [← hS]
    exact Ideal.span_le.2 hSK
  exact this hc

/-- On a quasi-compact open, finitely many affine charts give a uniform exponent. -/
lemma exists_uniform_pow [IsNoetherian X] (O W : X.Opens) (hOW : O ≤ W) (g : Γ(X, W))
    (δ : ∀ V : X.affineOpens, V.1 ≤ O → Γ(Q, V.1))
    (hres : ∀ (V V' : X.affineOpens) (h : V.1 ≤ O) (h' : V'.1 ≤ O) (hle : V'.1 ≤ V.1),
      Cech.res hle (δ V h) = δ V' h')
    (hpow : ∀ V h, ∃ r : ℕ, rres (h.trans hOW) g ^ r • δ V h = 0) :
    ∃ N : ℕ, ∀ V h, rres (h.trans hOW) g ^ N • δ V h = 0 := by
  classical
  have hcomp : IsCompact (O : Set X) := NoetherianSpace.isCompact _
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
    (fun V : {V : X.affineOpens // V.1 ≤ O} => (V.1.1 : Set X)) (fun V => V.1.1.isOpen) (by
      intro x hx
      obtain ⟨V, hVa, hxV, hVO⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
      exact Set.mem_iUnion.2 ⟨⟨⟨V, hVa⟩, hVO⟩, hxV⟩)
  choose r hr using fun V : {V : X.affineOpens // V.1 ≤ O} => hpow V.1 V.2
  refine ⟨t.sup r, fun V h => ?_⟩
  apply eq_zero_of_local
  intro y hy
  obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 (ht (h hy))
  obtain ⟨V'', hV''a, hyV'', hV''le⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y ∈ V.1 ⊓ j.1.1 from ⟨hy, hyj⟩)
  refine ⟨V'', hV''le.trans inf_le_left, hyV'', ?_⟩
  have h'' : V'' ≤ O := (hV''le.trans inf_le_left).trans h
  have hj' := congrArg (Cech.res (P := Q.presheaf) (hV''le.trans inf_le_right)) (hr j)
  rw [res_smul, map_pow, rres_rres, map_zero, hres j.1 ⟨V'', hV''a⟩ j.2 h''] at hj'
  rw [res_smul, map_pow, rres_rres, hres V ⟨V'', hV''a⟩ h h'',
    ← Nat.sub_add_cancel (Finset.le_sup hj : r j ≤ t.sup r), pow_add, mul_smul]
  exact (congrArg _ hj').trans (smul_zero _)

namespace Witness

variable (w : Witness Q)

/-- The function underlying a section of the ideal sheaf. -/
def ival {V : w.Z.Opens} (a : Γ(w.I, V)) : Γ(w.Z, V) :=
  (show ↥(w.idealSub.obj (op V)) from a).1

lemma ival_mem {V : w.Z.Opens} (a : Γ(w.I, V)) : w.Mem V (w.ival a) :=
  (show ↥(w.idealSub.obj (op V)) from a).2

lemma ival_injective {V : w.Z.Opens} : Function.Injective (w.ival (V := V)) := fun _ _ h =>
  Subtype.ext (p := fun x => x ∈ w.idealSub.obj (op V)) h

/-- A section of the ideal sheaf from an admissible function. -/
def imk {V : w.Z.Opens} (a : Γ(w.Z, V)) (ha : w.Mem V a) : Γ(w.I, V) :=
  (show ↥(w.idealSub.obj (op V)) from ⟨a, ha⟩)

lemma ival_imk {V : w.Z.Opens} (a : Γ(w.Z, V)) (ha : w.Mem V a) : w.ival (w.imk a ha) = a := rfl

lemma ival_res {V V' : w.Z.Opens} (h : V' ≤ V) (a : Γ(w.I, V)) :
    w.ival (Cech.res h a) = rres h (w.ival a) := rfl

lemma ival_smul {V : w.Z.Opens} (r : Γ(w.Z, V)) (a : Γ(w.I, V)) :
    w.ival (r • a) = r * w.ival a := rfl

lemma ival_zero {V : w.Z.Opens} : w.ival (0 : Γ(w.I, V)) = 0 := rfl

lemma isLocalizingAt_I_zero (W : X.affineOpens) (h : Γ(w.Z, w.i ⁻¹ᵁ W.1))
    (t : Γ(w.I, w.i ⁻¹ᵁ W.1)) (ht : Cech.res (w.Z.basicOpen_le h) t = 0) :
    ∃ n : ℕ, h ^ n • t = 0 := by
  have hV : IsAffineOpen (w.i ⁻¹ᵁ W.1) := W.2.preimage w.i
  have := hV.isLocalization_basicOpen h
  have hz : algebraMap Γ(w.Z, w.i ⁻¹ᵁ W.1) Γ(w.Z, w.Z.basicOpen h) (w.ival t) = 0 := by
    change rres (w.Z.basicOpen_le h) (w.ival t) = 0
    rw [← w.ival_res, ht]
    rfl
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers h) Γ(w.Z, w.Z.basicOpen h) (w.ival t)).1 hz
  exact ⟨n, w.ival_injective (by rw [w.ival_smul]; exact hn)⟩

lemma isLocalizingAt_I_res [IsNoetherian X] [Q.IsQuasicoherent] (W : X.affineOpens)
    (h : Γ(w.Z, w.i ⁻¹ᵁ W.1)) (s' : Γ(w.I, w.Z.basicOpen h)) :
    ∃ (n : ℕ) (t : Γ(w.I, w.i ⁻¹ᵁ W.1)),
      Cech.res (w.Z.basicOpen_le h) t = rres (w.Z.basicOpen_le h) h ^ n • s' := by
  classical
  have hVa : IsAffineOpen (w.i ⁻¹ᵁ W.1) := W.2.preimage w.i
  obtain ⟨g, rfl⟩ := w.app_surjective W h
  have hDe : w.i ⁻¹ᵁ X.basicOpen g = w.Z.basicOpen (w.i.app W.1 g) :=
    Scheme.preimage_basicOpen w.i g
  obtain ⟨t, htk, htag⟩ := w.ival_mem s' (X.basicOpen g) hDe.le
  -- localization of the functions on the closed subscheme
  have hloc := hVa.isLocalization_basicOpen (w.i.app W.1 g)
  obtain ⟨⟨a₀, _, n, rfl⟩, ha₀⟩ :=
    IsLocalization.surj (Submonoid.powers (w.i.app W.1 g)) (w.ival s')
  have ha₀' : w.ival s' * rres (w.Z.basicOpen_le _) (w.i.app W.1 g ^ n) =
      rres (w.Z.basicOpen_le (w.i.app W.1 g)) a₀ := ha₀
  -- localization of the sections of the module
  obtain ⟨m, t₁, ht₁⟩ := (isLocalizingAt_of_isQuasicoherent W.2 Q).exists_res_eq g t
  obtain ⟨E, hE⟩ := exists_pow_smul_killed w.J W g t₁ (by rw [ht₁]; exact htk.smul _)
  have ht₂ : Cech.res (X.basicOpen_le g) (g ^ E • t₁) =
      rres (X.basicOpen_le g) g ^ (E + m) • t := by
    rw [res_smul, ht₁, map_pow, ← mul_smul, ← pow_add]
  -- the defect over affine opens of `W ⊓ U`
  let δ : ∀ V : X.affineOpens, V.1 ≤ W.1 ⊓ w.U.1 → Γ(Q, V.1) := fun V hV =>
    Cech.res (hV.trans inf_le_left) (g ^ n • g ^ E • t₁) -
      w.mu V (hV.trans inf_le_right)
        (rres (w.pre_le (hV.trans inf_le_left)) (w.i.app W.1 g ^ (E + m) * a₀))
  have hres : ∀ (V V' : X.affineOpens) (h : V.1 ≤ W.1 ⊓ w.U.1) (h' : V'.1 ≤ W.1 ⊓ w.U.1)
      (hle : V'.1 ≤ V.1), Cech.res hle (δ V h) = δ V' h' := by
    intro V V' h h' hle
    simp only [δ, map_sub, Cech.res_res]
    rw [← w.mu_res V V' _ hle, rres_rres]
  have hpow : ∀ V h, ∃ r : ℕ, rres (h.trans inf_le_left) g ^ r • δ V h = 0 := by
    intro V hV
    have hVW : V.1 ≤ W.1 := hV.trans inf_le_left
    let γ : Γ(X, V.1) := rres hVW g
    let D' : X.affineOpens := X.affineBasicOpen (U := V) γ
    have hD'eq : X.basicOpen γ = V.1 ⊓ X.basicOpen g := basicOpen_rres hVW g
    have hD'D : D'.1 ≤ X.basicOpen g := fun x hx => by
      have : x ∈ V.1 ⊓ X.basicOpen g := hD'eq ▸ hx
      exact this.2
    have hD'V : D'.1 ≤ V.1 := X.basicOpen_le γ
    have hD'U : D'.1 ≤ w.U.1 := hD'V.trans (hV.trans inf_le_right)
    have hD'W : D'.1 ≤ W.1 := hD'V.trans hVW
    have hD'O : D'.1 ≤ W.1 ⊓ w.U.1 := le_inf hD'W hD'U
    apply (isLocalizingAt_of_isQuasicoherent V.2 Q).exists_pow_smul_eq_zero γ
    change Cech.res hD'V (δ V hV) = 0
    rw [hres V D' hV hD'O hD'V]
    simp only [δ]
    rw [sub_eq_zero]
    -- the left side
    have hL : Cech.res (hD'O.trans inf_le_left) (g ^ n • g ^ E • t₁) =
        rres hD'W g ^ n • rres hD'W g ^ (E + m) • Cech.res hD'D t := by
      rw [res_smul, map_pow, ← Cech.res_res hD'D (X.basicOpen_le g), ht₂, res_smul, map_pow,
        rres_rres]
    -- the right side
    have hA : rres (w.pre_le hD'W) a₀ =
        w.i.app D'.1 (rres hD'W g ^ n) * rres (w.pre_le hD'D) (rres hDe.le (w.ival s')) := by
      have e1 : rres (w.pre_le hD'W) a₀ = rres ((w.pre_le hD'D).trans hDe.le)
          (rres (w.Z.basicOpen_le (w.i.app W.1 g)) a₀) := by rw [rres_rres]
      rw [e1, ← ha₀', map_mul, mul_comm, rres_rres, rres_rres, map_pow, map_pow, app_rres]
    have hR : w.mu D' hD'U (rres (w.pre_le (hD'O.trans inf_le_left))
        (w.i.app W.1 g ^ (E + m) * a₀)) =
          rres hD'W g ^ (E + m) • rres hD'W g ^ n • Cech.res hD'D t := by
      rw [map_mul, map_pow, ← app_rres w.i hD'W g, ← map_pow, w.mu_mul, hA, w.mu_mul]
      congr 2
      exact (htag D' (le_inf hD'D hD'U)).symm
    rw [hL, hR, smul_comm]
  obtain ⟨N, hN⟩ := exists_uniform_pow (W.1 ⊓ w.U.1) W.1 inf_le_left g δ hres hpow
  -- the admissible function
  let b : Γ(w.Z, w.i ⁻¹ᵁ W.1) := w.i.app W.1 g ^ (N + (E + m)) * a₀
  have hb : w.InT W.1 b := by
    refine ⟨g ^ N • g ^ n • g ^ E • t₁, ((hE.smul _).smul _), fun V hV => ?_⟩
    have hNV := hN V hV
    simp only [δ, smul_sub, sub_eq_zero] at hNV
    rw [res_smul, map_pow, hNV, ← w.mu_mul]
    congr 1
    simp only [b, map_mul, map_pow, app_rres w.i, pow_add, mul_assoc]
  refine ⟨N + (E + m) + n, w.imk b ((w.mem_iff_inT W.1 b).2 hb), ?_⟩
  apply w.ival_injective
  rw [w.ival_res, w.ival_imk, w.ival_smul]
  simp only [b, map_mul, map_pow]
  rw [← ha₀', map_pow, pow_add (rres _ (w.i.app W.1 g)) (N + (E + m)) n]
  ring

/-- The ideal sheaf of admissible functions is quasi-coherent. -/
theorem isQuasicoherent_I [IsNoetherian X] [Q.IsQuasicoherent] : w.I.IsQuasicoherent := by
  choose W hWa hxW _ using fun z : w.Z =>
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show w.i z ∈ (⊤ : X.Opens) from trivial)
  refine isQuasicoherent_of_affine_nbhds w.I (fun z => w.i ⁻¹ᵁ W z)
    (fun z => (hWa z).preimage w.i) (fun z => hxW z) (fun z => ?_)
  exact isQuasicoherent_of_isLocalizingAt ((hWa z).preimage w.i)
    ⟨fun h s => w.isLocalizingAt_I_res ⟨W z, hWa z⟩ h s,
      fun h t ht => w.isLocalizingAt_I_zero ⟨W z, hWa z⟩ h t ht⟩

/-- The closed subscheme of a noetherian scheme is locally noetherian. -/
instance [IsNoetherian X] : IsLocallyNoetherian w.Z := by
  apply isLocallyNoetherian_of_affine_cover
    (S := fun W : X.affineOpens => (⟨w.i ⁻¹ᵁ W.1, W.2.preimage w.i⟩ : w.Z.affineOpens))
  · rw [eq_top_iff]
    intro z _
    obtain ⟨W, hWa, hzW, _⟩ :=
      (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show w.i z ∈ (⊤ : X.Opens) from trivial)
    exact Opens.mem_iSup.2 ⟨⟨W, hWa⟩, hzW⟩
  · intro W
    have := IsLocallyNoetherian.component_noetherian W
    exact isNoetherianRing_of_surjective _ _ (w.i.app W.1).hom (w.app_surjective W)

lemma hasFiniteAffineSections_structureModule :
    HasFiniteAffineSections (structureModule w.Z) := fun V =>
  Module.Finite.self Γ(w.Z, V.1)

instance mono_ι : Mono w.ι := inferInstanceAs (Mono (w.idealSub).ι)

theorem hasFiniteAffineSections_I [IsNoetherian X] : HasFiniteAffineSections w.I :=
  HasFiniteAffineSections.of_mono w.ι w.hasFiniteAffineSections_structureModule

theorem hasFiniteAffineSections_pushforward [IsNoetherian X] :
    HasFiniteAffineSections ((Scheme.Modules.pushforward w.i).obj w.I) := by
  intro W
  have hfin : Module.Finite Γ(w.Z, w.i ⁻¹ᵁ W.1) Γ(w.I, w.i ⁻¹ᵁ W.1) :=
    w.hasFiniteAffineSections_I ⟨w.i ⁻¹ᵁ W.1, W.2.preimage w.i⟩
  obtain ⟨S, hS⟩ := hfin.fg_top
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff]
  intro m hm0
  clear hm0
  have hm : m ∈ Submodule.span Γ(w.Z, w.i ⁻¹ᵁ W.1) (S : Set Γ(w.I, w.i ⁻¹ᵁ W.1)) := by
    rw [hS]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨r, rfl⟩ := w.app_surjective W c
    exact Submodule.smul_mem _ r hx

end Witness

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules

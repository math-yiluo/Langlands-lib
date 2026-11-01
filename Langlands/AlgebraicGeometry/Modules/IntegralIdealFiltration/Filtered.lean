import Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationStatement
import Langlands.AlgebraicGeometry.Modules.CoherentGraph

/-! # Filtrations by integral ideal pushforwards and the ascending chain argument -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.SchemeModule Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

variable {X : Scheme.{u}}

/-- `C` is isomorphic to the pushforward of a nonzero coherent ideal sheaf along a closed
immersion from an integral scheme. -/
def IsIdealPushforward (C : X.Modules) : Prop :=
  ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ IsIntegral Z ∧
    ∃ (I : Z.Modules) (ι : I ⟶ structureModule Z), Mono ι ∧ I.IsQuasicoherent ∧
      HasFiniteAffineSections I ∧ ¬ IsZero I ∧
      Nonempty (C ≅ (Scheme.Modules.pushforward i).obj I)

/-- Coherent modules admitting a filtration whose successive quotients are ideal pushforwards,
built from the top: the last step is a short exact sequence `F ⟶ M ⟶ C`. -/
inductive Filtered : X.Modules → Prop
  | zero {M : X.Modules} : IsZero M → M.IsQuasicoherent → HasFiniteAffineSections M →
      Filtered M
  | step {F M C : X.Modules} : Filtered F → M.IsQuasicoherent → HasFiniteAffineSections M →
      IsIdealPushforward C → ∀ (α : F ⟶ M) (β : M ⟶ C) (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact → Filtered M

/-- Short exactness transported along isomorphisms of the three terms. -/
lemma exists_shortExact_of_iso {A B C A' B' C' : X.Modules} (eA : A' ≅ A) (eB : B' ≅ B)
    (eC : C ≅ C') (α : A ⟶ B) (β : B ⟶ C) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) :
    ∃ (α' : A' ⟶ B') (β' : B' ⟶ C') (w' : α' ≫ β' = 0),
      (ShortComplex.mk α' β' w').ShortExact := by
  refine ⟨eA.hom ≫ α ≫ eB.inv, eB.hom ≫ β ≫ eC.hom, by simp [reassoc_of% w], ?_⟩
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk eA.symm eB.symm eC (by simp) (by simp)) hS

namespace Filtered

lemma isQuasicoherent {M : X.Modules} (h : Filtered M) : M.IsQuasicoherent := by
  cases h with
  | zero _ hq _ => exact hq
  | step _ hq _ _ _ _ _ _ => exact hq

lemma hasFiniteAffineSections {M : X.Modules} (h : Filtered M) : HasFiniteAffineSections M := by
  cases h with
  | zero _ _ hf => exact hf
  | step _ _ hf _ _ _ _ _ => exact hf

lemma of_iso {M N : X.Modules} (h : Filtered M) (e : M ≅ N) : Filtered N := by
  have hq : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e h.isQuasicoherent
  have hf : HasFiniteAffineSections N := h.hasFiniteAffineSections.of_iso e
  cases h with
  | zero h0 _ _ => exact .zero (h0.of_iso e.symm) hq hf
  | step hF _ _ hC α β w hS =>
    obtain ⟨α', β', w', hS'⟩ := exists_shortExact_of_iso (Iso.refl _) e.symm (Iso.refl _)
      α β w hS
    exact .step hF hq hf hC α' β' w' hS'

/-- A filtered module has a filtration in the form of the target statement. -/
theorem exists_chain {M : X.Modules} (hM : Filtered M) :
    ∃ (n : ℕ) (F : Fin (n + 1) → X.Modules),
      IsZero (F 0) ∧
      Nonempty (F (Fin.last n) ≅ M) ∧
      (∀ j, (F j).IsQuasicoherent ∧ HasFiniteAffineSections (F j)) ∧
      ∀ j : Fin n, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ (I : Z.Modules) (ι : I ⟶ structureModule Z),
          Mono ι ∧ I.IsQuasicoherent ∧ HasFiniteAffineSections I ∧
          ¬ IsZero I ∧
          ∃ (α : F j.castSucc ⟶ F j.succ)
            (β : F j.succ ⟶ (Scheme.Modules.pushforward i).obj I)
            (h : α ≫ β = 0),
              (ShortComplex.mk α β h).ShortExact := by
  induction hM with
  | zero h hq hf =>
    exact ⟨0, fun _ => _, h, ⟨Iso.refl _⟩, fun _ => ⟨hq, hf⟩, fun j => j.elim0⟩
  | @step F' M C hF hq hf hC α β w hS ih =>
    obtain ⟨n, F, h0, ⟨e⟩, hF', hsteps⟩ := ih
    obtain ⟨Z, i, hi, hZ, I, ι, hι, hIq, hIf, hI0, ⟨eC⟩⟩ := hC
    let G : Fin (n + 2) → X.Modules := Fin.snoc F M
    have hG : ∀ k : Fin (n + 1), G k.castSucc = F k := fun k => Fin.snoc_castSucc ..
    have hGl : G (Fin.last (n + 1)) = M := Fin.snoc_last ..
    refine ⟨n + 1, G, ?_, ?_, ?_, ?_⟩
    · have : (0 : Fin (n + 2)) = Fin.castSucc 0 := rfl
      rw [this, hG]
      exact h0
    · rw [hGl]
      exact ⟨Iso.refl _⟩
    · intro j
      induction j using Fin.lastCases with
      | last => rw [hGl]; exact ⟨hq, hf⟩
      | cast k => rw [hG]; exact hF' k
    · intro j
      induction j using Fin.lastCases with
      | last =>
        refine ⟨Z, i, hi, hZ, I, ι, hι, hIq, hIf, hI0, ?_⟩
        have h2 : G (Fin.last n).succ = M := by rw [Fin.succ_last, hGl]
        exact exists_shortExact_of_iso (eqToIso (hG _) ≪≫ e) (eqToIso h2) eC α β w hS
      | cast k =>
        obtain ⟨Z', i', hi', hZ', I', ι', hι', hIq', hIf', hI0', α', β', w', hS'⟩ := hsteps k
        refine ⟨Z', i', hi', hZ', I', ι', hι', hIq', hIf', hI0', ?_⟩
        have h2 : G k.castSucc.succ = F k.succ := by rw [Fin.succ_castSucc, hG]
        exact exists_shortExact_of_iso (eqToIso (hG _)) (eqToIso h2) (Iso.refl _) α' β' w' hS'

end Filtered

section Cover

/-- Vanishing on each member of a family of opens gives vanishing on their union. -/
lemma vanishesOn_iSup {ι : Type u} {M : X.Modules} (U : ι → X.Opens)
    (h : ∀ l, QuasicoherentLocal.VanishesOn M (U l)) :
    QuasicoherentLocal.VanishesOn M (⨆ l, U l) := by
  intro W hW s
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (F := F) (U := fun l => W ⊓ U l) W
    (fun l => homOfLE inf_le_left) ?_ s 0 (fun l => ?_)
  · intro x hx
    obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hW hx)
    exact Opens.mem_iSup.2 ⟨l, ⟨hx, hl⟩⟩
  · rw [map_zero]
    exact h l _ inf_le_right _

/-- A quasi-coherent module whose sections over an affine open vanish is zero on that open. -/
lemma vanishesOn_of_affine {M : X.Modules} [M.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (h : ∀ t : Γ(M, V), t = 0) : QuasicoherentLocal.VanishesOn M V := by
  have hL := QuasicoherentLocal.isLocalizingAt_of_isQuasicoherent hV M
  intro W hW s
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have key : ∀ x : W, ∃ (D : X.Opens) (_ : x.1 ∈ D) (hD : D ≤ W),
      Cech.res (P := M.presheaf) hD s = 0 := by
    intro x
    obtain ⟨g, hgW, hxg⟩ := hV.exists_basicOpen_le (V := W) ⟨x.1, x.2⟩ (hW x.2)
    refine ⟨X.basicOpen g, hxg, hgW, ?_⟩
    obtain ⟨n, t, ht⟩ := hL.exists_res_eq g (Cech.res hgW s)
    rw [h t, map_zero] at ht
    have hu : IsUnit (AffineVanishing.rres (X.basicOpen_le g) g ^ n) :=
      (X.toRingedSpace.isUnit_res_basicOpen g).pow n
    exact (hu.smul_eq_zero).1 ht.symm
  choose D hxD hD hDs using key
  refine TopCat.Sheaf.eq_of_locally_eq' (F := F) (U := D) W (fun x => homOfLE (hD x)) ?_ s 0
    (fun x => ?_)
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxD ⟨x, hx⟩⟩
  · rw [map_zero]
    exact hDs x

end Cover

section Chain

/-- The sections of a morphism of modules over an open, as a linear map. -/
def secHom {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (φ.val.app (op U)).hom

lemma secHom_apply {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    secHom φ U x = φ.app U x :=
  rfl

/-- A monomorphism of modules is injective on sections. -/
lemma injective_app {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (V : X.Opens) :
    Function.Injective (φ.app V) := by
  have : Mono ((PushforwardInjectiveAcyclic.toAbSheaf X).map φ) :=
    (PushforwardInjectiveAcyclic.toAbSheaf X).map_mono φ
  exact QuasicoherentLocal.injective_app_of_mono ((PushforwardInjectiveAcyclic.toAbSheaf X).map φ) V

/-- A noetherian scheme has a finite cover by affine opens. -/
lemma exists_finite_affine_cover [IsNoetherian X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      (∀ l, IsAffineOpen (U l)) ∧ ⨆ l, U l = ⊤ := by
  choose V hV hxV _ using fun x : X =>
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨t, inferInstance, fun l => V l.1, fun l => hV l.1, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

/-- The ascending chain argument: if every nonzero coherent module contains a nonzero ideal
pushforward, then every coherent module is filtered. -/
theorem filtered_of_core [IsNoetherian X]
    (core : ∀ Q : X.Modules, Q.IsQuasicoherent → HasFiniteAffineSections Q → ¬ IsZero Q →
      ∃ (C : X.Modules) (φ : C ⟶ Q), Mono φ ∧ IsIdealPushforward C ∧ C.IsQuasicoherent ∧
        HasFiniteAffineSections C ∧ ¬ IsZero C)
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M) : Filtered M := by
  classical
  obtain ⟨ι, _, U, hU, hcov⟩ := exists_finite_affine_cover (X := X)
  have hnoeth : ∀ l, IsNoetherian Γ(X, U l) Γ(M, U l) := fun l => by
    have := IsLocallyNoetherian.component_noetherian ⟨U l, hU l⟩
    have := hM ⟨U l, hU l⟩
    exact isNoetherian_of_isNoetherianRing_of_finite _ _
  let meas : ∀ {K : X.Modules}, (K ⟶ M) → ∀ l, (Submodule Γ(X, U l) Γ(M, U l))ᵒᵈ :=
    fun κ l => OrderDual.toDual (LinearMap.range (secHom κ (U l)))
  let S : Set (∀ l, (Submodule Γ(X, U l) Γ(M, U l))ᵒᵈ) :=
    {μ | ∃ (K : X.Modules) (κ : K ⟶ M), Mono κ ∧ Filtered K ∧ meas κ = μ}
  have hS : S.Nonempty :=
    ⟨_, kernel (𝟙 M), kernel.ι _, inferInstance,
      .zero (isZero_kernel_of_mono _) (QuasicoherentLocal.isQuasicoherent_kernel _)
        (hM.kernel _), rfl⟩
  have hwf : WellFounded ((· < ·) : (∀ l, (Submodule Γ(X, U l) Γ(M, U l))ᵒᵈ) → _ → Prop) :=
    wellFounded_lt
  obtain ⟨_, ⟨K₀, κ₀, hκ₀, hK₀, rfl⟩, hmin⟩ := hwf.has_min S hS
  have hq₀ := hK₀.isQuasicoherent
  have hepi : Epi κ₀ := by
    by_contra hne
    have hQ : ¬ IsZero (cokernel κ₀) := fun h => hne (Preadditive.epi_of_isZero_cokernel _ h)
    have hQq := QuasicoherentLocal.isQuasicoherent_cokernel κ₀
    obtain ⟨C, φ, hφ, hC, hCq, hCf, hC0⟩ :=
      core (cokernel κ₀) hQq (HasFiniteAffineSections.cokernel κ₀ hM) hQ
    let fst := pullback.fst (cokernel.π κ₀) φ
    let snd := pullback.snd (cokernel.π κ₀) φ
    let α : K₀ ⟶ pullback (cokernel.π κ₀) φ := pullback.lift κ₀ 0 (by simp)
    have hα : α ≫ fst = κ₀ := pullback.lift_fst _ _ _
    have hw : α ≫ snd = 0 := pullback.lift_snd _ _ _
    have hmono : Mono α := mono_of_mono_fac hα
    have hSE : (ShortComplex.mk α snd hw).ShortExact := by
      refine { exact := ?_, mono_f := hmono, epi_g := inferInstance }
      apply ShortComplex.exact_of_f_is_kernel
      refine KernelFork.IsLimit.ofι' α hw (fun {T} g hg => ?_)
      have hg' : (g ≫ fst) ≫ cokernel.π κ₀ = 0 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (g ≫ snd) ≫ φ = 0
        rw [hg, zero_comp]
      refine ⟨Abelian.monoLift κ₀ (g ≫ fst) hg', ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc]
        change _ ≫ α ≫ fst = g ≫ fst
        rw [hα, Abelian.monoLift_comp]
      · rw [Category.assoc]
        change _ ≫ α ≫ snd = g ≫ snd
        rw [hw, comp_zero]
        exact hg.symm
    have hK'q : (pullback (cokernel.π κ₀) φ).IsQuasicoherent :=
      QuasicoherentLocal.isQuasicoherent_pullback _ _
    have hK' : Filtered (pullback (cokernel.π κ₀) φ) :=
      .step hK₀ hK'q (HasFiniteAffineSections.pullback _ _ hM hCf) hC α snd hw hSE
    have hmem : meas fst ∈ S := ⟨_, fst, inferInstance, hK', rfl⟩
    have hle : meas fst ≤ meas κ₀ := by
      intro l
      change LinearMap.range (secHom κ₀ (U l)) ≤ LinearMap.range (secHom fst (U l))
      rintro _ ⟨k, rfl⟩
      refine ⟨α.app (U l) k, ?_⟩
      exact congrArg (fun f => Scheme.Modules.Hom.app f (U l) k) hα
    refine hmin _ hmem (lt_of_le_of_ne hle (fun heq => hC0 ?_))
    apply NoetherianVanishing.isZero_of_vanishesOn_top
    rw [← hcov]
    apply vanishesOn_iSup
    intro l
    apply vanishesOn_of_affine (hU l)
    intro c
    have hr : LinearMap.range (secHom fst (U l)) = LinearMap.range (secHom κ₀ (U l)) :=
      congrArg OrderDual.ofDual (congrFun heq l)
    obtain ⟨k', rfl⟩ := QuasicoherentLocal.surjective_app_of_epi snd (U l) (hU l) c
    obtain ⟨k₀, hk₀⟩ : fst.app (U l) k' ∈ LinearMap.range (secHom κ₀ (U l)) := by
      rw [← hr]
      exact ⟨k', rfl⟩
    have hk : k' = α.app (U l) k₀ := by
      apply injective_app fst (U l)
      change fst.app (U l) k' = (α ≫ fst).app (U l) k₀
      rw [hα]
      exact hk₀.symm
    rw [hk]
    change (α ≫ snd).app (U l) k₀ = 0
    rw [hw]
    rfl
  have := isIso_of_mono_of_epi κ₀
  exact hK₀.of_iso (asIso κ₀)

end Chain

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules

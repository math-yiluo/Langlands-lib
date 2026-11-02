import Langlands.AlgebraicGeometry.Modules.SerreVanishing.ChartOf
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Good
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic
import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth
import Langlands.Cohomology.RightDerivedSequence

/-! # Killing cohomology classes by powers of a section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.SchemeModule.SectionClearing
open Langlands.AlgebraicGeometry.Picard Langlands.Cohomology
open Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal
open Langlands.AlgebraicGeometry.Modules.AffineVanishing

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

section Biproduct

/-- Morphisms of modules commute with restriction of sections. -/
lemma app_cechRes {A B : X.Modules} (φ : A ⟶ B) {V W : X.Opens} (h : V ≤ W) (x : Γ(A, W)) :
    φ.app V (Cech.res h x) = Cech.res h (φ.app W x) :=
  Cech.map_res φ.mapPresheaf h x

variable {ι : Type*} [Fintype ι] (G : ι → X.Modules)

/-- A finite direct sum of modules with the localization property over `V` has it. -/
lemma isLocalizingAt_biproduct {V : X.Opens} (hG : ∀ i, IsLocalizingAt (G i) V) :
    IsLocalizingAt (⨁ G) V where
  exists_res_eq h x := by
    choose n t ht using fun i => (hG i).exists_res_eq h ((biproduct.π G i).app _ x)
    have hn : ∀ i, n i ≤ ∑ j, n j := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    obtain ⟨t', ht'⟩ := CechResolution.biproduct_exists_app G V
      (fun i => h ^ (∑ j, n j - n i) • t i)
    refine ⟨∑ j, n j, t', CechResolution.biproduct_ext_app G fun i => ?_⟩
    rw [app_cechRes, ht', res_smul, ht i, Scheme.Modules.Hom.app_smul, smul_smul, map_pow,
      ← pow_add, Nat.sub_add_cancel (hn i)]
  exists_pow_smul_eq_zero h t ht := by
    choose n hn using fun i => (hG i).exists_pow_smul_eq_zero h ((biproduct.π G i).app V t)
      (by rw [← app_cechRes, ht, map_zero])
    have hle : ∀ i, n i ≤ ∑ j, n j := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    refine ⟨∑ j, n j, CechResolution.biproduct_ext_app G fun i => ?_⟩
    rw [Scheme.Modules.Hom.app_smul, map_zero, ← Nat.sub_add_cancel (hle i), pow_add, mul_smul,
      hn i, smul_zero]

end Biproduct

section CechTerm

variable {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsSeparated f]

include f in
/-- Over a separated base, the sheaf of sections over an affine open of a quasi-coherent
module is quasi-coherent over every affine open. -/
lemma isAffineLocallyQuasicoherent_sheafOn (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) : IsAffineLocallyQuasicoherent (CechResolution.sheafOn M W) := by
  have hWa : IsAffine W.toScheme := hW
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  exact IsAffineLocallyQuasicoherent.pushforward W.ι (.of_isQuasicoherent _)

include f in
/-- Over a separated base, the terms of the Čech complex of a quasi-coherent module are
quasi-coherent. -/
lemma isQuasicoherent_cechTerm (𝒰 : X.OrderedAffineCover) (M : X.Modules) [M.IsQuasicoherent]
    (p : ℕ) : (CechResolution.cechTerm 𝒰 M p).IsQuasicoherent :=
  IsAffineLocallyQuasicoherent.isQuasicoherent fun V hV =>
    isQuasicoherent_of_isLocalizingAt hV (isLocalizingAt_biproduct _ fun s =>
      have := isAffineLocallyQuasicoherent_sheafOn f M
        (CechResolution.isAffineOpen_inter f 𝒰 s) V hV
      isLocalizingAt_of_isQuasicoherent hV _)

end CechTerm

/-- The short exact sequence `0 ⟶ Z ⟶ C⁰(𝒰, Z) ⟶ Q ⟶ 0` of the Čech augmentation. -/
abbrev cechCokernelSc (𝒰 : X.OrderedAffineCover) (Z : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (CechResolution.augmentation 𝒰 Z)
    (cokernel.π (CechResolution.augmentation 𝒰 Z)) (cokernel.condition _)

lemma cechCokernelSc_shortExact (𝒰 : X.OrderedAffineCover) (Z : X.Modules) :
    (cechCokernelSc 𝒰 Z).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (CechResolution.mono_augmentation (𝒰 := 𝒰) Z) (inferInstanceAs (Epi (cokernel.π _)))

section TwistSequence

variable (N : X.Modules) (s : GlobalSections N)

instance twistIter_preservesZeroMorphisms (k : ℕ) : (twistIter N k).PreservesZeroMorphisms := by
  induction k with
  | zero => exact inferInstanceAs (𝟭 X.Modules).PreservesZeroMorphisms
  | succ k ih => exact inferInstanceAs (twistIter N k ⋙ tensorBy N).PreservesZeroMorphisms

/-- Twisting by a line bundle preserves short exact sequences. -/
lemma shortExact_twistIter (hN : IsLocallyFreeRankOne N) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (k : ℕ) : (S.map (twistIter N k)).ShortExact := by
  induction k with
  | zero => exact hS
  | succ k ih => exact shortExact_tensorBy (S.map (twistIter N k)) ih N hN

/-- Multiplication by `s ^ k`, from a short complex to its `k`-th twist. -/
def twistPowHom (S : ShortComplex X.Modules) (k : ℕ) : S ⟶ S.map (twistIter N k) where
  τ₁ := (twistPow N s k).app S.X₁
  τ₂ := (twistPow N s k).app S.X₂
  τ₃ := (twistPow N s k).app S.X₃
  comm₁₂ := ((twistPow N s k).naturality S.f).symm
  comm₂₃ := ((twistPow N s k).naturality S.g).symm

end TwistSequence

section Killing

variable {R : CommRingCat.{u}} (f : X ⟶ Spec R) (N : X.Modules) (hN : IsLocallyFreeRankOne N)
  (s : GlobalSections N)

include hN in
/-- Dimension shifting: for a short exact sequence whose middle term has vanishing
cohomology in degree `n + 1`, a class in degree `n + 1` of the first term is killed by a
power of `s` once every class in degree `n` of the last term becomes, after a power of `s`,
the image of a class of the twisted middle term. -/
lemma exists_twistPow_eq_zero_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ)
    (h₂ : IsZero (((DerivedSections.relativeGlobalSections f).rightDerived (n + 1)).obj S.X₂))
    (h₃ : ∀ η : ((DerivedSections.relativeGlobalSections f).rightDerived n).obj S.X₃,
      ∃ (k : ℕ) (y : ((DerivedSections.relativeGlobalSections f).rightDerived n).obj
          ((twistIter N k).obj S.X₂)),
        (((DerivedSections.relativeGlobalSections f).rightDerived n).map
            ((twistIter N k).map S.g)).hom y =
          (((DerivedSections.relativeGlobalSections f).rightDerived n).map
            ((twistPow N s k).app S.X₃)).hom η)
    (ξ : ((DerivedSections.relativeGlobalSections f).rightDerived (n + 1)).obj S.X₁) :
    ∃ k : ℕ, (((DerivedSections.relativeGlobalSections f).rightDerived (n + 1)).map
      ((twistPow N s k).app S.X₁)).hom ξ = 0 := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  set Φ := DerivedSections.relativeGlobalSections f
  have hδ : Epi (DerivedPlus.rightDerivedδ Φ hS n (n + 1) rfl) :=
    DerivedPlus.epi_rightDerivedδ_of_isZero Φ hS n (n + 1) rfl h₂
  obtain ⟨η, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hδ ξ
  obtain ⟨k, y, hy⟩ := h₃ η
  have hk := shortExact_twistIter N hN S hS k
  refine ⟨k, ?_⟩
  have hnat := congrArg (fun g => g.hom η)
    (DerivedPlus.rightDerivedδ_naturality Φ hS hk (twistPowHom N s S k) n (n + 1) rfl)
  have hzero := congrArg (fun g => g.hom y)
    (DerivedPlus.rightDerived_map_comp_δ Φ hk n (n + 1) rfl)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hnat hzero
  change ((Φ.rightDerived (n + 1)).map (twistPowHom N s S k).τ₁).hom _ = 0
  rw [hnat]
  change (DerivedPlus.rightDerivedδ Φ hk n (n + 1) rfl).hom
    (((Φ.rightDerived n).map ((twistPow N s k).app S.X₃)).hom η) = 0
  rw [← hy]
  exact hzero

/-- Zeroth derived global sections act on elements as global sections. -/
lemma rightDerivedZero_map_apply {A B : X.Modules} (g : A ⟶ B)
    (x : ((DerivedSections.relativeGlobalSections f).rightDerived 0).obj A) :
    (((DerivedSections.relativeGlobalSections f).rightDerived 0).map g).hom x =
      ((DerivedSections.relativeGlobalSections f).rightDerivedZeroIsoSelf.inv.app B).hom
        (g.app ⊤
          (((DerivedSections.relativeGlobalSections f).rightDerivedZeroIsoSelf.hom.app A).hom
            x)) := by
  set e := (DerivedSections.relativeGlobalSections f).rightDerivedZeroIsoSelf
  have h1 := congrArg (fun k => k.hom ((e.hom.app A).hom x)) (e.inv.naturality g)
  have h2 := congrArg (fun k => k.hom x) (e.hom_inv_id_app A)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at h1 h2
  rw [h2] at h1
  exact h1.symm

include hN in
/-- A global section of the target of an epimorphism of quasi-coherent modules lifts after
multiplication by a power of `s`, when the trivialization locus of `s` is affine. -/
lemma exists_lift_twist [IsSeparated f] [CompactSpace X]
    (hU : IsAffineOpen (trivializationOpen N s)) {C Q : X.Modules} [C.IsQuasicoherent]
    [Q.IsQuasicoherent] (π : C ⟶ Q) [Epi π] (q : Γ(Q, ⊤)) :
    ∃ (m : ℕ) (a : Γ((twistIter N m).obj C, ⊤)),
      ((twistIter N m).map π).app ⊤ a = ((twistPow N s m).app Q).app ⊤ q := by
  obtain ⟨c, hc⟩ := surjective_app_of_epi π _ hU (Q.presheaf.map (homOfLE le_top).op q)
  refine exists_global_lift (N := fun m => (twistIter N m).obj C)
    (N' := fun m => (twistIter N m).obj Q) (μ := fun m => (stepNat N s m).app C)
    (μ' := fun m => (stepNat N s m).app Q) (fun m => (twistIter N m).map π)
    (fun m => (stepNat N s m).naturality π) π (trivializationOpen N s) (fun x => ?_)
    (fun V hV => isLocalizingAt_of_isQuasicoherent hV C)
    (fun V hV => isLocalizingAt_of_isQuasicoherent hV Q)
    (fun V hV => surjective_app_of_epi π V hV)
    (fun V V' hV hV' => CechResolution.isAffineOpen_inf f hV hV')
    (fun m => ((twistPow N s m).app Q).app ⊤ q) (fun m => rfl)
    (fun m => ((twistPow N s m).app C).app _ c) (fun m => rfl) (fun m => ?_)
  · obtain ⟨T, hxT, ⟨e⟩⟩ := hN x
    exact ⟨T, chartCoeff (chartMulOf T N e (sectionHom N s)), hxT,
      basicOpen_chartCoeff T ⟨N, hN⟩ s e, twistModChart N s T e C, twistModChart N s T e Q,
      fun m W hW d => twistModChart_naturality N s T e π m W hW d⟩
  · rw [← hom_app_map]
    erw [← hc]
    exact congrArg (fun g => g.app (trivializationOpen N s) c)
      ((twistPow N s m).naturality π).symm

include hN in
/-- Every class in positive degree of a quasi-coherent module is killed by a power of `s`,
by dimension shifting through the Čech sequence `0 ⟶ Z ⟶ C⁰(𝒰, Z) ⟶ Q ⟶ 0`. -/
theorem exists_twistPow_eq_zero [IsSeparated f] [CompactSpace X]
    (hU : IsAffineOpen (trivializationOpen N s)) (𝒰 : X.OrderedAffineCover) (p : ℕ) :
    ∀ (Z : X.Modules) [Z.IsQuasicoherent]
      (ξ : ((DerivedSections.relativeGlobalSections f).rightDerived (p + 1)).obj Z),
      ∃ k : ℕ, (((DerivedSections.relativeGlobalSections f).rightDerived (p + 1)).map
        ((twistPow N s k).app Z)).hom ξ = 0 := by
  induction p with
  | zero =>
    intro Z _ ξ
    have := isQuasicoherent_cechTerm f 𝒰 Z 0
    have := isQuasicoherent_cokernel (CechResolution.augmentation 𝒰 Z)
    refine exists_twistPow_eq_zero_of_shortExact f N hN s (cechCokernelSc 𝒰 Z)
      (cechCokernelSc_shortExact 𝒰 Z) 0
      (CechResolution.isZero_relativeCohomology_cechTerm f 𝒰 Z 0 0) (fun η => ?_) ξ
    set e := (DerivedSections.relativeGlobalSections f).rightDerivedZeroIsoSelf
    obtain ⟨m, a, ha⟩ := exists_lift_twist f N hN s hU
      (cokernel.π (CechResolution.augmentation 𝒰 Z)) ((e.hom.app _).hom η)
    refine ⟨m, (e.inv.app _).hom a, ?_⟩
    have h2 := congrArg (fun k => k.hom a) (e.inv_hom_id_app ((twistIter N m).obj
      (CechResolution.cechTerm 𝒰 Z 0)))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h2
    rw [rightDerivedZero_map_apply, rightDerivedZero_map_apply]
    erw [h2, ha]
    rfl
  | succ p ih =>
    intro Z _ ξ
    have := isQuasicoherent_cechTerm f 𝒰 Z 0
    have := isQuasicoherent_cokernel (CechResolution.augmentation 𝒰 Z)
    refine exists_twistPow_eq_zero_of_shortExact f N hN s (cechCokernelSc 𝒰 Z)
      (cechCokernelSc_shortExact 𝒰 Z) (p + 1)
      (CechResolution.isZero_relativeCohomology_cechTerm f 𝒰 Z 0 (p + 1)) (fun η => ?_) ξ
    obtain ⟨k, hk⟩ := ih (cokernel (CechResolution.augmentation 𝒰 Z)) η
    exact ⟨k, 0, by rw [map_zero, hk]⟩

end Killing

/-- Killing of cohomology classes by powers of a section (after Stacks 01XR). -/
theorem twistKilling : TwistKillingStatement.{u} := by
  intro K _ X f hf N hN s hU Z hZ p ξ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨𝒰, -⟩ := BiCech.exists_frameCover hN
  exact exists_twistPow_eq_zero f N hN s hU 𝒰 p Z ξ

end Langlands.AlgebraicGeometry.Modules.SerreVanishing

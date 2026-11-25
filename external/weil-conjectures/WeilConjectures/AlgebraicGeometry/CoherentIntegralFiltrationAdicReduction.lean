/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationExtension
import WeilConjectures.AlgebraicGeometry.CoherentSupportPowerIdealKills
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial

/-! # Reducing an integral-support filtration to generic residue-field modules

Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, ideal-power paragraph.
(blueprint: lem-weil-pbc-coherent-integral-filtration-adic-reduction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem generic_ideal_range {X : Scheme.{u}}
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk ξ) (X.presheaf.stalk ξ))
    (he : ∀ (U : X.Opens) (hx : ξ ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U ξ hx r) = X.presheaf.germ U ξ hx r) :
    LinearMap.range (((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
      (IdealSheafData.vanishingIdeal T).toModulesι) ≫ e.hom).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
  let J := IdealSheafData.vanishingIdeal T
  let fJ := (PresheafOfModules.toPresheaf _).map J.toModulesι.val
  have hJ := (IdealSheafData.reduced_induced_closed_subscheme X T).1
  ext a
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq J.toModules.val.presheaf m
    have hm : J.toModulesι.app U m ∈ J.idealOfOpens U := by
      change J.toModulesι.app U m ∈ (J.idealOfOpens U : Set Γ(X, U))
      rw [← J.range_toModulesι_app_eq_idealOfOpens U]
      exact Set.mem_range_self m
    change e.hom (((TopCat.Presheaf.stalkFunctor Ab ξ).map fJ)
      (TopCat.Presheaf.germ J.toModules.val.presheaf U ξ hx m)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ)
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply U ξ hx fJ m]
    change e.hom (TopCat.Presheaf.germ
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf U ξ hx (J.toModulesι.app U m)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ)
    rw [he, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hz := (hJ U _).mp hm ξ hx hξ.mem
    exact fun hu ↦ ((X.evaluation_eq_zero_iff_notMem_basicOpen ξ hx _).mp hz)
      ((X.mem_basicOpen _ ξ hx).mpr hu)
  · intro ha
    obtain ⟨U, hx, f, rfl⟩ := X.presheaf.exists_germ_eq a
    have hn : ξ ∉ X.basicOpen f := by
      rw [X.mem_basicOpen f ξ hx]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      exact ha
    have hf : f ∈ J.idealOfOpens U := by
      apply (hJ U f).mpr
      intro t ht hT
      apply (X.evaluation_eq_zero_iff_notMem_basicOpen t ht f).mpr
      intro hb
      exact hn ((hξ.specializes hT).mem_open (X.basicOpen f).isOpen hb)
    change f ∈ (J.idealOfOpens U : Set Γ(X, U)) at hf
    rw [← J.range_toModulesι_app_eq_idealOfOpens U] at hf
    obtain ⟨m, hm⟩ := hf
    refine ⟨TopCat.Presheaf.germ J.toModules.val.presheaf U ξ hx m, ?_⟩
    change e.hom (((TopCat.Presheaf.stalkFunctor Ab ξ).map fJ)
      (TopCat.Presheaf.germ J.toModules.val.presheaf U ξ hx m)) = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply U ξ hx fJ m]
    change e.hom (TopCat.Presheaf.germ
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf U ξ hx (J.toModulesι.app U m)) = _
    rw [hm, he]

private theorem stalk_injective {X : RingedSpace.{u}} {M N : RingedSpace.Modules X}
    (f : M ⟶ N) [Mono f] (x : X) :
    Function.Injective ((RingedSpace.moduleStalkFunctor X x).map f).hom := by
  have h := (RingedSpace.module_stalk_exact X f).1
  have hm : Mono ((RingedSpace.moduleStalkFunctor X x).map f) := by
    apply h
    intro U
    have : Mono f.val := (SheafOfModules.forget _).map_mono f
    exact (ModuleCat.mono_iff_injective (f.val.app (Opposite.op U))).mp inferInstance
  exact (ModuleCat.mono_iff_injective _).mp hm

open MonoidalCategory in
private theorem power_quasiCoherent {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ) :
    (idealSheafPower J.toModulesι n).1.IsQuasicoherent := by
  have := isQuasicoherent_toModules J
  induction n using Nat.twoStepInduction with
  | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | one => assumption
  | more n ih₁ ih₂ =>
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let M := (idealSheafPower J.toModulesι (n + 1)).1
    have : M.IsQuasicoherent := ih₂
    have : (J.toModules ⊗ M).IsQuasicoherent :=
      (quasiCoherent_tensor_product_affine_sections J.toModules M).1
    let f := MonoidalCategory.whiskerRight J.toModulesι M ≫
      (MonoidalCategory.leftUnitor M).hom
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage f)
      (quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
/-- For an irreducible closed support, it suffices to filter the coherent modules
supported there whose generic stalk is killed by the ambient maximal ideal.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, proof, third paragraph,
using Lemma 01Y9 and the reduced induced closed subscheme of Schemes Lemma 01J3.
(blueprint: lem-weil-pbc-coherent-integral-filtration-adic-reduction)

Proof: let J be the vanishing ideal of T with its reduced induced scheme structure.
Its zero locus is T and its stalk at ξ is the maximal ideal: a function vanishing at ξ
vanishes throughout T on its domain, since its zero locus is closed and ξ is generic.
By the support-power lemma some J^n kills F. Put A_t = J^t F for 0 <= t <= n, with
A_0 = F, and Q_t = A_t/A_{t+1}. Ideal products and powers are quasi-coherent on affine
opens, hence A_t and Q_t are coherent on the Noetherian scheme. Stalk exactness shows
Supp Q_t is contained in T. The equality of ideal-product stalks with products of
local modules shows J Q_t = 0, so the maximal ideal at ξ kills (Q_t)_ξ. Apply hgraded
to every Q_t. A_n is zero, so has the length-zero filtration. Descending induction
on t, using coherentIntegralFiltration_of_shortExact for A_{t+1} -> A_t -> Q_t,
gives a filtration of A_0 = F. If n = 0, F itself is zero and the same base case applies.
No assertion that all the Q_t have full support T is needed. -/
theorem coherentIntegralFiltration_of_generic_annihilated
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hgraded : ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X) →
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
        ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) →
      HasCoherentIntegralFiltration G) :
    HasCoherentIntegralFiltration F := by
  classical
  let J := IdealSheafData.vanishingIdeal T
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  have hsupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map J.toModulesι).hom} := by
    rw [← (quasi_coherent_ideal_zero_set_affine X J).2.2.2.2
      J.subscheme J.subschemeι (IdealSheafData.ker_subschemeι J)]
    rw [IdealSheafData.range_subschemeι, hSupp]
    simp [J]
  obtain ⟨n, hn⟩ := (coherent_support_power_ideal_kills X F hF J).mpr hsupp
  let P (t : ℕ) := idealModuleProduct (idealSheafPower J.toModulesι t).2 F
  let b (t : ℕ) := idealModuleProductι (idealSheafPower J.toModulesι t).2 F
  have hb (t : ℕ) : Mono (b t) := by
    dsimp [b, idealModuleProductι]
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    infer_instance
  have hP (t : ℕ) : RingedSpace.IsCoherent X.toRingedSpace (P t) := by
    have := power_quasiCoherent J t
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let M := (idealSheafPower J.toModulesι t).1
    have : (MonoidalCategoryStruct.tensorObj M F).IsQuasicoherent :=
      (quasiCoherent_tensor_product_affine_sections M F).1
    let f := MonoidalCategory.whiskerRight (idealSheafPower J.toModulesι t).2 F ≫
      (MonoidalCategory.leftUnitor F).hom
    have : (P t).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (Abelian.imageIsoImage f)
        (quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.1
    exact ((isCoherent_kernel_cokernel_biprod_and_submodule X).2
      F (P t) (b t) hF (hb t) inferInstance).1
  have hzero : IsIso (b 0) := by
    let : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
      SheafOfModules.monoidalCategory X.sheaf
    dsimp only [b, idealSheafPower, idealModuleProductι]
    have := epi_image_of_epi
      (MonoidalCategoryStruct.whiskerRight
        (𝟙 (SheafOfModules.unit X.ringCatSheaf : X.Modules)) F ≫
          (MonoidalCategoryStruct.leftUnitor F).hom)
    exact isIso_of_mono_of_epi _
  have factor (t : ℕ) : ∃ f : P (t + 1) ⟶ P t, f ≫ b t = b (t + 1) := by
    obtain ⟨f, hf⟩ := formalModuleQuotient_factor J (𝟙 F) (Nat.le_succ t)
    exact ⟨f, by simpa [b] using hf.symm⟩
  have good_of_zero (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
      (hz : IsZero G) : HasCoherentIntegralFiltration G := by
    apply hgraded G hG
    · intro x hx
      exact (hx (ModuleCat.isZero_iff_subsingleton.mp
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_isZero hz))).elim
    · intro a ha m
      have := ModuleCat.isZero_iff_subsingleton.mp
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_isZero hz)
      exact Subsingleton.elim _ _
  have hgood : ∀ t, t ≤ n → HasCoherentIntegralFiltration (P t) := by
    intro t ht
    induction ht using Nat.decreasingInduction with
    | self => exact good_of_zero (P n) (hP n) hn
    | @of_succ t ht ih =>
      obtain ⟨f, hf⟩ := factor t
      have : Mono (b t) := hb t
      have : Mono (b (t + 1)) := hb (t + 1)
      have : Mono (f ≫ b t) := hf.symm ▸ inferInstance
      have : Mono f := mono_of_mono f (b t)
      have hQ := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
        (P (t + 1)) (P t) (hP (t + 1)) (hP t)).1 f |>.2
      apply coherentIntegralFiltration_of_shortExact X
        (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
        ⟨ShortComplex.cokernelSequence_exact f⟩ (hP (t + 1)) (hP t) hQ ih
      apply hgraded (cokernel f) hQ
      · intro x hx
        by_contra hxT
        let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
        have hzF : Subsingleton (S.obj F) := by
          by_contra hnF
          exact hxT (hSupp ▸ hnF)
        have : Mono (b t) := hb t
        have : Subsingleton (S.obj F) := hzF
        have hinj := stalk_injective (b t) x
        have : Subsingleton (S.obj (P t)) := hinj.subsingleton
        have hepi := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x |>.1
        have hsurj := (ModuleCat.epi_iff_surjective (S.map (cokernel.π f))).mp hepi
        exact hx hsurj.subsingleton
      · let S := RingedSpace.moduleStalkFunctor X.toRingedSpace ξ
        obtain ⟨e, he, hi, hpi, hr, hq, hp⟩ := ideal_module_product_stalk J.toModulesι F ξ
        let I : Ideal (X.presheaf.stalk ξ) := LinearMap.range (S.map J.toModulesι ≫ e.hom).hom
        have hI : I = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
          generic_ideal_range T ξ hξ e he
        have hrange (k : ℕ) : LinearMap.range (S.map (b k)).hom =
            I ^ k • (⊤ : Submodule (X.presheaf.stalk ξ) (S.obj F)) := by
          cases k with
          | zero =>
            rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
            have : IsIso (b 0) := hzero
            exact LinearMap.range_eq_top.mpr
              ((ModuleCat.epi_iff_surjective (S.map (b 0))).mp inferInstance)
          | succ k => exact (hp (k + 1) (Nat.succ_pos k)).2.1
        intro a ha m
        have haI : a ∈ I := by rwa [hI]
        have hepi := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 ξ |>.1
        obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (S.map (cokernel.π f))).mp hepi m
        have hmem : (S.map (b t)).hom (a • y) ∈
            I ^ (t + 1) • (⊤ : Submodule (X.presheaf.stalk ξ) (S.obj F)) := by
          rw [(S.map (b t)).hom.map_smul, pow_succ', Submodule.mul_smul]
          apply Submodule.smul_mem_smul haI
          rw [← hrange t]
          exact LinearMap.mem_range_self _ y
        rw [← hrange (t + 1)] at hmem
        obtain ⟨z, hz⟩ := hmem
        have hfy : (S.map f).hom z = a • y := by
          apply stalk_injective (b t) ξ
          change (S.map f ≫ S.map (b t)).hom z = _
          rw [← S.map_comp, hf]
          exact hz
        change a • (S.map (cokernel.π f)).hom y = 0
        rw [← (S.map (cokernel.π f)).hom.map_smul, ← hfy]
        change (S.map f ≫ S.map (cokernel.π f)).hom z = 0
        rw [← S.map_comp, cokernel.condition, S.map_zero]
        rfl
  have : IsIso (b 0) := hzero
  have : Mono (b 0) := hb 0
  have hQ := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
    (P 0) F (hP 0) hF).1 (b 0) |>.2
  apply coherentIntegralFiltration_of_shortExact X
    (ShortComplex.mk (b 0) (cokernel.π (b 0)) (cokernel.condition (b 0)))
    ⟨ShortComplex.cokernelSequence_exact (b 0)⟩ (hP 0) hF hQ (hgood 0 (Nat.zero_le n))
  exact good_of_zero (cokernel (b 0)) hQ (isZero_cokernel_of_epi (b 0))

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel


/-! # Finite coherent adic chains

Source: Stacks Project, Tag 01YF, irreducible-support ideal-power paragraph,
using Tags 01Y9 and 01J3.
(blueprint: lem-pc-s3-coherent-support-adic-chain)
-/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem generic_ideal_range {X : Scheme.{u}}
    (J : X.IdealSheafData) (T : Set X) (ξ : X)
    (hJ : ∀ (U : X.Opens) (f : Γ(X, U)),
      f ∈ J.idealOfOpens U ↔
        ∀ (t : X) (ht : t ∈ U), t ∈ T → X.evaluation U t ht f = 0)
    (hmem : ξ ∈ T) (hspec : ∀ t ∈ T, Specializes ξ t)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk ξ) (X.presheaf.stalk ξ))
    (he : ∀ (U : X.Opens) (hx : ξ ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U ξ hx r) = X.presheaf.germ U ξ hx r) :
    LinearMap.range (((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
      J.toModulesι) ≫ e.hom).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
  let fJ := (PresheafOfModules.toPresheaf _).map J.toModulesι.val
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
    have hz := (hJ U _).mp hm ξ hx hmem
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
      exact hn ((hspec t hT).mem_open (X.basicOpen f).isOpen hb)
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

private theorem stalk_map_mono {X : RingedSpace.{u}} {M N : RingedSpace.Modules X}
    (f : M ⟶ N) [Mono f] (x : X) :
    Mono ((RingedSpace.moduleStalkFunctor X x).map f) := by
  apply (RingedSpace.module_stalk_exact X f).1
  intro U
  have : Mono f.val := (SheafOfModules.forget _).map_mono f
  exact (ModuleCat.mono_iff_injective (f.val.app (Opposite.op U))).mp inferInstance

open MonoidalCategory in
private theorem power_quasiCoherent {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) [J.IsQuasicoherent] (n : ℕ) :
    (idealSheafPower ι n).1.IsQuasicoherent := by
  induction n using Nat.twoStepInduction with
  | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | one => assumption
  | more n ih₁ ih₂ =>
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let M := (idealSheafPower ι (n + 1)).1
    have : M.IsQuasicoherent := ih₂
    have : (J ⊗ M).IsQuasicoherent :=
      (quasiCoherent_tensor_product_affine_sections J M).1
    let f := MonoidalCategory.whiskerRight ι M ≫
      (MonoidalCategory.leftUnitor M).hom
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage f)
      (quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.1

private theorem idealSheafPower_factor {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    {m n : ℕ} (h : n ≤ m) :
    ∃ j : (Scheme.idealSheafPower ι m).1 ⟶
        (Scheme.idealSheafPower ι n).1,
      j ≫ (Scheme.idealSheafPower ι n).2 =
        (Scheme.idealSheafPower ι m).2 := by
  have hs (k : ℕ) :
      ∃ j : (Scheme.idealSheafPower ι (k + 1)).1 ⟶
          (Scheme.idealSheafPower ι k).1,
        j ≫ (Scheme.idealSheafPower ι k).2 =
          (Scheme.idealSheafPower ι (k + 1)).2 := by
    cases k with
    | zero => exact ⟨ι, Category.comp_id _⟩
    | succ k => exact ⟨Scheme.idealModuleProductι ι
        (Scheme.idealSheafPower ι (k + 1)).1, rfl⟩
  induction h with
  | refl => exact ⟨𝟙 _, Category.id_comp _⟩
  | @step m h ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, hk⟩ := hs m
    exact ⟨k ≫ j, by rw [Category.assoc, hj, hk]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem product_power_factor {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    {F G : X.Modules} (f : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    ∃ k : Scheme.idealModuleProduct (Scheme.idealSheafPower ι m).2 F ⟶
        Scheme.idealModuleProduct (Scheme.idealSheafPower ι n).2 G,
      Scheme.idealModuleProductι (Scheme.idealSheafPower ι m).2 F ≫ f =
        k ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower ι n).2 G := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨j, hj⟩ := idealSheafPower_factor ι h
  let a := (Scheme.idealSheafPower ι m).2
  let b := (Scheme.idealSheafPower ι n).2
  have w : (MonoidalCategoryStruct.whiskerRight j F ≫
      MonoidalCategoryStruct.whiskerLeft (Scheme.idealSheafPower ι n).1 f) ≫
      (MonoidalCategoryStruct.whiskerRight b G ≫
        (MonoidalCategoryStruct.leftUnitor G).hom) =
      (MonoidalCategoryStruct.whiskerRight a F ≫
        (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f := by
    rw [Category.assoc, ← MonoidalCategory.whisker_exchange_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, hj,
      MonoidalCategory.whisker_exchange_assoc]
    exact (congrArg (((MonoidalCategoryStruct.whiskerRight a F)) ≫ ·)
      (MonoidalCategory.leftUnitor_naturality f)).trans (Category.assoc _ _ _).symm
  refine ⟨image.map (Arrow.homMk' _ _ w), ?_⟩
  exact (image.map_homMk'_ι w).symm
set_option backward.isDefEq.respectTransparency false in
/-- A finite coherent adic chain with generic-residue-field successive quotients.

Source: Stacks Project, Tag 01YF, irreducible-support ideal-power paragraph,
using Tags 01Y9 and 01J3 (https://stacks.math.columbia.edu/tag/01YF).
(blueprint: lem-pc-s3-coherent-support-adic-chain)

Proof: construct the vanishing ideal J of the reduced induced closed subscheme T.
The nilpotence lemma gives n with J^n F zero. Put P(t) equal to the image J^t F,
including the zero power. Its image inclusion b(0) is an isomorphism onto F.
Define the returned chain by Q(0) = F and Q(k+1) = P(k), with terminal index n+1.
The first quotient is the zero cokernel of b(0); later quotients are the cokernels
of the monic inclusions P(t+1) into P(t). No condition is required beyond n+1.
Quasi-coherence of ideal powers, products and cokernels, together with coherent
submodule and cokernel closure, gives coherence. Stalk exactness gives support
containment for the quotients. The stalk of J at the generic point is the maximal
ideal: a nonunit germ has a representative whose basic open omits the generic
point and therefore all its specializations in T. The stalk ranges of the products
are J_xi^t F_xi. Multiplying a lifted quotient germ by J_xi places its image in
J_xi^(t+1) F_xi; injectivity of b(t) identifies it with a lift from P(t+1), and the
cokernel projection kills it. At n = 0 the same construction has just the initial
isomorphism and its zero quotient.
This statement constructs only the chain; it asserts no integral filtration. -/
theorem coherent_support_adic_chain
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X)) :
    ∃ (n : ℕ) (P : ℕ → X.Modules), P 0 = F ∧ IsZero (P n) ∧
      (∀ k, k ≤ n → RingedSpace.IsCoherent X.toRingedSpace (P k)) ∧
      ∀ k, k < n → ∃ (G : X.Modules) (f : P (k + 1) ⟶ P k) (g : P k ⟶ G)
        (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X) ∧
        (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
          ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) := by
  classical
  let J := IdealSheafData.vanishingIdeal T
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  obtain ⟨n, hn⟩ := coherent_support_vanishingIdeal_nilpotence X T F hF
    (by rw [hSupp])
  have : J.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
      isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated J.subschemeι _
    exact isQuasicoherent_kernel J.toPushforwardSubscheme
  let P (t : ℕ) := idealModuleProduct (idealSheafPower J.toModulesι t).2 F
  let b (t : ℕ) := idealModuleProductι (idealSheafPower J.toModulesι t).2 F
  have hb (t : ℕ) : Mono (b t) := by
    dsimp [b, idealModuleProductι]
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    infer_instance
  have hP (t : ℕ) : RingedSpace.IsCoherent X.toRingedSpace (P t) := by
    have := power_quasiCoherent J.toModulesι t
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
    obtain ⟨f, hf⟩ := product_power_factor J.toModulesι (𝟙 F) (Nat.le_succ t)
    exact ⟨f, by simpa [b] using hf.symm⟩
  have step (t : ℕ) : ∃ (G : X.Modules) (f : P (t + 1) ⟶ P t)
      (g : P t ⟶ G) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      RingedSpace.IsCoherent X.toRingedSpace G ∧
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
        ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) := by
    obtain ⟨f, hf⟩ := factor t
    have : Mono (b t) := hb t
    have : Mono (b (t + 1)) := hb (t + 1)
    have : Mono (f ≫ b t) := hf.symm ▸ inferInstance
    have : Mono f := mono_of_mono f (b t)
    have hQ := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
      (P (t + 1)) (P t) (hP (t + 1)) (hP t)).1 f |>.2
    refine ⟨cokernel f, f, cokernel.π f, cokernel.condition f,
      ⟨ShortComplex.cokernelSequence_exact f⟩, hQ, ?_, ?_⟩
    · intro x hx
      by_contra hxT
      let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      have hzF : Subsingleton (S.obj F) := by
        by_contra hnF
        exact hxT (hSupp ▸ hnF)
      have : Mono (b t) := hb t
      have : Subsingleton (S.obj F) := hzF
      have hinj := (ModuleCat.mono_iff_injective _).mp (stalk_map_mono (b t) x)
      have : Subsingleton (S.obj (P t)) := hinj.subsingleton
      have hepi := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x |>.1
      have hsurj := (ModuleCat.epi_iff_surjective (S.map (cokernel.π f))).mp hepi
      exact hx hsurj.subsingleton
    · let S := RingedSpace.moduleStalkFunctor X.toRingedSpace ξ
      obtain ⟨e, he, hi, hpi, hr, hq, hp⟩ := ideal_module_product_stalk J.toModulesι F ξ
      let I : Ideal (X.presheaf.stalk ξ) := LinearMap.range (S.map J.toModulesι ≫ e.hom).hom
      have hI : I = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
        generic_ideal_range J (T : Set X) ξ
          (IdealSheafData.reduced_induced_closed_subscheme X T).1
          hξ.mem (fun t ht ↦ hξ.specializes ht) e he
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
        apply (ModuleCat.mono_iff_injective _).mp (stalk_map_mono (b t) ξ)
        change (S.map f ≫ S.map (b t)).hom z = _
        rw [← S.map_comp, hf]
        exact hz
      change a • (S.map (cokernel.π f)).hom y = 0
      rw [← (S.map (cokernel.π f)).hom.map_smul, ← hfy]
      change (S.map f ≫ S.map (cokernel.π f)).hom z = 0
      rw [← S.map_comp, cokernel.condition, S.map_zero]
      rfl
  let Q : ℕ → X.Modules
    | 0 => F
    | k + 1 => P k
  have : IsIso (b 0) := hzero
  have : Mono (b 0) := hb 0
  refine ⟨n + 1, Q, rfl, hn, ?_, ?_⟩
  · intro k hk
    cases k with
    | zero => exact hF
    | succ k => exact hP k
  · intro k hk
    cases k with
    | zero =>
      have hZ : IsZero (cokernel (b 0)) := isZero_cokernel_of_epi (b 0)
      have hC := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
        (P 0) F (hP 0) hF).1 (b 0) |>.2
      refine ⟨cokernel (b 0), b 0, cokernel.π (b 0), cokernel.condition (b 0),
        ⟨ShortComplex.cokernelSequence_exact (b 0)⟩, hC, ?_, ?_⟩
      · intro x hx
        exact (hx (ModuleCat.isZero_iff_subsingleton.mp
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_isZero hZ))).elim
      · intro a ha m
        have := ModuleCat.isZero_iff_subsingleton.mp
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_isZero hZ)
        exact Subsingleton.elim _ _
    | succ k => exact step k


end AlgebraicGeometry.Scheme.Modules

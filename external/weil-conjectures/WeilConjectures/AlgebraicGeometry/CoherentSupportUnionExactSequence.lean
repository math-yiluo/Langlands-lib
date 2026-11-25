/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentSupportPowerIdealKills
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine

/-! # Splitting the support of a coherent module into two closed pieces

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.1, Tag 01YD
(blueprint: lem-weil-pbc-coherent-support-union-exact-sequence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

open MonoidalCategory in
private theorem product_quasiCoherent {X : Scheme.{u}} {J : X.Modules}
    (j : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
    [J.IsQuasicoherent] [F.IsQuasicoherent] :
    (idealModuleProduct j F).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : (J ⊗ F).IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections J F).1
  let f := j ▷ F ≫ (λ_ F).hom
  have h := (quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.1
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage f) h

private theorem ideal_proper_locus (X : Scheme.{u}) (K : X.IdealSheafData) :
    {x : X | ¬ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} =
      (K.support : Set X) := by
  rw [← (quasi_coherent_ideal_zero_set_affine X K).2.2.2.2
    K.subscheme K.subschemeι (IdealSheafData.ker_subschemeι K)]
  exact IdealSheafData.range_subschemeι K

private theorem restrict_stalk_subsingleton {X : Scheme.{u}} (F : X.Modules)
    (V : X.Opens) (x : V.toScheme) :
    Subsingleton (((restrictFunctor V.ι).obj F).presheaf.stalk x) ↔
      Subsingleton (F.presheaf.stalk (V.ι x)) := by
  exact ((restrictStalkNatIso V.ι x).app F).addCommGroupIsoToAddEquiv.toEquiv
    |>.subsingleton_congr

private theorem power_quotient_stalk_zero {X : Scheme.{u}}
    (K : X.IdealSheafData) (F : X.Modules) (n : ℕ) (x : X)
    (hx : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom) :
    Subsingleton ((cokernel
      (idealModuleProductι (idealSheafPower K.toModulesι n).2 F)).presheaf.stalk x) := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨e, he, hinj, hpinj, hr, hq, hp⟩ := ideal_module_product_stalk K.toModulesι F x
  have htop : (LinearMap.range (S.map K.toModulesι ≫ e.hom).hom :
      Ideal (X.presheaf.stalk x)) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact e.toLinearEquiv.surjective.comp hx
  cases n with
  | zero =>
    obtain ⟨e', he', hi', hpi', hr', ⟨q, hq'⟩, hp'⟩ :=
      ideal_module_product_stalk (𝟙 (SheafOfModules.unit X.ringCatSheaf)) F x
    have ht : (LinearMap.range (S.map (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
        e'.hom).hom : Ideal (X.presheaf.stalk x)) = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      rw [S.map_id, Category.id_comp]
      exact e'.toLinearEquiv.surjective
    rw [ht, Submodule.top_smul] at q
    exact q.symm.injective.subsingleton
  | succ n =>
    obtain ⟨hrn, hrp, q, hq⟩ := hp (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    rw [htop, Ideal.top_pow, Submodule.top_smul] at q
    exact q.symm.injective.subsingleton

/-- A coherent module with support `Z ∪ Z'` has a coherent submodule supported on `Z'`
and coherent quotient supported on `Z`. The inclusion is a monomorphism `i`, and the
quotient is its canonical cokernel. Support uses the inline nonzero-stalk convention.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.1, Tag 01YD
(blueprint: lem-weil-pbc-coherent-support-union-exact-sequence).

Proof:
1. Take the actual vanishing ideal K of Z. The zero-set theorem identifies its proper
   stalk locus with its closed support, which is Z.
2. On V = X minus Z', restrict F and K. Restriction identifies stalks, so the support
   of F|V lies in the proper-stalk locus of K|V. The open V is Noetherian, hence
   coherent_support_power_ideal_kills supplies t with (K|V)^t (F|V) = 0.
3. The ideal-power restriction comparison gives (K^t F)|V = 0. Set G' = K^t F and
   i its image inclusion. The ideal powers and F are quasi-coherent; their tensor
   product and image are quasi-coherent. The coherent-submodule theorem gives
   coherence of G' and cokernel i. The abelian cokernel sequence is short exact.
4. At points of V the restriction-stalk comparison makes the stalk of G' zero,
   proving its support is contained in Z'. Outside Z, the stalk ideal K_x is the
   unit ideal. The ideal-power quotient stalk formula therefore identifies the
   quotient stalk with F_x/F_x = 0. For t = 0 use the identity inclusion of the
   structure sheaf and the product stalk formula directly. -/
theorem exists_coherent_submodule_of_support_union
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (Z Z' : Set X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = Z ∪ Z') :
    ∃ (G' : X.Modules) (i : G' ⟶ F),
      RingedSpace.IsCoherent X.toRingedSpace G' ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel i) ∧
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact ∧
      {x : X | ¬ Subsingleton (G'.presheaf.stalk x)} ⊆ Z' ∧
      {x : X | ¬ Subsingleton ((cokernel i).presheaf.stalk x)} ⊆ Z := by
  classical
  have : IsNoetherian X := ⟨⟩
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  let K : X.IdealSheafData := IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  have hK : (K.support : Set X) = Z := by simp [K]
  let V : X.Opens := ⟨Z'ᶜ, hZ'.isOpen_compl⟩
  let FV := (restrictFunctor V.ι).obj F
  let KV := K.comap V.ι
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (V : Set X))
  have : IsNoetherian V.toScheme := ⟨⟩
  have hFV : RingedSpace.IsCoherent V.toScheme.toRingedSpace FV :=
    (coherent_module_local_on_open_cover X F PUnit (fun _ ↦ ⊤) (by simp)).1 hF V
  have hsV : {x : V.toScheme | ¬ Subsingleton (FV.presheaf.stalk x)} ⊆
      {x : V.toScheme | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace x).map
          KV.toModulesι).hom} := by
    rw [ideal_proper_locus]
    intro x hx
    have hxF : ¬ Subsingleton (F.presheaf.stalk (V.ι x)) := by
      rwa [← restrict_stalk_subsingleton F V x]
    have hxZ : V.ι x ∈ Z := by
      have hm : V.ι x ∈ Z ∪ Z' := by rw [← hSupp]; exact hxF
      exact hm.resolve_right x.2
    change x ∈ (K.comap V.ι).support
    rw [IdealSheafData.support_comap]
    change V.ι x ∈ (K.support : Set X)
    rwa [hK]
  obtain ⟨t, ht⟩ := (coherent_support_power_ideal_kills V.toScheme FV hFV KV).mpr hsV
  have hz : IsZero ((restrictFunctor V.ι).obj
      (idealModuleProduct (idealSheafPower K.toModulesι t).2 F)) :=
    (idealPowerProduct_restrict_isZero_iff K F V t).mpr ht
  let G' := idealModuleProduct (idealSheafPower K.toModulesι t).2 F
  let i : G' ⟶ F := idealModuleProductι (idealSheafPower K.toModulesι t).2 F
  have hi : Mono i := by
    dsimp [i, idealModuleProductι]
    infer_instance
  have hpow : (idealSheafPower K.toModulesι t).1.IsQuasicoherent := by
    cases t with
    | zero =>
      change (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent
      exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    | succ n =>
      exact (ideal_times_quasiCoherent_affine_sections K F).2.2.1 _ (Nat.succ_pos n)
  have : G'.IsQuasicoherent := product_quasiCoherent _ F
  obtain ⟨hc, hq⟩ :=
    (isCoherent_kernel_cokernel_biprod_and_submodule X).2 F G' i hF hi inferInstance
  refine ⟨G', i, hc, hq, ⟨ShortComplex.cokernelSequence_exact i⟩, ?_, ?_⟩
  · intro x hx
    by_contra hxZ'
    let y : V.toScheme := ⟨x, hxZ'⟩
    have hs : Subsingleton (((restrictFunctor V.ι).obj G').presheaf.stalk y) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace y).map_isZero hz)
    exact hx ((restrict_stalk_subsingleton G' V y).mp hs)
  · intro x hx
    by_contra hxZ
    have hsurj : Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom := by
      by_contra hn
      have hm : x ∈ (K.support : Set X) := by
        rw [← ideal_proper_locus]; exact hn
      exact hxZ (hK ▸ hm)
    exact hx (power_quotient_stalk_zero K F t x hsurj)

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealPowerImage
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Restriction detects vanishing of ideal-power products

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YD;
Schemes, Lemma 01I8; Modules, Lemma 01CD
(blueprint: lem-weil-pbc-ideal-power-product-restriction-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem power_mono {X : Scheme.{u}} (K : X.IdealSheafData) (n : ℕ) :
    Mono (idealSheafPower K.toModulesι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [idealSheafPower]; infer_instance
  | one => simp only [idealSheafPower]; infer_instance
  | more n _ ih =>
    change Mono (idealModuleProductι K.toModulesι _ ≫ _)
    have : Mono (idealModuleProductι K.toModulesι (idealSheafPower K.toModulesι (n + 1)).1) := by
      dsimp [idealModuleProductι]
      infer_instance
    have := ih
    infer_instance

private theorem power_subobject {X : Scheme.{u}} (K : X.IdealSheafData) (n : ℕ) :
    let := power_mono K n
    Subobject.mk (idealSheafPower K.toModulesι n).2 = Subobject.mk (K ^ n).toModulesι := by
  let := power_mono K n
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hr (U : X.affineOpens) :
      Set.range ((idealSheafPower K.toModulesι n).2.app U.1) =
        Set.range ((K ^ n).toModulesι.app U.1) := by
    rw [IdealSheafData.range_toModulesι_app]
    cases n with
    | zero => simp [idealSheafPower]
    | succ n =>
      exact ((ideal_times_quasiCoherent_affine_sections K
        (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 _ (by omega)
  exact le_antisymm
    (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).le))
    (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).ge))

private theorem restrict_mono {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N) [Mono f] : Mono ((restrictFunctor j).map f) := by
  constructor
  intro Z a b hab
  apply hom_ext
  intro U
  have h : Function.Injective (f.app (j ''ᵁ U)) :=
    (ModuleCat.mono_iff_injective _).mp
      ((SheafOfModules.evaluation _ (Opposite.op (j ''ᵁ U))).map_mono f)
  ext s
  apply h
  exact congrArg (fun q ↦ q.app U s) hab

private theorem product_iso {X : Scheme.{u}} {J L : X.Modules}
    (i : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    (j : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : J ≅ L) (he : e.hom ≫ j = i) (F : X.Modules) :
    Nonempty (idealModuleProduct i F ≅ idealModuleProduct j F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  open MonoidalCategory in
  have hμ : i ▷ F ≫ (λ_ F).hom = e.hom ▷ F ≫ (j ▷ F ≫ (λ_ F).hom) := by
    rw [← Category.assoc, ← comp_whiskerRight, he]
  have hs : imageSubobject (i ▷ F ≫ (λ_ F).hom) =
      imageSubobject (j ▷ F ≫ (λ_ F).hom) := by
    calc
      _ = imageSubobject (e.hom ▷ F ≫ (j ▷ F ≫ (λ_ F).hom)) :=
        congrArg (fun f ↦ imageSubobject f) hμ
      _ = _ := imageSubobject_iso_comp _ _
  exact ⟨Subobject.isoOfMkEqMk _ _ hs⟩

private theorem comap_power {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (K : X.IdealSheafData) (n : ℕ) : (K ^ n).comap j = (K.comap j) ^ n := by
  apply IdealSheafData.ext
  funext U
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, IdealSheafData.ideal_pow,
    Pi.pow_apply]
  let e := (j.appIso U.1).commRingCatIsoToRingEquiv
  let I := K.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩
  change (I ^ n).comap e.symm = (I.comap e.symm) ^ n
  simp only [Ideal.comap_symm, Ideal.map_pow]

private theorem single_product_restrict {X : Scheme.{u}} (K : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens) :
    IsZero ((restrictFunctor V.ι).obj (idealModuleProduct K.toModulesι F)) ↔
      IsZero (idealModuleProduct (K.comap V.ι).toModulesι
        ((restrictFunctor V.ι).obj F)) := by
  let f := (restrictFunctor V.ι).map (idealModuleProductι K.toModulesι F)
  let g := idealModuleProductι (K.comap V.ι).toModulesι ((restrictFunctor V.ι).obj F)
  have hm : Mono (idealModuleProductι K.toModulesι F) := by
    dsimp [idealModuleProductι]
    infer_instance
  have : Mono f := restrict_mono V.ι _
  have : Mono g := by dsimp [g, idealModuleProductι]; infer_instance
  have hs := (ideal_times_quasiCoherent_affine_sections K F).2.2.2.2 V
  exact ((imageMonoIsoSource f).symm ≪≫
    Subobject.isoOfMkEqMk _ _ hs ≪≫ imageMonoIsoSource g).isZero_iff

/-- Restricting an ideal-power product to an open gives zero exactly when the
corresponding product of the restricted ideal and module is zero.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YD;
Schemes, Lemma 01I8; Modules, Lemma 01CD
(blueprint: lem-weil-pbc-ideal-power-product-restriction-zero).

Proof: Restriction computes sections on image opens, with scalars transported by
the structure-ring isomorphism. Kernels are computed on sections, so restriction
preserves kernels; its restriction/direct-image adjunction preserves cokernels.
Thus it is exact and preserves images. The tensor comparison and unit comparison
carry the multiplication map to restricted multiplication: on a pure tensor a ⊗ m
both composites give a • m. Pure tensors determine maps from tensor products.
The restricted inclusion of K is the inclusion of K.comap V.ι, as follows on each
affine open of V from the section formula for a quasi-coherent ideal. Induct on n:
for n = 0 the ideal is the structure sheaf with identity inclusion; for n = 1 use
the preceding identification; for n + 2 apply the product comparison to K and its
(n + 1)-st power and compose inclusions. Apply the same comparison once more to F.
This gives an isomorphism between the two objects below, which preserves and
reflects being a zero object. The argument also covers the empty open and F = 0. -/
theorem idealPowerProduct_restrict_isZero_iff {X : Scheme.{u}}
    (K : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (V : X.Opens) (n : ℕ) :
    IsZero ((restrictFunctor V.ι).obj
      (idealModuleProduct (idealSheafPower K.toModulesι n).2 F)) ↔
    IsZero (idealModuleProduct (idealSheafPower (K.comap V.ι).toModulesι n).2
      ((restrictFunctor V.ι).obj F)) := by
  have := power_mono K n
  let e := Subobject.isoOfMkEqMk _ _ (power_subobject K n)
  have he : e.hom ≫ (K ^ n).toModulesι = (idealSheafPower K.toModulesι n).2 := by
    simp [e]
  obtain ⟨p⟩ := product_iso _ _ e he F
  have := power_mono (K.comap V.ι) n
  let e' := Subobject.isoOfMkEqMk _ _ (power_subobject (K.comap V.ι) n)
  have he' : e'.hom ≫ ((K.comap V.ι) ^ n).toModulesι =
      (idealSheafPower (K.comap V.ι).toModulesι n).2 := by
    simp [e']
  obtain ⟨q⟩ := product_iso _ _ e' he' ((restrictFunctor V.ι).obj F)
  calc
    _ ↔ IsZero ((restrictFunctor V.ι).obj (idealModuleProduct (K ^ n).toModulesι F)) :=
      ((restrictFunctor V.ι).mapIso p).isZero_iff
    _ ↔ IsZero (idealModuleProduct ((K ^ n).comap V.ι).toModulesι
        ((restrictFunctor V.ι).obj F)) := single_product_restrict (K ^ n) F V
    _ ↔ IsZero (idealModuleProduct ((K.comap V.ι) ^ n).toModulesι
        ((restrictFunctor V.ι).obj F)) := by rw [comap_power]
    _ ↔ _ := q.isZero_iff.symm

end AlgebraicGeometry.Scheme.Modules

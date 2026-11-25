/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A scalar from the nth power of the base ideal kills every section of F/J^nF.
Source: Stacks Project, Tag 02OC, construction of the comparison maps;
Modules, Tags 01AG and 01CB, stalks of products and quotients.
(blueprint: lem-weil-pbc-formal-module-quotient-scalar-zero).

Proof: At a point z, let K be the image of J_z in O_{X,z}. The germ of the
image of a base scalar in I lies in K by the definition of the extended ideal.
The ring map from A to O_{X,z} therefore sends I^n into K^n. Exactness of
stalks and compatibility with tensor products identify (F/J^nF)_z with
F_z/(K^n F_z), on which every element of K^n acts by zero. The germ of the
claimed scalar multiple is consequently zero at every point of U. A section
of a sheaf with all germs zero is zero, giving the result. When n = 0,
J^0 = O_X and the multiplication image is F, so the quotient itself is zero.
The argument also covers I = 0, the unit ideal, F = 0 and the empty scheme;
it uses no coherence, properness or Noetherian assumption. -/
theorem formalModuleQuotient_scalar_zero {A : Type v} [CommRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (n : ℕ) (a : A) (ha : a ∈ I ^ n)
    (U : X.Opens) (t : (formalModuleQuotient J n F).val.obj (op U)) :
    (X.presheaf.map (homOfLE (le_top (a := U))).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom a) • t = 0 := by
  cases n with
  | zero =>
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have : Epi (Scheme.idealModuleProductι (𝟙 (SheafOfModules.unit X.ringCatSheaf)) F) := by
      dsimp only [Scheme.idealModuleProductι]
      change Epi (CategoryTheory.Limits.image.ι
        (MonoidalCategoryStruct.whiskerRight (𝟙 _) F ≫
          (MonoidalCategoryStruct.leftUnitor F).hom))
      exact CategoryTheory.Limits.epi_image_of_epi _
    have h := CategoryTheory.Limits.isZero_cokernel_of_epi
      (Scheme.idealModuleProductι (𝟙 (SheafOfModules.unit X.ringCatSheaf)) F)
    have hQ := ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (SheafOfModules.evaluation X.ringCatSheaf (op U)) h)
    exact hQ.elim _ _
  | succ n =>
    let Q := formalModuleQuotient J (n + 1) F
    apply TopCat.Presheaf.section_ext ⟨Q.val.presheaf, Q.isSheaf⟩ U _ _
    intro x hx
    rw [map_zero, PresheafOfModules.germ_smul (R := X.presheaf) Q.val]
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    obtain ⟨e, he, _, _, _, _, hp⟩ :=
      Scheme.ideal_module_product_stalk J.toModulesι F x
    let K : Ideal (X.presheaf.stalk x) :=
      LinearMap.range (S.map J.toModulesι ≫ e.hom).hom
    let g : A →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x (by trivial)).hom.comp
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)
    have hK : I ≤ K.comap g := by
      intro b hb
      let L := Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      have hL : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b ∈
          L.ideal ⟨⊤, isAffineOpen_top _⟩ := by
        simpa [L] using Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hb
      have hle : L ≤ J.map f := by
        rw [hJ]
        exact L.le_map_comap f
      have hk := (J.subschemeι ≫ f).ideal_ker_le ⟨⊤, isAffineOpen_top _⟩ (hle _ hL)
      have hz : J.subschemeι.app ⊤
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom b) = 0 := by
        simpa [Scheme.Hom.comp_appTop] using hk
      have hsrange :
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom b) ∈
            Set.range (J.toModulesι.app ⊤) := by
        rw [J.range_toModulesι_app_eq ⊤]
        exact hz
      obtain ⟨s, hs⟩ := hsrange
      refine ⟨TopCat.Presheaf.germ J.toModules.val.presheaf ⊤ x (by trivial) s, ?_⟩
      change e.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf _).map J.toModulesι.val)
        (TopCat.Presheaf.germ J.toModules.val.presheaf ⊤ x (by trivial) s)) = g b
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      change e.hom (TopCat.Presheaf.germ
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf ⊤ x (by trivial)
          (J.toModulesι.app ⊤ s)) = g b
      rw [he, hs]
      rfl
    have hpow : g a ∈ K ^ (n + 1) := by
      have hm := Ideal.mem_map_of_mem g ha
      have hle : (I ^ (n + 1)).map g ≤ K ^ (n + 1) := by
        rw [Ideal.map_pow]
        exact pow_le_pow_left' ((Ideal.map_le_iff_le_comap).mpr hK) _
      exact hle hm
    obtain ⟨_, _, φ, _⟩ := hp (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    let m : S.obj Q := TopCat.Presheaf.germ Q.val.presheaf U x hx t
    obtain ⟨z, hz⟩ := φ.surjective m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hzero : g a • m = 0 := by
      rw [← hz, ← φ.map_smul, ← Submodule.Quotient.mk_smul]
      have hmem : g a • y ∈ K ^ (n + 1) •
          (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) :=
        Submodule.smul_mem_smul hpow (Submodule.mem_top)
      rw [(Submodule.Quotient.mk_eq_zero _).mpr hmem, map_zero]
    simpa [g, m, Q, X.presheaf.germ_res_apply] using hzero

end AlgebraicGeometry

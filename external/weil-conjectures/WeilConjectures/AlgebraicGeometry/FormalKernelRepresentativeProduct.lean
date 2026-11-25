/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Products of formal kernel representatives

Source: Stacks Project, Lemma 087Z and Section 0EHN.
(blueprint: lem-weil-pbc-formal-kernel-representative-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem stalk_map_germ {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (p : X) (hp : p ∈ U)
    (z : M.val.obj (op U)) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace p).map f
      (TopCat.Presheaf.germ M.val.presheaf U p hp z) =
        TopCat.Presheaf.germ N.val.presheaf U p hp (f.val.app (op U) z) := by
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat p).map
    ((PresheafOfModules.toPresheaf _).map f.val) _ = _
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _

private theorem unit_stalk_iso_unique {X : Scheme.{u}} (p : X)
    (e e' : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    (he' : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e'.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r) : e = e' := by
  apply Iso.ext
  ext z
  obtain ⟨U, hp, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (SheafOfModules.unit X.ringCatSheaf).val.presheaf z
  exact (he U hp r).trans (he' U hp r).symm

private theorem stalk_power_data {X : Scheme.{u}} (I : X.IdealSheafData) (p : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    (M : X.Modules) (n : ℕ) (hn : 1 ≤ n) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
    let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    LinearMap.range (S.map (Scheme.idealSheafPower I.toModulesι n).2 ≫ e.hom).hom = J ^ n ∧
    LinearMap.range (S.map (Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι n).2 M)).hom = J ^ n • ⊤ ∧
    ∃ φ : (S.obj M ⧸ J ^ n • (⊤ : Submodule (X.presheaf.stalk p) (S.obj M))) ≃ₗ[
        X.presheaf.stalk p] S.obj (formalModuleQuotient I n M),
      ∀ z : S.obj M, φ (Submodule.Quotient.mk z) =
        (S.map (formalModuleQuotientπ I n M)).hom z := by
  obtain ⟨e', he', _, _, _, _, hpow⟩ := Scheme.ideal_module_product_stalk I.toModulesι M p
  have hh := unit_stalk_iso_unique p e' e he' he
  subst e'
  exact hpow n hn

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_reduction_ker {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (p : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    {k l : ℕ} (h : k ≤ l) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
    let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    LinearMap.ker (S.map (F.obj.map (homOfLE h).op)).hom =
      J ^ (k + 1) • (⊤ : Submodule (X.presheaf.stalk p) (S.obj (F.obj.obj (op l)))) := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
  let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
  have hz (r : ℕ) :
      J ^ (r + 1) • (⊤ : Submodule (X.presheaf.stalk p) (S.obj (F.obj.obj (op r)))) = ⊥ := by
    have hd := (stalk_power_data I p e he (F.obj.obj (op r)) (r + 1) (by omega)).2.1
    have hi : Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (r + 1)).2
        (F.obj.obj (op r)) = 0 := (F.property.2.1 r).eq_zero_of_src _
    rw [hi, S.map_zero, ModuleCat.hom_zero, LinearMap.range_zero] at hd
    exact hd.symm
  have hs (r : ℕ) :
      Function.Surjective (S.map (F.obj.map (homOfLE (Nat.le_succ r)).op)).hom ∧
      LinearMap.ker (S.map (F.obj.map (homOfLE (Nat.le_succ r)).op)).hom =
        J ^ (r + 1) • ⊤ := by
    obtain ⟨a, ha⟩ := F.property.2.2 r
    let M := F.obj.obj (op (r + 1))
    let q := formalModuleQuotientπ I (r + 1) M
    have hq : Epi (S.map q) :=
      (RingedSpace.module_stalk_exact X.toRingedSpace
        (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (r + 1)).2 M)).2.2.1 p |>.1
    have ht : S.map (F.obj.map (homOfLE (Nat.le_succ r)).op) = S.map q ≫ S.map a.hom := by
      rw [← ha, S.map_comp]
    constructor
    · rw [ht]
      exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    · obtain ⟨_, _, φ, hφ⟩ := stalk_power_data I p e he M (r + 1) (by omega)
      ext z
      change (S.map (F.obj.map (homOfLE (Nat.le_succ r)).op)).hom z = 0 ↔ _
      rw [ht]
      change (S.mapIso a).toLinearEquiv ((S.map q).hom z) = 0 ↔ _
      rw [(S.mapIso a).toLinearEquiv.map_eq_zero_iff, ← hφ z, φ.map_eq_zero_iff]
      exact Submodule.Quotient.mk_eq_zero _
  change LinearMap.ker (S.map (F.obj.map (homOfLE h).op)).hom = J ^ (k + 1) • ⊤
  induction h with
  | refl =>
    have hi : (homOfLE (show k ≤ k from le_rfl)).op = 𝟙 (op k) := Subsingleton.elim _ _
    rw [hi, F.obj.map_id, S.map_id]
    simpa using (hz k).symm
  | @step l h ih =>
    have hi : (homOfLE (show k ≤ l + 1 from Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ l)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [hi, F.obj.map_comp, S.map_comp, ModuleCat.hom_comp, LinearMap.ker_comp, ih,
      Submodule.comap_smul_top_of_surjective _ _ (hs l).1, (hs l).2]
    exact sup_of_le_left (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_power_range {X : Scheme.{u}} (I : X.IdealSheafData) (p : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    (n : ℕ) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
    let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    LinearMap.range (S.map (Scheme.idealSheafPower I.toModulesι n).2 ≫ e.hom).hom = J ^ n := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
  dsimp only
  cases n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    change LinearMap.range (S.map (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫ e.hom).hom = ⊤
    rw [S.map_id, Category.id_comp]
    exact LinearMap.range_eq_top.mpr e.toLinearEquiv.surjective
  | succ n => exact (stalk_power_data I p e he (SheafOfModules.unit X.ringCatSheaf)
      (n + 1) (by omega)).1

private theorem pow_smul_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) (m n : ℕ) {a : R} {t : M}
    (ha : a ∈ J ^ m) (ht : t ∈ J ^ n • (⊤ : Submodule R M)) :
    a • t ∈ J ^ (m + n) • (⊤ : Submodule R M) := by
  rw [pow_add, Submodule.mul_smul]
  exact Submodule.smul_mem_smul ha ht

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_kernel_representative {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (p : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    {n l : ℕ} (h : n ≤ l) (U : X.Opens) (hp : p ∈ U)
    (x : (formalKernelPiece F n).val.obj (op U))
    (t : (F.obj.obj (op l)).val.obj (op U))
    (ht : (F.obj.map (homOfLE h).op).val.app (op U) t =
      (formalKernelι F n).val.app (op U) x) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
    let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    TopCat.Presheaf.germ (F.obj.obj (op l)).val.presheaf U p hp t ∈
      J ^ n • (⊤ : Submodule (X.presheaf.stalk p) (S.obj (F.obj.obj (op l)))) := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
  let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
  change TopCat.Presheaf.germ (F.obj.obj (op l)).val.presheaf U p hp t ∈ J ^ n • ⊤
  cases n with
  | zero => simp
  | succ n =>
    rw [← stalk_reduction_ker I F p e he (show n ≤ l by omega)]
    change (S.map (F.obj.map (homOfLE (show n ≤ l by omega)).op))
      (TopCat.Presheaf.germ (F.obj.obj (op l)).val.presheaf U p hp t) = 0
    rw [stalk_map_germ]
    have hc : F.obj.map (homOfLE (show n ≤ l by omega)).op =
        F.obj.map (homOfLE h).op ≫ F.obj.map (homOfLE (Nat.le_succ n)).op := by
      rw [← F.obj.map_comp]
      congr 1
    have hz : (F.obj.map (homOfLE (Nat.le_succ n)).op).val.app (op U)
        ((formalKernelι F (n + 1)).val.app (op U) x) = 0 :=
      congrArg (fun f ↦ f.val.app (op U) x)
        (kernel.condition (F.obj.map (homOfLE (Nat.le_succ n)).op))
    have hzt : (F.obj.map (homOfLE (show n ≤ l by omega)).op).val.app (op U) t = 0 := by
      rw [hc]
      change (F.obj.map (homOfLE (Nat.le_succ n)).op).val.app (op U)
        ((F.obj.map (homOfLE h).op).val.app (op U) t) = 0
      rw [ht, hz]
    rw [hzt]
    exact map_zero _

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_coefficient_difference {X : Scheme.{u}} (I : X.IdealSheafData) (p : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    (n : ℕ) (U : X.Opens) (hp : p ∈ U)
    (a b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U))
    (hab : (formalAssociatedGradedπ I n).val.app (op U) b =
      (formalAssociatedGradedπ I n).val.app (op U) a) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
    let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    X.presheaf.germ U p hp
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) -
      X.presheaf.germ U p hp
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) a)) ∈
      J ^ (n + 1) := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
  let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
  let P := (Scheme.idealSheafPower I.toModulesι n).1
  let f := (S.map (Scheme.idealSheafPower I.toModulesι n).2 ≫ e.hom).hom
  let z : S.obj P := TopCat.Presheaf.germ P.val.presheaf U p hp b -
    TopCat.Presheaf.germ P.val.presheaf U p hp a
  have hz : z ∈ LinearMap.ker (S.map (formalAssociatedGradedπ I n)).hom := by
    change (S.map (formalAssociatedGradedπ I n)).hom z = 0
    dsimp only [z]
    rw [map_sub, stalk_map_germ, stalk_map_germ, hab, sub_self]
  have hr := ((RingedSpace.module_stalk_exact X.toRingedSpace
    (Scheme.idealModuleProductι I.toModulesι P)).2.2.1 p).2.moduleCat_range_eq_ker
  change LinearMap.range (S.map (Scheme.idealModuleProductι I.toModulesι P)).hom =
    LinearMap.ker (S.map (formalAssociatedGradedπ I n)).hom at hr
  have hpdata := (stalk_power_data I p e he P 1 (by omega)).2.1
  have hz' : z ∈ J • (⊤ : Submodule (X.presheaf.stalk p) (S.obj P)) := by
    change LinearMap.range (S.map (Scheme.idealModuleProductι I.toModulesι P)).hom =
      J ^ 1 • ⊤ at hpdata
    rw [pow_one] at hpdata
    rw [← hpdata, hr]
    exact hz
  have hh := Submodule.mem_map_of_mem (f := f) hz'
  rw [Submodule.map_smul'', Submodule.map_top, stalk_power_range I p e he n,
    Ideal.smul_eq_mul, ← pow_succ'] at hh
  have hf (c : P.val.obj (op U)) :
      f (TopCat.Presheaf.germ P.val.presheaf U p hp c) =
        X.presheaf.germ U p hp
          (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) c)) := by
    change e.hom ((S.map (Scheme.idealSheafPower I.toModulesι n).2)
      (TopCat.Presheaf.germ P.val.presheaf U p hp c)) = _
    rw [stalk_map_germ, he]
    rfl
  simpa only [z, map_sub, hf] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem formalKernel_lift_of_stalk_power {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (l : ℕ) (U : X.Opens)
    (z : (F.obj.obj (op l)).val.obj (op U))
    (hz : ∀ (p : X) (hp : p ∈ U)
      (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
          (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p)),
      (∀ (V : X.Opens) (hpV : p ∈ V) (r : Γ(X, V)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          V p hpV r) = X.presheaf.germ V p hpV r) →
      let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
      let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
      TopCat.Presheaf.germ (F.obj.obj (op l)).val.presheaf U p hp z ∈
        J ^ l • (⊤ : Submodule (X.presheaf.stalk p) (S.obj (F.obj.obj (op l))))) :
    ∃ y : (formalKernelPiece F l).val.obj (op U),
      (formalKernelι F l).val.app (op U) y = z := by
  cases l with
  | zero => exact ⟨z, rfl⟩
  | succ l =>
    let f := F.obj.map (homOfLE (Nat.le_succ l)).op
    have hh : f.val.app (op U) z = 0 := by
      apply TopCat.Presheaf.section_ext
        ⟨(F.obj.obj (op l)).val.presheaf, (F.obj.obj (op l)).isSheaf⟩ U
      intro p hp
      obtain ⟨e, he, _⟩ := Scheme.ideal_module_product_stalk I.toModulesι
        (F.obj.obj (op (l + 1))) p
      have ht := hz p hp e he
      dsimp only at ht
      rw [← stalk_reduction_ker I F p e he (Nat.le_succ l)] at ht
      change (RingedSpace.moduleStalkFunctor X.toRingedSpace p).map f
        (TopCat.Presheaf.germ (F.obj.obj (op (l + 1))).val.presheaf U p hp z) = 0 at ht
      rw [stalk_map_germ] at ht
      simpa only [map_zero] using ht
    have hh' := (Set.ext_iff.mp (Scheme.Modules.range_map_kernelι U f) z).mpr hh
    exact hh'

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_coefficient_mem {X : Scheme.{u}} (I : X.IdealSheafData) (p : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace p).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p))
    (he : ∀ (U : X.Opens) (hp : p ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U p hp r) = X.presheaf.germ U p hp r)
    (n : ℕ) (U : X.Opens) (hp : p ∈ U)
    (a : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
    let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    X.presheaf.germ U p hp
      (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) a)) ∈ J ^ n := by
  dsimp only
  rw [← stalk_power_range I p e he n]
  refine ⟨TopCat.Presheaf.germ
    (Scheme.idealSheafPower I.toModulesι n).1.val.presheaf U p hp a, ?_⟩
  change e.hom ((RingedSpace.moduleStalkFunctor X.toRingedSpace p).map
    (Scheme.idealSheafPower I.toModulesι n).2 _) = _
  rw [stalk_map_germ, he]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication of actual representatives lands in the successive kernel and is
independent of the representatives. This statement neither lifts arbitrary quotient
sections nor glues local products.
Source: Stacks Project, Lemma 087Z (lemma-finite-over-rees-algebra), associated graded
construction, and Section 0EHN, equation 0880.
(blueprint: lem-weil-pbc-formal-kernel-representative-product).

Proof: On each stalk the adjacent formal quotient identifications, iterated through
nested ideal powers, identify the reduction from level m+n+1 to level n+1 with
quotient by I^(n+1). For n>0, the reduction of t belongs to the adjacent kernel,
so t belongs to I^n times the top level; for n=0 this is automatic. The coefficient
belongs to I^m. Their product belongs to I^(m+n) times the top level, which is the
kernel of the adjacent reduction when m+n>0. The sectionwise kernel universal
property gives its preimage. When m+n=0 the inclusion is the identity.
If b and a have the same quotient class, b-a lies stalkwise in I^(m+1). If s and t
have the same reduction, s-t lies in I^(n+1) times the top level. Expand
b s - a t = (b-a)t + b(s-t). Both summands belong to I^(m+n+1) times that level,
which is zero by the formal annihilation condition. Equality on stalks gives the
section equality, including on the empty open by sheaf separation. This covers
zero degrees and the zero and unit ideals without additional hypotheses. -/
theorem formalKernel_representative_product {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U))
    (t : (F.obj.obj (op (m + n))).val.obj (op U))
    (ht : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
      (formalKernelι F n).val.app (op U) x) :
    (∃ y : (formalKernelPiece F (m + n)).val.obj (op U),
      (formalKernelι F (m + n)).val.app (op U) y =
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t) ∧
    (∀ (b : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
      (s : (F.obj.obj (op (m + n))).val.obj (op U)),
      (formalAssociatedGradedπ I m).val.app (op U) b =
        (formalAssociatedGradedπ I m).val.app (op U) a →
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) s =
        (formalKernelι F n).val.app (op U) x →
      (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) b)) • s =
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t) :=
  by
    constructor
    · apply formalKernel_lift_of_stalk_power I F (m + n) U
      intro p hp e he
      rw [PresheafOfModules.germ_smul (R := X.presheaf)]
      exact pow_smul_mem _ m n (stalk_coefficient_mem I p e he m U hp a)
        (stalk_kernel_representative I F p e he (Nat.le_add_left n m) U hp x t ht)
    · intro b s hb hs
      apply TopCat.Presheaf.section_ext
        ⟨(F.obj.obj (op (m + n))).val.presheaf, (F.obj.obj (op (m + n))).isSheaf⟩ U
      intro p hp
      obtain ⟨e, he, _⟩ := Scheme.ideal_module_product_stalk I.toModulesι
        (F.obj.obj (op (m + n))) p
      let S := RingedSpace.moduleStalkFunctor X.toRingedSpace p
      let J : Ideal (X.presheaf.stalk p) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
      let A := X.presheaf.germ U p hp
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a))
      let B := X.presheaf.germ U p hp
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) b))
      let T := TopCat.Presheaf.germ (F.obj.obj (op (m + n))).val.presheaf U p hp t
      let Z := TopCat.Presheaf.germ (F.obj.obj (op (m + n))).val.presheaf U p hp s
      have hB : B ∈ J ^ m := stalk_coefficient_mem I p e he m U hp b
      have hT : T ∈ J ^ n • (⊤ : Submodule (X.presheaf.stalk p)
          (S.obj (F.obj.obj (op (m + n))))) :=
        stalk_kernel_representative I F p e he (Nat.le_add_left n m) U hp x t ht
      have hD : B - A ∈ J ^ (m + 1) := stalk_coefficient_difference I p e he m U hp a b hb
      have hST : Z - T ∈ J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk p)
          (S.obj (F.obj.obj (op (m + n))))) := by
        rw [← stalk_reduction_ker I F p e he (Nat.le_add_left n m)]
        change (S.map (F.obj.map (homOfLE (Nat.le_add_left n m)).op)).hom (Z - T) = 0
        dsimp only [Z, T]
        rw [map_sub, stalk_map_germ, stalk_map_germ, hs, ht, sub_self]
      have hz : J ^ (m + n + 1) • (⊤ : Submodule (X.presheaf.stalk p)
          (S.obj (F.obj.obj (op (m + n))))) = ⊥ := by
        have hd := (stalk_power_data I p e he (F.obj.obj (op (m + n)))
          (m + n + 1) (by omega)).2.1
        have hi : Scheme.idealModuleProductι
            (Scheme.idealSheafPower I.toModulesι (m + n + 1)).2
            (F.obj.obj (op (m + n))) = 0 := (F.property.2.1 (m + n)).eq_zero_of_src _
        rw [hi, S.map_zero, ModuleCat.hom_zero, LinearMap.range_zero] at hd
        exact hd.symm
      have hdiff : B • Z - A • T ∈ J ^ (m + n + 1) •
          (⊤ : Submodule (X.presheaf.stalk p) (S.obj (F.obj.obj (op (m + n))))) := by
        have h₁ := pow_smul_mem J (m + 1) n hD hT
        have h₂ := pow_smul_mem J m (n + 1) hB hST
        have hcalc : B • Z - A • T = (B - A) • T + B • (Z - T) := by
          simp only [sub_smul, smul_sub]
          abel
        rw [hcalc]
        apply Submodule.add_mem
        · simpa only [show m + 1 + n = m + n + 1 by omega] using h₁
        · simpa only [Nat.add_assoc] using h₂
      rw [hz, Submodule.mem_bot] at hdiff
      rw [PresheafOfModules.germ_smul (R := X.presheaf),
        PresheafOfModules.germ_smul (R := X.presheaf)]
      exact sub_eq_zero.mp hdiff

end AlgebraicGeometry

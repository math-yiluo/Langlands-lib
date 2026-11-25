/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.IdealModuleMultiplicationStalkRange
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Annihilator calculus for sheaves of modules

Source: Stacks Project, proof of Lemma 0CYV, part (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A module sheaf is zero exactly when every module stalk is zero, by the faithful
forgetful functor and the zero-stalk criterion for abelian sheaves.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem zero_iff_stalks (X : Scheme.{u}) (F : X.Modules) :
    IsZero F ↔ ∀ x : X,
      IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) := by
  have hf : IsZero F ↔ IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) := by
    rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero,
      ← (SheafOfModules.toSheaf X.ringCatSheaf).map_id F, Functor.map_eq_zero_iff]
  rw [hf, TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  apply forall_congr'
  intro x
  let A := forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat
  change IsZero (A.obj ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) ↔ _
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero,
    ← A.map_id ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F),
    Functor.map_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity and the range formula for the product inclusion turn zero product
stalks into scalar annihilation by the image ideal.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem product_stalk_zero_iff {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    (F : X.Modules) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    IsZero (S.obj (idealModuleProduct ι F)) ↔
      ∀ r ∈ LinearMap.range (S.map ι ≫ e.hom).hom, ∀ m : S.obj F, r • m = 0 := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨e', he', hi, hpi, hr', rest⟩ := ideal_module_product_stalk ι F x
  have hr : LinearMap.range (S.map (idealModuleProductι ι F)).hom =
      (LinearMap.range (S.map ι ≫ e.hom).hom : Ideal (X.presheaf.stalk x)) • ⊤ := by
    exact ideal_multiplication_stalk_range ι F x e he
  have hz : IsZero (S.obj (idealModuleProduct ι F)) ↔
      LinearMap.range (S.map (idealModuleProductι ι F)).hom = ⊥ := by
    rw [ModuleCat.isZero_iff_subsingleton]
    constructor
    · intro h
      let _ := h
      apply le_antisymm _ bot_le
      rintro _ ⟨m, rfl⟩
      simp [Subsingleton.elim m 0]
    · intro h
      constructor
      intro a b
      apply hpi
      have ha : (S.map (idealModuleProductι ι F)).hom a = 0 := by
        have hm : (S.map (idealModuleProductι ι F)).hom a ∈
            LinearMap.range (S.map (idealModuleProductι ι F)).hom := ⟨a, rfl⟩
        simpa [h] using hm
      have hb : (S.map (idealModuleProductι ι F)).hom b = 0 := by
        have hm : (S.map (idealModuleProductι ι F)).hom b ∈
            LinearMap.range (S.map (idealModuleProductι ι F)).hom := ⟨b, rfl⟩
        simpa [h] using hm
      exact ha.trans hb.symm
  dsimp only
  rw [hz, hr, eq_bot_iff, Submodule.smul_le]
  simp only [Submodule.mem_top, Submodule.mem_bot, forall_true_left]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the middle term passes to module stalks.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem stalk_exact {X : Scheme.{u}} (T : ShortComplex X.Modules)
    (h : T.Exact) (x : X) :
    let := RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
    (T.map (RingedSpace.moduleStalkFunctor X.toRingedSpace x)).Exact := by
  exact ((RingedSpace.module_stalk_exact X.toRingedSpace T.f).2.2.2.2
    T.X₃ T.f T.g T.zero).mp h x

/-- A module-sheaf monomorphism gives injective module stalk maps.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem stalk_injective {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) [Mono a] (x : X) :
    Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map a).hom := by
  apply (ModuleCat.mono_iff_injective _).mp
  apply (RingedSpace.module_stalk_exact X.toRingedSpace a).1
  intro U
  have : Mono a.val := (SheafOfModules.forget _).map_mono a
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- A module-sheaf epimorphism gives surjective module stalk maps: apply stalk
exactness to the complex F -> G -> 0.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem stalk_surjective {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) [Epi a] (x : X) :
    Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map a).hom := by
  let := RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
  let T := ShortComplex.mk a (0 : G ⟶ G) (by simp)
  have hT : T.Exact := (T.exact_iff_epi rfl).mpr inferInstance
  have h := stalk_exact T hT x
  apply (ModuleCat.epi_iff_surjective _).mp
  exact h.epi_f (by simp [T])

set_option backward.isDefEq.respectTransparency false in
/-- The ideal inclusion on stalks sends an ideal-section germ to its ring germ.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem inclusion_stalk_germ {X : Scheme.{u}} (J : X.IdealSheafData) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(J.toModules, U)) :
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map J.toModulesι ≫ e.hom)
      (TopCat.Presheaf.germ J.toModules.val.presheaf U x hx a) =
        X.presheaf.germ U x hx (J.toModulesι.app U a) := by
  change e.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
    ((PresheafOfModules.toPresheaf _).map J.toModulesι.val)
      (TopCat.Presheaf.germ J.toModules.val.presheaf U x hx a)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact he U hx _

set_option backward.isDefEq.respectTransparency false in
/-- An element belongs to the stalk image ideal exactly when it is a germ of an
ideal section on an affine neighborhood.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem mem_stalkIdeal_iff {X : Scheme.{u}} (J : X.IdealSheafData) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) (r : X.presheaf.stalk x) :
    r ∈ LinearMap.range
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map J.toModulesι ≫ e.hom).hom ↔
      ∃ (U : X.affineOpens) (hx : x ∈ U.1) (a : Γ(X, U.1)),
        a ∈ J.ideal U ∧ X.presheaf.germ U.1 x hx a = r := by
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq J.toModules.val.presheaf m
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
    let m' := J.toModules.val.map (homOfLE hUV).op m
    refine ⟨⟨U, hU⟩, hxU, J.toModulesι.app U m', ?_, ?_⟩
    · change J.toModulesι.app U m' ∈ (J.ideal ⟨U, hU⟩ : Set Γ(X, U))
      rw [← J.range_toModulesι_app ⟨U, hU⟩]
      exact ⟨m', rfl⟩
    · rw [← inclusion_stalk_germ J x e he U hxU m']
      congr 1
      exact TopCat.Presheaf.germ_res_apply J.toModules.val.presheaf _ x hxU m
  · rintro ⟨U, hx, a, ha, rfl⟩
    change a ∈ (J.ideal U : Set Γ(X, U.1)) at ha
    rw [← J.range_toModulesι_app U] at ha
    obtain ⟨m, rfl⟩ := ha
    exact ⟨TopCat.Presheaf.germ J.toModules.val.presheaf U.1 x hx m,
      inclusion_stalk_germ J x e he U.1 hx m⟩

set_option backward.isDefEq.respectTransparency false in
/-- The stalk image ideal of J*K is the product of the stalk image ideals.
Use affine ideal sections, Ideal.map_mul, and a common affine neighborhood.
Source: Stacks Project, 01AG, 01CB, and the annihilator argument in 0CYV (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus). -/
private theorem stalkIdeal_mul {X : Scheme.{u}} (J K : X.IdealSheafData) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    (LinearMap.range (S.map (J * K).toModulesι ≫ e.hom).hom :
      Ideal (X.presheaf.stalk x)) =
      (LinearMap.range (S.map J.toModulesι ≫ e.hom).hom : Ideal _) *
        (LinearMap.range (S.map K.toModulesι ≫ e.hom).hom : Ideal _) := by
  dsimp only
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let I (L : X.IdealSheafData) : Ideal (X.presheaf.stalk x) :=
    LinearMap.range (S.map L.toModulesι ≫ e.hom).hom
  have hmap (L : X.IdealSheafData) (U : X.affineOpens) (hx : x ∈ U.1) :
      (L.ideal U).map (X.presheaf.germ U.1 x hx).hom ≤ I L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (mem_stalkIdeal_iff L x e he _).mpr ⟨U, hx, a, ha, rfl⟩
  change I (J * K) = I J * I K
  apply le_antisymm
  · intro r hr
    obtain ⟨U, hx, a, ha, rfl⟩ := (mem_stalkIdeal_iff (J * K) x e he r).mp hr
    have hm := Ideal.mem_map_of_mem (X.presheaf.germ U.1 x hx).hom ha
    change X.presheaf.germ U.1 x hx a ∈
      (J.ideal U * K.ideal U).map (X.presheaf.germ U.1 x hx).hom at hm
    rw [Ideal.map_mul] at hm
    exact (Ideal.mul_mono (hmap J U hx) (hmap K U hx)) hm
  · apply Ideal.mul_le.mpr
    intro r hr s hs
    obtain ⟨U, hxU, a, ha, rfl⟩ := (mem_stalkIdeal_iff J x e he r).mp hr
    obtain ⟨V, hxV, b, hb, rfl⟩ := (mem_stalkIdeal_iff K x e he s).mp hs
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (U.1 ⊓ V.1) from ⟨hxU, hxV⟩) (U.1 ⊓ V.1).isOpen
    have hWU : W ≤ U.1 := fun y hy ↦ (hWUV hy).1
    have hWV : W ≤ V.1 := fun y hy ↦ (hWUV hy).2
    let a' := X.presheaf.map (homOfLE hWU).op a
    let b' := X.presheaf.map (homOfLE hWV).op b
    have ha' : a' ∈ J.ideal ⟨W, hW⟩ := J.ideal_le_comap_ideal hWU ha
    have hb' : b' ∈ K.ideal ⟨W, hW⟩ := K.ideal_le_comap_ideal hWV hb
    apply (mem_stalkIdeal_iff (J * K) x e he _).mpr
    refine ⟨⟨W, hW⟩, hxW, a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
    rw [map_mul]
    congr 1
    · exact X.presheaf.germ_res_apply (homOfLE hWU) x hxW a
    · exact X.presheaf.germ_res_apply (homOfLE hWV) x hxW b

set_option backward.isDefEq.respectTransparency false in
/-- Annihilation passes to submodules and quotients. In an exact complex, the product
of ideals annihilating the outer terms annihilates the middle term.

Source: Stacks Project, proof of Lemma 0CYV, part (2), the annihilator argument.
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus).

Proof: The forgetful functor to abelian sheaves is faithful and preserves zero
morphisms. Hence a module sheaf is zero exactly when all its module stalks are zero.
The stalk image formula for ideal multiplication and injectivity of the product
inclusion identify vanishing with scalar annihilation by the image ideal in each stalk.
Monomorphisms induce injective stalk maps, so linearity transfers annihilation to the
source. Epimorphisms induce surjective stalk maps (apply stalk exactness to F -> G -> 0),
so lifting stalk elements transfers annihilation to the target.
For ideal multiplication, represent ideal stalk elements by ideal sections on affine
neighborhoods, using the range of toModulesι on affine sections. Mapping the product
ideal on an affine neighborhood into the stalk gives the forward inclusion. For the
reverse inclusion restrict representatives of both factors to a common affine
neighborhood and multiply there. Thus the stalk ideal of J*K is the product of the
stalk ideals of J and K.
Finally, for a middle stalk element b and k in K, linearity and annihilation of the
third stalk show that kb is in the kernel of the second map. Stalk exactness lifts kb
to a first-stalk element a. If j is in J, then jkb = f(ja) = 0. The universal property
of ideal multiplication puts J*K inside the annihilator of the middle stalk.
The argument includes zero ideals, zero modules, and the empty scheme, and requires
only exactness at the middle term. -/
theorem idealModuleProduct_exact_calculus (X : Scheme.{u}) :
    (∀ (J : X.IdealSheafData) {F G : X.Modules} (a : F ⟶ G) [Mono a],
      IsZero (idealModuleProduct J.toModulesι G) →
        IsZero (idealModuleProduct J.toModulesι F)) ∧
    (∀ (J : X.IdealSheafData) {F G : X.Modules} (a : F ⟶ G) [Epi a],
      IsZero (idealModuleProduct J.toModulesι F) →
        IsZero (idealModuleProduct J.toModulesι G)) ∧
    (∀ (J K : X.IdealSheafData) (T : ShortComplex X.Modules), T.Exact →
      IsZero (idealModuleProduct J.toModulesι T.X₁) →
      IsZero (idealModuleProduct K.toModulesι T.X₃) →
        IsZero (idealModuleProduct (J * K).toModulesι T.X₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro J F G a ha hG
    apply (zero_iff_stalks X _).mpr
    intro x
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let : S.PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
    obtain ⟨e, he, rest⟩ := ideal_module_product_stalk J.toModulesι G x
    have hkill := (product_stalk_zero_iff J.toModulesι G x e he).mp
      ((zero_iff_stalks X _).mp hG x)
    apply (product_stalk_zero_iff J.toModulesι F x e he).mpr
    intro r hr m
    apply stalk_injective a x
    change (S.map a).hom (r • m) = (S.map a).hom 0
    rw [map_smul, map_zero]
    exact hkill r hr _
  · intro J F G a ha hF
    apply (zero_iff_stalks X _).mpr
    intro x
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let : S.PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
    obtain ⟨e, he, rest⟩ := ideal_module_product_stalk J.toModulesι F x
    have hkill := (product_stalk_zero_iff J.toModulesι F x e he).mp
      ((zero_iff_stalks X _).mp hF x)
    apply (product_stalk_zero_iff J.toModulesι G x e he).mpr
    intro r hr m
    obtain ⟨n, rfl⟩ := stalk_surjective a x m
    rw [← map_smul]
    rw [hkill r hr n, map_zero]
  · intro J K T hT hA hC
    apply (zero_iff_stalks X _).mpr
    intro x
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let : S.PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
    obtain ⟨e, he, rest⟩ := ideal_module_product_stalk J.toModulesι T.X₁ x
    have hJ := (product_stalk_zero_iff J.toModulesι T.X₁ x e he).mp
      ((zero_iff_stalks X _).mp hA x)
    have hK := (product_stalk_zero_iff K.toModulesι T.X₃ x e he).mp
      ((zero_iff_stalks X _).mp hC x)
    have hex := (T.map S).moduleCat_exact_iff.mp (stalk_exact T hT x)
    apply (product_stalk_zero_iff (J * K).toModulesι T.X₂ x e he).mpr
    rw [stalkIdeal_mul J K x e he]
    let IJ : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map J.toModulesι ≫ e.hom).hom
    let IK : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map K.toModulesι ≫ e.hom).hom
    have hann : IJ * IK ≤ (⊤ : Submodule (X.presheaf.stalk x) (S.obj T.X₂)).annihilator := by
      apply Ideal.mul_le.mpr
      intro j hj k hk
      apply Submodule.mem_annihilator.mpr
      intro b hb
      have hz : (S.map T.g).hom (k • b) = 0 := by
        rw [map_smul]
        exact hK k hk _
      obtain ⟨a, hfa⟩ := hex (k • b) hz
      change (S.map T.f).hom a = k • b at hfa
      rw [mul_smul, ← hfa, ← map_smul, hJ j hj a, map_zero]
    intro r hr m
    exact Submodule.mem_annihilator.mp (hann hr) m Submodule.mem_top

end AlgebraicGeometry.Scheme

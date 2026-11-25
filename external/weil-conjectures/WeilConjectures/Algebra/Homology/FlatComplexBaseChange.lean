/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Algebra.Homology.FlatComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.RingTheory.Flat.Basic

/-!
# Base change of quasi-isomorphisms between complexes of flat modules

For an `A`-algebra `B`, extension of scalars `M ↦ B ⊗[A] M` is an additive functor
`ModuleCat.baseChange A B : ModuleCat A ⥤ ModuleCat B`. It sends a quasi-isomorphism
`φ : K ⟶ L` between complexes of flat modules to a quasi-isomorphism, provided the cycles of the
mapping cone of `φ` are flat in high degrees, for instance when `K` and `L` are bounded above
(`CochainComplex.quasiIso_map_baseChange`): the mapping cone is an acyclic complex of flat modules
whose cycles are all flat, so it stays acyclic after base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **Extension of scalars** `M ↦ B ⊗[A] M` along an algebra map `A → B`. Unlike
`ModuleCat.extendScalars`, the tensor product is formed for the `A`-module structure of `B`
coming from the algebra structure. -/
@[simps]
noncomputable def baseChange : ModuleCat.{u} A ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (B ⊗[A] M)
  map f := ModuleCat.ofHom (f.hom.baseChange B)
  map_id M := by
    ext : 1
    exact LinearMap.baseChange_id
  map_comp f g := by
    ext : 1
    exact LinearMap.baseChange_comp _ _

instance : (baseChange A B).Additive where
  map_add := by
    intros
    ext : 1
    exact LinearMap.baseChange_add _ _

end ModuleCat

namespace CochainComplex

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- The base change `B ⊗[A] C` of a complex `C` of `A`-modules is exact in degree `k + 1` if and
only if the tensored differentials are exact. -/
lemma exactAt_baseChange_iff (C : CochainComplex (ModuleCat.{u} A) ℤ) (k : ℤ) :
    (((ModuleCat.baseChange A B).mapHomologicalComplex _).obj C).ExactAt (k + 1) ↔
      Function.Exact ((C.d k (k + 1)).hom.lTensor B)
        ((C.d (k + 1) (k + 1 + 1)).hom.lTensor B) := by
  rw [exactAt_iff_exact]
  change Function.Exact ((C.d k (k + 1)).hom.baseChange B)
    ((C.d (k + 1) (k + 1 + 1)).hom.baseChange B) ↔ _
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]

variable {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L)

/-- The terms of the mapping cone of a morphism between complexes of flat modules are flat. -/
lemma flat_mappingCone_X (hK : ∀ k, Module.Flat A (K.X k)) (hL : ∀ k, Module.Flat A (L.X k))
    (k : ℤ) : Module.Flat A ((mappingCone φ).X k) := by
  have := hK (k + 1)
  have := hL k
  let e : (mappingCone φ).X k ≃ₗ[A] K.X (k + 1) × L.X k :=
    { toFun x := (((mappingCone.fst φ).1.v k (k + 1) rfl).hom x,
        ((mappingCone.snd φ).v k k (add_zero k)).hom x)
      map_add' x y := by simp
      map_smul' a x := by simp
      invFun y := ((mappingCone.inl φ).v (k + 1) k (by lia)).hom y.1 +
        ((mappingCone.inr φ).f k).hom y.2
      left_inv x := by
        have := congrArg (fun f ↦ f.hom x) (mappingCone.id_X φ k (k + 1) rfl)
        simpa using this
      right_inv y := by
        ext
        · simp only [map_add]
          rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, mappingCone.inl_v_fst_v,
            mappingCone.inr_f_fst_v]
          simp
        · simp only [map_add]
          rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, mappingCone.inl_v_snd_v,
            mappingCone.inr_f_snd_v]
          simp }
  exact Module.Flat.of_linearEquiv e

/-- If `K` vanishes in degree `k + 1`, the cycles of the mapping cone of `φ` in
degree `k` are those of `L`. -/
lemma flat_ker_d_mappingCone (k : ℤ) (h₁ : IsZero (K.X (k + 1)))
    (hL : Module.Flat A (LinearMap.ker (L.d k (k + 1)).hom)) :
    Module.Flat A (LinearMap.ker ((mappingCone φ).d k (k + 1)).hom) := by
  -- `inr φ` is an isomorphism `Lʲ ≅ (mappingCone φ)ʲ` when `Kʲ⁺¹ = 0`, with inverse `snd φ`
  have hsec (j : ℤ) (hj : IsZero (K.X (j + 1))) (x : (mappingCone φ).X j) :
      ((mappingCone.inr φ).f j).hom (((mappingCone.snd φ).v j j (add_zero j)).hom x) = x := by
    have := congrArg (fun f ↦ f.hom x) (mappingCone.id_X φ j (j + 1) rfl)
    simpa [hj.eq_of_tgt ((mappingCone.fst φ).1.v j (j + 1) rfl) 0] using this
  have hret (j : ℤ) (y : L.X j) :
      ((mappingCone.snd φ).v j j (add_zero j)).hom (((mappingCone.inr φ).f j).hom y) = y := by
    rw [← ModuleCat.comp_apply, mappingCone.inr_f_snd_v]
    rfl
  let e : L.X k ≃ₗ[A] (mappingCone φ).X k :=
    { toFun := ((mappingCone.inr φ).f k).hom
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := ((mappingCone.snd φ).v k k (add_zero k)).hom
      left_inv := hret k
      right_inv := hsec k h₁ }
  have heq : LinearMap.ker ((mappingCone φ).d k (k + 1)).hom =
      (LinearMap.ker (L.d k (k + 1)).hom).map (e : L.X k →ₗ[A] (mappingCone φ).X k) := by
    ext x
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    change _ ↔ (L.d k (k + 1)).hom (((mappingCone.snd φ).v k k (add_zero k)).hom x) = 0
    conv_lhs => rw [← hsec k h₁ x, ← ModuleCat.comp_apply, mappingCone.inr_f_d,
      ModuleCat.comp_apply]
    constructor
    · intro h
      rw [← hret (k + 1) ((L.d k (k + 1)).hom _), h, map_zero]
    · intro h
      rw [h, map_zero]
  rw [heq]
  exact Module.Flat.of_linearEquiv (e.submoduleMap _).symm

/-- **Base change preserves quasi-isomorphisms between complexes of flat modules**, provided the
cycles of the mapping cone are flat in high degrees. -/
theorem quasiIso_map_baseChange [QuasiIso φ] (hK : ∀ k, Module.Flat A (K.X k))
    (hL : ∀ k, Module.Flat A (L.X k)) {N : ℤ}
    (hN : ∀ k, N ≤ k → Module.Flat A (LinearMap.ker ((mappingCone φ).d k (k + 1)).hom)) :
    QuasiIso (((ModuleCat.baseChange A B).mapHomologicalComplex _).map φ) := by
  have hφ := (mappingCone.quasiIso_iff_acyclic φ).1 inferInstance
  have hC := flat_mappingCone_X φ hK hL
  have hex (k : ℤ) : (mappingCone φ).ExactAt k := hφ k
  have hZ (k : ℤ) : Module.Flat A (LinearMap.ker ((mappingCone φ).d k (k + 1)).hom) :=
    flat_ker_d_of_exactAt hC (m := k + 1) (fun j _ ↦ hex j) hN k (by lia)
  rw [mappingCone.quasiIso_iff_acyclic]
  intro k
  refine HomologicalComplex.ExactAt.of_iso ?_
    (mappingCone.mapHomologicalComplexIso φ (ModuleCat.baseChange A B))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  rw [exactAt_baseChange_iff]
  exact exact_lTensor_d B (m := j + 1) (fun i _ ↦ hex i) (fun i _ ↦ hZ i) j le_rfl


/-- The terms of the truncation `τ^{≤ n} C` of a complex of flat modules whose cycles in degree
`n` are flat are flat. -/
lemma flat_truncLE_X (C : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (hC : ∀ k, Module.Flat A (C.X k)) (hZ : Module.Flat A (LinearMap.ker (C.d n (n + 1)).hom))
    (i : ℤ) : Module.Flat A ((C.truncLE n).X i) := by
  rcases lt_trichotomy i n with h | rfl | h
  · have := hC i
    exact Module.Flat.of_linearEquiv (C.truncLEXIso n i h).toLinearEquiv
  · have hZ' : Module.Flat A (LinearMap.ker (C.sc i).g.hom) := by
      change Module.Flat A (LinearMap.ker (C.d i ((ComplexShape.up ℤ).next i)).hom)
      rw [CochainComplex.next]
      exact hZ
    have : Module.Flat A (C.sc i).moduleCatLeftHomologyData.K := hZ'
    exact Module.Flat.of_linearEquiv
      (C.truncLEXIsoCycles i ≪≫ (C.sc i).moduleCatCyclesIso).toLinearEquiv
  · have : Subsingleton ((C.truncLE n).X i) :=
      ModuleCat.subsingleton_of_isZero ((C.truncLE n).isZero_of_isStrictlyLE n i h)
    infer_instance

/-- **Base change of a truncation.** Let `C` be a complex of flat modules, exact in degrees `> n`,
whose cycles are flat in degrees `≥ n`. Then the truncation `τ^{≤ n} C ⟶ C` stays a
quasi-isomorphism after any base change. -/
theorem quasiIso_map_baseChange_ιTruncLE (C : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (hC : ∀ k, Module.Flat A (C.X k)) (hex : ∀ k, n < k → C.ExactAt k)
    (hZ : ∀ k, n ≤ k → Module.Flat A (LinearMap.ker (C.d k (k + 1)).hom)) :
    QuasiIso (((ModuleCat.baseChange A B).mapHomologicalComplex _).map (C.ιTruncLE n)) := by
  have : C.IsLE n := (C.isLE_iff n).2 hex
  refine quasiIso_map_baseChange B (C.ιTruncLE n) (flat_truncLE_X C n hC (hZ n le_rfl)) hC
    (N := n) fun k hk ↦ flat_ker_d_mappingCone _ k
      ((C.truncLE n).isZero_of_isStrictlyLE n _ (by lia))
      (hZ k hk)

end CochainComplex

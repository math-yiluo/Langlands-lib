import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Homology of cochain complexes of modules with vanishing differentials

Elementary facts about a cochain complex of modules in a degree where the incoming and outgoing
differentials vanish, so that the homology is the term itself.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.FibreH0Spread

section Ring

variable {R : Type u} [Ring R]

/-- If both differentials at degree `i` of the source vanish, two chain maps that are jointly
injective on degree-`i` homology are jointly injective on the degree-`i` terms. -/
theorem jointly_injective_f_of_homologyMap {C D₁ D₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (f₁ : C ⟶ D₁) (f₂ : C ⟶ D₂) (i : ℤ) (h₀ : C.d (i - 1) i = 0) (h₁ : C.d i (i + 1) = 0)
    (h : ∀ c : C.homology i, (HomologicalComplex.homologyMap f₁ i).hom c = 0 →
      (HomologicalComplex.homologyMap f₂ i).hom c = 0 → c = 0) :
    ∀ x : C.X i, (f₁.f i).hom x = 0 → (f₂.f i).hom x = 0 → x = 0 := by
  intro x hx₁ hx₂
  let c := (C.iCyclesIso i (i + 1) (by simp) h₁).inv.hom x
  have hc : (C.iCycles i).hom c = x := by
    rw [← ModuleCat.comp_apply, HomologicalComplex.iCyclesIso_inv_hom_id]
    rfl
  have key : ∀ {D : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ D), (f.f i).hom x = 0 →
      (HomologicalComplex.homologyMap f i).hom ((C.homologyπ i).hom c) = 0 := by
    intro D f hx
    have hz : (HomologicalComplex.cyclesMap f i).hom c = 0 := by
      apply (ModuleCat.mono_iff_injective (D.iCycles i)).1 inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, hc, hx,
        map_zero]
    rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply,
      hz, map_zero]
  have hπ : (C.homologyπ i).hom c = 0 := h _ (key f₁ hx₁) (key f₂ hx₂)
  have hc0 : c = 0 := by
    have hinj := (ModuleCat.mono_iff_injective
      (C.isoHomologyπ (i - 1) i (by simp) h₀).hom).1 inferInstance
    apply hinj
    rw [map_zero]
    exact hπ
  rw [← hc, hc0, map_zero]

/-- The term of a complex in a degree where both differentials vanish is isomorphic to its
homology. -/
def termIsoHomology (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (h₀ : C.d (i - 1) i = 0)
    (h₁ : C.d i (i + 1) = 0) : C.X i ≅ C.homology i :=
  (C.iCyclesIso i (i + 1) (by simp) h₁).symm ≪≫ C.isoHomologyπ (i - 1) i (by simp) h₀

lemma termIsoHomology_hom_naturality {C D : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ D)
    (i : ℤ) (hC₀ : C.d (i - 1) i = 0) (hC₁ : C.d i (i + 1) = 0) (hD₀ : D.d (i - 1) i = 0)
    (hD₁ : D.d i (i + 1) = 0) :
    (termIsoHomology C i hC₀ hC₁).hom ≫ HomologicalComplex.homologyMap f i =
      f.f i ≫ (termIsoHomology D i hD₀ hD₁).hom := by
  have hcyc : (C.iCyclesIso i (i + 1) (by simp) hC₁).inv ≫ HomologicalComplex.cyclesMap f i =
      f.f i ≫ (D.iCyclesIso i (i + 1) (by simp) hD₁).inv := by
    rw [← cancel_mono (D.iCycles i)]
    simp
  simp only [termIsoHomology, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.isoHomologyπ_hom,
    Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, hcyc, Category.assoc]

/-- If both differentials at degree `i` vanish in source and target, a chain map is bijective on
degree-`i` homology exactly when it is bijective on the degree-`i` terms. -/
theorem bijective_homologyMap_iff {C D : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ D)
    (i : ℤ) (hC₀ : C.d (i - 1) i = 0) (hC₁ : C.d i (i + 1) = 0) (hD₀ : D.d (i - 1) i = 0)
    (hD₁ : D.d i (i + 1) = 0) :
    Function.Bijective (HomologicalComplex.homologyMap f i).hom ↔
      Function.Bijective (f.f i).hom := by
  have hsq := termIsoHomology_hom_naturality f i hC₀ hC₁ hD₀ hD₁
  have hfun : (HomologicalComplex.homologyMap f i).hom ∘ (termIsoHomology C i hC₀ hC₁).hom.hom =
      (termIsoHomology D i hD₀ hD₁).hom.hom ∘ (f.f i).hom := by
    funext x
    exact congrArg (fun g ↦ g.hom x) hsq
  rw [← Function.Bijective.of_comp_iff _ (termIsoHomology C i hC₀ hC₁).toLinearEquiv.bijective,
    ← Function.Bijective.of_comp_iff' (termIsoHomology D i hD₀ hD₁).toLinearEquiv.bijective]
  exact iff_of_eq (congrArg Function.Bijective hfun)

end Ring

/-- Over a field, a degree whose homology has the dimension of the finite-dimensional term has
vanishing outgoing differential. -/
theorem d_eq_zero_of_finrank_homology {F : Type u} [Field F]
    (C : CochainComplex (ModuleCat.{u} F) ℤ) (i : ℤ) [Module.Finite F (C.X i)]
    (h : Module.finrank F (C.homology i) = Module.finrank F (C.X i)) : C.d i (i + 1) = 0 := by
  have hι : Function.Injective (C.iCycles i).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hπ : Function.Surjective (C.homologyπ i).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have : Module.Finite F (C.cycles i) := FiniteDimensional.of_injective (C.iCycles i).hom hι
  have h₁ : Module.finrank F (C.cycles i) ≤ Module.finrank F (C.X i) :=
    LinearMap.finrank_le_finrank_of_injective hι
  have h₂ : Module.finrank F (C.homology i) ≤ Module.finrank F (C.cycles i) := by
    rw [← finrank_top F (C.homology i), ← LinearMap.range_eq_top.mpr hπ]
    exact LinearMap.finrank_range_le _
  have hsurj : Function.Surjective (C.iCycles i).hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).1 hι
  ext x
  obtain ⟨c, rfl⟩ := hsurj x
  rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
  rfl

section CommRing

variable {T : Type u} [CommRing T]

/-- A complex with zero term in degree `-1`, rank-one free term in degree `0`, free term in
degree `1`, and degree-zero homology free of rank one has vanishing differential out of
degree `0`. -/
theorem d_zero_one_eq_zero (Q : CochainComplex (ModuleCat.{u} T) ℤ) (hneg : IsZero (Q.X (-1)))
    (e₀ : Q.X 0 ≃ₗ[T] T) [Module.Free T (Q.X 1)] (eH : Q.homology 0 ≃ₗ[T] T) :
    Q.d 0 1 = 0 := by
  have hd : Q.d (-1) 0 = 0 := hneg.eq_of_src _ _
  let E := Q.isoHomologyπ (-1) 0 (by simp) hd
  let j : T →ₗ[T] T :=
    e₀.toLinearMap ∘ₗ (Q.iCycles 0).hom ∘ₗ E.inv.hom ∘ₗ eH.symm.toLinearMap
  have hj : Function.Injective j := by
    have hι : Function.Injective (Q.iCycles 0).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    have hE : Function.Injective E.inv.hom := E.symm.toLinearEquiv.injective
    exact e₀.injective.comp (hι.comp (hE.comp eH.symm.injective))
  let a := j 1
  have hj_apply (t : T) : j t = t * a := by
    simpa [a] using j.map_smul t 1
  have hz : (Q.d 0 1).hom (e₀.symm a) = 0 := by
    have : e₀.symm a = (Q.iCycles 0).hom (E.inv.hom (eH.symm 1)) := by
      simp [a, j]
    rw [this, ← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  let v := (Q.d 0 1).hom (e₀.symm 1)
  have hav : a • v = 0 := by
    rw [← map_smul, ← map_smul, smul_eq_mul, mul_one]
    exact hz
  have hv : v = 0 := by
    let b := Module.Free.chooseBasis T (Q.X 1)
    apply b.repr.injective
    ext i
    have h' := congrArg (fun w ↦ b.repr w i) hav
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h'
    have : j (b.repr v i) = 0 := by
      rw [hj_apply, mul_comm]
      exact h'
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact hj (this.trans (map_zero j).symm)
  ext x
  have hx : x = e₀ x • e₀.symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  rw [hx, map_smul]
  change e₀ x • v = 0
  rw [hv, smul_zero]

/-- A linear map between modules free of rank one that has a left inverse up to a unit is
bijective. -/
theorem bijective_of_comp_eq_smul {M N : Type*} [AddCommGroup M] [Module T M] [AddCommGroup N]
    [Module T N] (eM : M ≃ₗ[T] T) (eN : N ≃ₗ[T] T) (f : M →ₗ[T] N) (g : N →ₗ[T] M) (u : T)
    (hu : IsUnit u) (h : g ∘ₗ f = u • LinearMap.id) : Function.Bijective f := by
  let t := eN (f (eM.symm 1))
  let s := eM (g (eN.symm 1))
  have hf (x : T) : eN (f (eM.symm x)) = x * t := by
    show _ = x * eN (f (eM.symm 1))
    rw [← smul_eq_mul, ← LinearEquiv.map_smul, ← LinearMap.map_smul, ← LinearEquiv.map_smul,
      smul_eq_mul, mul_one]
  have hg (y : T) : eM (g (eN.symm y)) = y * s := by
    show _ = y * eM (g (eN.symm 1))
    rw [← smul_eq_mul, ← LinearEquiv.map_smul, ← LinearMap.map_smul, ← LinearEquiv.map_smul,
      smul_eq_mul, mul_one]
  have hts : t * s = u := by
    have h1 := congrArg (fun φ : M →ₗ[T] M ↦ eM (φ (eM.symm 1))) h
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] at h1
    rw [← h1, ← hg t]
    congr 2
    exact eN.symm_apply_apply _
  have ht : IsUnit t := isUnit_of_mul_isUnit_left (hts ▸ hu)
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have := congrArg g hxy
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, h] at this
    simpa [hu.smul_left_cancel] using this
  · obtain ⟨w, hw⟩ := ht.exists_left_inv
    refine ⟨eM.symm (eN y * w), eN.injective ?_⟩
    rw [hf, mul_assoc, hw, mul_one]

end CommRing

end Langlands.Cohomology.ModuleComplex.FibreH0Spread

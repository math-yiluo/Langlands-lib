import Langlands.CommutativeAlgebra.FiniteFreeReversedDualBaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization

/-! # Maximal-ideal-power torsion in homology and reversed duals -/

universe u

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

/- The general flat-base-change and support lemmas are adapted from
Worker 975's local algebra draft, with their authorship retained. -/

/-- Flat scalar extension commutes with homology, as an actual isomorphism. -/
def flatBaseChangeHomologyIso {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((baseChange φ).obj K).homology n ≅
      (ModuleCat.extendScalars φ).obj (K.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact (K.sc n).mapHomologyIso (ModuleCat.extendScalars φ)

section Support

variable {B : Type u} [CommRing B] {M : Type u} [AddCommGroup M] [Module B M]

/-- If every element of a finite module is killed by a power of `f`, then one power of `f`
kills the whole module. -/
theorem exists_pow_smul_eq_zero [Module.Finite B M] (f : B)
    (h : ∀ x : M, ∃ k : ℕ, f ^ k • x = 0) : ∃ k : ℕ, ∀ x : M, f ^ k • x = 0 := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
  choose k hk using h
  refine ⟨s.sup k, fun x => ?_⟩
  have hx : x ∈ Submodule.span B (s : Set M) := hs ▸ Submodule.mem_top
  have hle : Submodule.span B (s : Set M) ≤
      LinearMap.ker ((f ^ s.sup k) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    have hky : k y ≤ s.sup k := Finset.le_sup (f := k) hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Nat.sub_add_cancel hky, pow_add, mul_smul, hk y, smul_zero]
  have := hle hx
  simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this

/-- Over a noetherian ring, if every element of the ideal `m` acts nilpotently on each element
of the finite module `M`, then a power of `m` kills `M`. -/
theorem exists_pow_le_annihilator [IsNoetherianRing B] [Module.Finite B M] (m : Ideal B)
    (h : ∀ f ∈ m, ∀ x : M, ∃ k : ℕ, f ^ k • x = 0) :
    ∃ N : ℕ, m ^ N ≤ Module.annihilator B M := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian m)
  intro f hf
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero f (h f hf)
  exact ⟨k, Module.mem_annihilator.mpr hk⟩

/-- Extending scalars along `φ : B →+* S` carries the annihilator of `M` into the annihilator
of `S ⊗_B M`. -/
theorem map_annihilator_le {S : Type u} [CommRing S] (φ : B →+* S) (M : ModuleCat.{u} B) :
    (Module.annihilator B M).map φ ≤
      Module.annihilator S ((ModuleCat.extendScalars φ).obj M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  refine TensorProduct.inductionOn
    (motive := fun z : TensorProduct B ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) M =>
      φ a • (show (ModuleCat.extendScalars φ).obj M from z) = 0) z ?_ ?_
  · intro s x
    have hx : a • x = 0 := Module.mem_annihilator.mp ha x
    exact (TensorProduct.smul_tmul a s x).trans (by rw [hx, TensorProduct.tmul_zero]; rfl)
  · intro y w hy hw
    exact (smul_add (A := (ModuleCat.extendScalars φ).obj M) (φ a)
      (show (ModuleCat.extendScalars φ).obj M from y)
      (show (ModuleCat.extendScalars φ).obj M from w)).trans (by rw [hy, hw, add_zero])

/-- If the scalar extension of `M` to a localization of `B` at `T` vanishes, then every element
of `M` is killed by an element of `T`. -/
theorem exists_smul_eq_zero_of_isZero {A : Type u} [CommRing A] (φ : B →+* A)
    {T : Submonoid B} (hT : T.IsLocalizationMap φ) (M : ModuleCat.{u} B)
    (h : IsZero ((ModuleCat.extendScalars φ).obj M)) (x : M) : ∃ t ∈ T, t • x = 0 := by
  let := φ.toAlgebra
  have : IsLocalization T A := ⟨hT⟩
  let g : M →ₗ[B] TensorProduct B A M := TensorProduct.mk B A M 1
  have : IsLocalizedModule T g :=
    (isLocalizedModule_iff_isBaseChange T A g).2 (TensorProduct.isBaseChange B M A)
  have hsub : Subsingleton (TensorProduct B A M) := ModuleCat.isZero_iff_subsingleton.mp h
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T g).mp (Subsingleton.elim _ _)
  exact ⟨t, t.2, ht⟩

/-- If `B_f ⊗_B M` vanishes, then every element of `M` is killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero_of_isZero (f : B) (M : ModuleCat.{u} B)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap B (Localization.Away f))).obj M))
    (x : M) : ∃ k : ℕ, f ^ k • x = 0 := by
  obtain ⟨t, ⟨k, rfl⟩, ht⟩ := exists_smul_eq_zero_of_isZero _
    ((isLocalization_iff_isLocalizationMap (Submonoid.powers f) (Localization.Away f)).mp
      inferInstance) M h x
  exact ⟨k, ht⟩

end Support

variable {B : Type u} [CommRing B]

/-- Over a noetherian ring, the homology of a strictly perfect complex is finite. -/
theorem finite_homology [IsNoetherianRing B] {Kc : CochainComplex (ModuleCat.{u} B) ℤ}
    (hKc : IsStrictlyPerfect Kc) (n : ℤ) : Module.Finite B (Kc.homology n) := by
  have := (hKc.2 n).1
  have : Module.Finite B (Kc.cycles n) :=
    Module.Finite.of_injective (Kc.iCycles n).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (Kc.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- If the homology of a strictly perfect complex over a noetherian ring vanishes after
inverting each element of `m`, then a power of `m` kills each homology module. -/
theorem exists_pow_le_annihilator_homology [IsNoetherianRing B] (m : Ideal B)
    {Kc : CochainComplex (ModuleCat.{u} B) ℤ} (hKc : IsStrictlyPerfect Kc)
    (hsupp : ∀ f ∈ m, ∀ n : ℤ,
      IsZero (((baseChange (algebraMap B (Localization.Away f))).obj Kc).homology n))
    (n : ℤ) : ∃ N : ℕ, m ^ N ≤ Module.annihilator B (Kc.homology n) := by
  have := finite_homology hKc n
  refine exists_pow_le_annihilator m fun f hf x => ?_
  have hflat : (algebraMap B (Localization.Away f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  let e := flatBaseChangeHomologyIso _ hflat Kc n
  exact exists_pow_smul_eq_zero_of_isZero f _ (IsZero.of_iso (hsupp f hf n) e.symm) x


/-- An annihilator element whose image is a unit makes the scalar extension zero. -/
theorem isZero_extendScalars_of_annihilator_of_isUnit {S : Type u} [CommRing S]
    (φ : B →+* S) (M : ModuleCat.{u} B) (a : B)
    (ha : a ∈ Module.annihilator B M) (hu : IsUnit (φ a)) :
    IsZero ((ModuleCat.extendScalars φ).obj M) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  apply (Module.annihilator_eq_top_iff (R := S)
    (M := (ModuleCat.extendScalars φ).obj M)).mp
  exact (Module.annihilator S ((ModuleCat.extendScalars φ).obj M)).eq_top_of_isUnit_mem
    (map_annihilator_le φ M (Ideal.mem_map_of_mem φ ha)) hu

/-- Inverting an element of an ideal kills homology annihilated by a power of that ideal. -/
theorem acyclic_away_of_pow_le_annihilator (m : Ideal B)
    (C : CochainComplex (ModuleCat.{u} B) ℤ)
    (h : ∀ i : ℤ, ∃ N : ℕ, m ^ N ≤ Module.annihilator B (C.homology i))
    (f : B) (hf : f ∈ m) :
    ((baseChange (algebraMap B (Localization.Away f))).obj C).Acyclic := by
  intro i
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  obtain ⟨N, hN⟩ := h i
  have hz := isZero_extendScalars_of_annihilator_of_isUnit
    (algebraMap B (Localization.Away f)) (C.homology i) (f ^ N)
    (hN (Ideal.pow_mem_pow hf N))
    (by simpa only [map_pow] using
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).pow N)
  have hflat : (algebraMap B (Localization.Away f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  exact hz.of_iso (flatBaseChangeHomologyIso _ hflat C i)

/-- Over a noetherian ring, ideal-power torsion in homology passes to reversed duals
of bounded finite free complexes. -/
theorem exists_pow_le_annihilator_homology_reversedDual [IsNoetherianRing B]
    (m : Ideal B) (g : ℤ) (C : CochainComplex (ModuleCat.{u} B) ℤ)
    (hC : IsFiniteFree C)
    (h : ∀ i : ℤ, ∃ N : ℕ, m ^ N ≤ Module.annihilator B (C.homology i))
    (i : ℤ) : ∃ N : ℕ, m ^ N ≤ Module.annihilator B ((reversedDual g C).homology i) := by
  apply exists_pow_le_annihilator_homology m
    (isStrictlyPerfect_of_isFiniteFree (isFiniteFree_reversedDual g C hC))
  intro f hf j
  exact isZero_homology_baseChange_reversedDual_of_acyclic _ g C hC
    (acyclic_away_of_pow_le_annihilator m C h f hf) j

end Langlands.CommutativeAlgebra

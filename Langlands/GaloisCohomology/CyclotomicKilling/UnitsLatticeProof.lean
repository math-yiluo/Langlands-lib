import Langlands.GaloisCohomology.CyclotomicKilling.FiniteModuleProof
import Langlands.GaloisCohomology.CyclotomicKilling.UnitsLatticeStatement
import Langlands.Cohomology.Profinite.Cup.Connecting
import Langlands.Cohomology.Profinite.InflationRestriction.DegreeOne
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-!
# Cyclotomic splitting for units–lattice coefficients

Restriction and corestriction give a uniform annihilator for degree-one cohomology
with units–lattice coefficients on open subgroups. Applying the finite-module
cyclotomic vanishing theorem to the tensor Kummer sequence then kills each primary
part of a torsion class over a finite layer.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois
  IntermediateField
open scoped TensorProduct

universe u

noncomputable section

section Cocycle

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} R G) [IsSmoothRep A]

private theorem exists_cocycleOne (c : G → A) (hc : IsLocallyConstant c)
    (hmul : ∀ σ τ, c (σ * τ) = c σ + A.ρ σ (c τ)) :
    ∃ z : cocycles A 1, ∀ σ, cocycleOneApplyG A z σ = c σ := by
  let f : locallyConstantCochains A 1 := ⟨fun x => c (x 0), hc.comp_continuous (continuous_apply 0)⟩
  have hf : ((cochains A).d 1 2).hom f = 0 := (cochains_d_one_eq_zero_iff A f).2 hmul
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_d_eq_zero (cochains A) 1 f hf
  exact ⟨z, fun σ => congrArg (fun f : locallyConstantCochains A 1 => f.1 fun _ => σ) hz⟩

private theorem class_eq_zero_iff_coboundary (z : cocycles A 1) (m : ℕ) :
    m • (cohomologyπ A 1).hom z = 0 ↔
      ∃ b : A, ∀ σ, m • cocycleOneApplyG A z σ = A.ρ σ b - b := by
  rw [← map_nsmul]
  change ((cochains A).homologyπ (0 + 1)).hom (m • z) = 0 ↔ _
  rw [homologyπ_succ_eq_zero_iff (cochains A) 0]
  simp only [map_nsmul]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.1 Fin.elim0, fun σ => ?_⟩
    have h := congrArg (fun f : locallyConstantCochains A 1 => f.1 fun _ => σ) hw
    exact h.symm.trans (cochains_d_zero_apply A w fun _ => σ)
  · rintro ⟨b, hb⟩
    refine ⟨⟨fun _ => b, IsLocallyConstant.const _⟩, Subtype.ext (funext fun f => ?_)⟩
    rw [cochains_d_zero_apply, fin_one_eq_const f]
    exact (hb (f 0)).symm

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (B : Rep.{u} R H) [IsSmoothRep B] (φ : H →ₜ* G) (f : Rep.res φ.toMonoidHom A ⟶ B)

private theorem cocycleOneApplyG_map (z : cocycles A 1) (σ : H) :
    cocycleOneApplyG B ((cocyclesMap φ f 1).hom z) σ =
      f.hom (cocycleOneApplyG A z (φ σ)) := by
  simp only [cocycleOneApplyG, cocyclesMap, iCycles_cyclesMap_apply]
  rfl

end Cocycle

section Annihilator

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (X : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K)) [IsSmoothRep X]
  [Module.Free (ULift.{u} ℤ) X] [Module.Finite (ULift.{u} ℤ) X]

local notation "unitsRep" => unitsModule K Ω
local notation "latticeCoeffs" => (unitsModule K Ω ⊗ X)

omit [NumberField K] [IsSepClosure K Ω] in
private theorem exists_open_kernel :
    ∃ V : OpenSubgroup Gal(Ω/K), (V : Subgroup Gal(Ω/K)) = X.ρ.ker := by
  let b := Module.Free.chooseBasis (ULift.{u} ℤ) X
  have hb :
      (X.ρ.ker : Set Gal(Ω/K)) = ⋂ i, (vectorStabilizer X.ρ (b i) : Set Gal(Ω/K)) := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_iInter, MonoidHom.mem_ker, mem_vectorStabilizer]
    constructor
    · intro h i
      rw [h]
      rfl
    · intro h
      exact b.ext fun i => h i
  refine ⟨⟨X.ρ.ker, ?_⟩, rfl⟩
  change IsOpen (X.ρ.ker : Set Gal(Ω/K))
  rw [hb]
  exact isOpen_iInter_of_finite (fun i => IsSmoothRep.isOpen_stabilizer X (b i))

set_option maxHeartbeats 400000 in
omit [NumberField K] in
private theorem subsingleton_cohomology_one_of_trivial_lattice (U : OpenSubgroup Gal(Ω/K))
    (hU : (U : Subgroup Gal(Ω/K)) ≤ X.ρ.ker) :
    Subsingleton (cohomology (Rep.res (U : Subgroup Gal(Ω/K)).subtype latticeCoeffs) 1) := by
  let C := Rep.res (U : Subgroup Gal(Ω/K)).subtype latticeCoeffs
  let D := Rep.res (U : Subgroup Gal(Ω/K)).subtype unitsRep
  let idU : (U : Subgroup Gal(Ω/K)) →ₜ* (U : Subgroup Gal(Ω/K)) := .id _
  suffices h : ∀ x : cohomology C 1, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective C 1 x
  let b := Module.Free.chooseBasis (ULift.{u} ℤ) X
  let e : C ≃ₗ[ULift.{u} ℤ] (_ → D) :=
    (TensorProduct.equivFinsuppOfBasisRight (M := ↑D) b).trans
      (Finsupp.linearEquivFunOnFinite (ULift.{u} ℤ) D _)
  have e_tmul (a : D) (v : X) (i : Module.Free.ChooseBasisIndex (ULift.{u} ℤ) X) :
      e (a ⊗ₜ[ULift.{u} ℤ] v) i = b.repr v i • a :=
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b a v i
  have he (σ : U) (t : C) (i : Module.Free.ChooseBasisIndex (ULift.{u} ℤ) X) :
      e (C.ρ σ t) i = D.ρ σ (e t i) := by
    change e ((latticeCoeffs).ρ (σ : Gal(Ω/K)) t) i = (unitsRep).ρ (σ : Gal(Ω/K)) (e t i)
    induction t using TensorProduct.inductionOn with
    | tmul a v =>
      have hv : X.ρ (σ : Gal(Ω/K)) v = v :=
        congrArg (fun f : Module.End (ULift.{u} ℤ) X => f v) (hU σ.2)
      rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, hv]
      rw [e_tmul, e_tmul, map_smul]
    | add t₁ t₂ h₁ h₂ => simp only [map_add, Pi.add_apply, h₁, h₂]
  let f (i : Module.Free.ChooseBasisIndex (ULift.{u} ℤ) X) : C ⟶ D :=
    Rep.ofHom ⟨(LinearMap.proj i).comp e.toLinearMap, fun σ => LinearMap.ext fun t => he σ t i⟩
  have : Subsingleton (cohomology D 1) := Local.subsingleton_cohomology_one_res_unitsModule K Ω U
  have hi (i : Module.Free.ChooseBasisIndex (ULift.{u} ℤ) X) :
      ∃ b : D, ∀ σ : U, e (cocycleOneApplyG C z σ) i = D.ρ σ b - b := by
    obtain ⟨b, hb⟩ := (class_eq_zero_iff_coboundary D
      ((cocyclesMap (A := C) idU (f i) 1).hom z) 1).1 (Subsingleton.elim _ _)
    exact ⟨b, fun σ => by
      specialize hb σ
      rw [one_nsmul] at hb
      exact (cocycleOneApplyG_map C D idU (f i) z σ).symm.trans hb⟩
  choose a ha using hi
  have hzero := (class_eq_zero_iff_coboundary C z 1).2 ⟨e.symm a, fun σ => by
    rw [one_nsmul]
    apply e.injective
    funext i
    rw [map_sub, Pi.sub_apply, he, e.apply_symm_apply]
    exact ha i σ⟩
  simpa only [one_nsmul] using hzero

set_option maxHeartbeats 500000 in
omit [NumberField K] in
/-- The index of an open subgroup acting trivially on the lattice kills degree-one
cohomology on every open subgroup, by restriction and corestriction. -/
private theorem exists_annihilator_units_lattice :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ (U : OpenSubgroup Gal(Ω/K))
      (x : cohomology (Rep.res (U : Subgroup Gal(Ω/K)).subtype latticeCoeffs) 1), d • x = 0 := by
  obtain ⟨V, hV⟩ := exists_open_kernel X
  have : (V : Subgroup Gal(Ω/K)).Normal := hV ▸ (show X.ρ.ker.Normal from inferInstance)
  refine ⟨(V : Subgroup Gal(Ω/K)).index, Subgroup.index_ne_zero_of_finite, fun U x => ?_⟩
  let W := V ⊓ U
  have hWU : W ≤ U := inf_le_right
  have hWV : (W : Subgroup Gal(Ω/K)) ≤ X.ρ.ker := hV ▸ inf_le_left
  have : Subsingleton (cohomology (Rep.res (W : Subgroup Gal(Ω/K)).subtype latticeCoeffs) 1) :=
    subsingleton_cohomology_one_of_trivial_lattice X W hWV
  have hx := (coresOfLE_resOfLE latticeCoeffs hWU 1 x).symm
  rw [Subsingleton.elim ((resOfLE latticeCoeffs (show (W : Subgroup Gal(Ω/K)) ≤ U from hWU) 1).hom x)
    0, map_zero] at hx
  have hd : (W : Subgroup Gal(Ω/K)).relIndex U ∣ (V : Subgroup Gal(Ω/K)).index := by
    have he : (W : Subgroup Gal(Ω/K)).subgroupOf U = (V : Subgroup Gal(Ω/K)).subgroupOf U := by
      ext σ
      exact ⟨fun h => h.1, fun h => ⟨h, σ.2⟩⟩
    rw [Subgroup.relIndex, he, ← Subgroup.relIndex]
    exact Subgroup.relIndex_dvd_index_of_normal (V : Subgroup Gal(Ω/K)) (U : Subgroup Gal(Ω/K))
  obtain ⟨k, hk⟩ := hd
  rw [hk, mul_nsmul, hx, nsmul_zero]

end Annihilator

section Kummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (X : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K)) [IsSmoothRep X]
  [Module.Free (ULift.{u} ℤ) X] [Module.Finite (ULift.{u} ℤ) X]

private abbrev tensorKummerSequence (n : ℕ) :=
  (kummerSequence K Ω n).map (tensorRight X)

omit [IsSmoothRep X] [Module.Finite (ULift.{u} ℤ) X] in
private theorem tensorKummerSequence_shortExact (n : ℕ) (hn : n ≠ 0) :
    (tensorKummerSequence X n).ShortExact := by
  let S := kummerSequence K Ω n
  have hS : S.ShortExact := kummerSequence_shortExact n (Nat.cast_ne_zero.mpr hn)
  have hExact : Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (forget₂ (Rep.{u} (ULift.{u} ℤ) Gal(Ω/K)) (ModuleCat.{u} (ULift.{u} ℤ))))).1
      (hS.exact.map _)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · refine shortComplex_exact_of_forall_exists (tensorKummerSequence X n) fun x hx => ?_
    exact (Module.Flat.rTensor_exact (↑X) hExact x).mp hx
  · exact (Rep.mono_iff_injective _).2 (Module.Flat.rTensor_preserves_injective_linearMap
      (M := ↑X) S.f.hom.toLinearMap ((Rep.mono_iff_injective S.f).1 hS.mono_f))
  · exact (Rep.epi_iff_surjective _).2 (LinearMap.rTensor_surjective (↑X)
      ((Rep.epi_iff_surjective S.g).1 hS.epi_g))

omit [NumberField K] [IsSepClosure K Ω] [IsSmoothRep X] [Module.Free (ULift.{u} ℤ) X]
  [Module.Finite (ULift.{u} ℤ) X] in
private theorem tensorKummerSequence_g (n : ℕ) :
    (tensorKummerSequence X n).g = n • 𝟙 (tensorKummerSequence X n).X₂ := by
  change (tensorRight X).map (n • 𝟙 (unitsModule K Ω)) = _
  rw [Functor.map_nsmul, (tensorRight X).map_id]
  rfl

omit [NumberField K] [IsSepClosure K Ω] [IsSmoothRep X] in
private theorem finite_tensorKummerSequence_X₁ (n : ℕ) [NeZero n] :
    Finite (tensorKummerSequence X n).X₁ := by
  let M := rootsOfUnityModule K Ω n
  have : Finite M := by
    change Finite (rootsOfUnity n Ω)
    infer_instance
  let b := Module.Free.chooseBasis (ULift.{u} ℤ) X
  let e := (TensorProduct.equivFinsuppOfBasisRight (M := ↑M) b).trans
    (Finsupp.linearEquivFunOnFinite (ULift.{u} ℤ) M _)
  exact Finite.of_equiv _ e.symm.toEquiv

omit [IsSmoothRep X] [Module.Finite (ULift.{u} ℤ) X] in
private theorem nsmul_tensorKummerSequence_X₁ (n : ℕ) (hn : n ≠ 0)
    (z : (tensorKummerSequence X n).X₁) :
    n • z = 0 := by
  let S := tensorKummerSequence X n
  let _ : Mono S.f := (tensorKummerSequence_shortExact X n hn).mono_f
  have hzero : n • S.f = 0 := by
    have h : S.f ≫ (n • 𝟙 S.X₂) = 0 := (congrArg (S.f ≫ ·) (tensorKummerSequence_g X n)).symm.trans S.zero
    simpa only [Preadditive.comp_nsmul, Category.comp_id] using h
  have h : n • 𝟙 S.X₁ = 0 := by
    apply (cancel_mono S.f).1
    rw [Preadditive.nsmul_comp, Category.id_comp, Limits.zero_comp, hzero]
  exact congrArg (fun f : S.X₁ ⟶ S.X₁ => f.hom z) h

end Kummer

section Restriction

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} R G) [IsSmoothRep A]

private theorem res_eq_zero_of_le {U V : Subgroup G} (hVU : V ≤ U) {j : ℕ}
    {x : cohomology A j} (hx : (res A U j).hom x = 0) :
    (res A V j).hom x = 0 := by
  have hcomp : res A U j ≫ resOfLE A hVU j = res A V j := by
    rw [res_eq A U, res_eq A V, resOfLE]
    exact (map_comp _ _ _ _ j).symm.trans (map_congr _ _ (by ext; rfl) (fun _ => rfl) j)
  rw [← hcomp, ModuleCat.comp_apply, hx, map_zero]

end Restriction

section Splitting

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (X : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K)) [IsSmoothRep X]
  [Module.Free (ULift.{u} ℤ) X] [Module.Finite (ULift.{u} ℤ) X]

omit [NumberField K] [IsSepClosure K Ω] in
private theorem cyclotomicLayer_le_of_isPrimitiveRoot {N : ℕ} [NeZero N]
    {E : IntermediateField K Ω} {ζ : Ω} (hζ : ζ ∈ E) (hprim : IsPrimitiveRoot ζ N) :
    cyclotomicLayer K Ω N ≤ E := by
  apply adjoin_le_iff.2
  intro x hx
  obtain ⟨i, _, rfl⟩ := hprim.eq_pow_of_pow_eq_one hx
  exact E.toSubalgebra.pow_mem hζ i

set_option maxHeartbeats 650000 in
private theorem exists_res_eq_zero_prime_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (a : ℕ)
    (x : cohomology (unitsModule K Ω ⊗ X) 1) (hx : ℓ ^ a • x = 0) :
    ∃ r : ℕ, ∀ E : IntermediateField K Ω, cyclotomicLayer K Ω (ℓ ^ r) ≤ E →
      (res (unitsModule K Ω ⊗ X) E.fixingSubgroup 1).hom x = 0 := by
  let A : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K) := unitsModule K Ω ⊗ X
  obtain ⟨d, hd₀, hd⟩ := exists_annihilator_units_lattice X
  let k := d.factorization ℓ
  let n := ℓ ^ k
  let d' := d / n
  have hn : n ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : NeZero n := ⟨hn⟩
  have hdprod : n * d' = d := Nat.ordProj_mul_ordCompl_eq_self d ℓ
  have hcop : (ℓ ^ a).Coprime d' := (Nat.coprime_ordCompl hℓ hd₀).pow_left a
  let S := tensorKummerSequence X n
  have : IsSmoothRep S.X₁ := isSmoothRep_map_tensorRight_X₁ X
  have : IsSmoothRep S.X₂ := isSmoothRep_map_tensorRight_X₂ X
  have : IsSmoothRep S.X₃ := isSmoothRep_map_tensorRight_X₃ X
  have : Finite S.X₁ := finite_tensorKummerSequence_X₁ X n
  have hS : S.ShortExact := tensorKummerSequence_shortExact X n hn
  obtain ⟨r, hβ⟩ := numberFieldFiniteModuleCyclotomicKilling K Ω S.X₁ ℓ k hℓ
    (nsmul_tensorKummerSequence_X₁ X n hn) ((δ hS 1 2 rfl).hom x)
  let N := ℓ ^ r
  have : NeZero N := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  have : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hprim⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
  let D := cyclotomicLayer K Ω N
  have hζ : ζ ∈ D := IntermediateField.subset_adjoin K _ hprim.pow_eq_one
  have hD : D = K⟮ζ⟯ :=
    le_antisymm (cyclotomicLayer_le_of_isPrimitiveRoot (mem_adjoin_simple_self K ζ) hprim)
      (adjoin_le_iff.2 (Set.singleton_subset_iff.2 hζ))
  have : FiniteDimensional K D :=
    hD ▸ IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let U : OpenSubgroup Gal(Ω/K) := ⟨D.fixingSubgroup, D.fixingSubgroup_isOpen⟩
  let F : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K) ⥤ Rep.{u} (ULift.{u} ℤ) D.fixingSubgroup :=
    Rep.resFunctor D.fixingSubgroup.subtype
  let Q := S.map F
  have hQ : Q.ShortExact := shortExact_map_res D.fixingSubgroup hS
  have hδ : (δ hQ 1 2 rfl).hom ((res A D.fixingSubgroup 1).hom x) = 0 := by
    have h := congrArg (fun f : cohomology S.X₃ 1 ⟶ cohomology Q.X₁ 2 => f.hom x)
      (δ_comp_res D.fixingSubgroup hS 1 2 rfl)
    exact h.symm.trans (hβ D ⟨ζ, hζ, hprim⟩)
  have hexact : ∃ y : cohomology Q.X₂ 1, (coeffMap Q.g 1).hom y =
      (res A D.fixingSubgroup 1).hom x :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hQ 1 2 rfl) _ hδ
  obtain ⟨y, hy⟩ := hexact
  have hg : Q.g = n • 𝟙 Q.X₂ := calc
    _ = F.map (n • 𝟙 S.X₂) :=
      congrArg (fun f : S.X₂ ⟶ S.X₂ => F.map f) (tensorKummerSequence_g X n)
    _ = n • F.map (𝟙 S.X₂) := F.map_nsmul
    _ = _ := congrArg (n • ·) (F.map_id S.X₂)
  have hg' : coeffMap Q.g 1 = n • 𝟙 (cohomology Q.X₂ 1) := calc
    _ = coeffMap (n • 𝟙 Q.X₂) 1 :=
      congrArg (fun f : Q.X₂ ⟶ Q.X₂ => coeffMap f 1) hg
    _ = _ := (map_id_nsmul Q.X₂ (𝟙 Q.X₂) n 1).trans
      (congrArg (n • ·) (coeffMap_id 1))
  have hy' : n • y = (res A D.fixingSubgroup 1).hom x := by
    exact (congrArg (fun f : cohomology Q.X₂ 1 ⟶ cohomology Q.X₂ 1 => f.hom y) hg').symm.trans hy
  have hz : (res A D.fixingSubgroup 1).hom x = 0 := by
    apply (nsmul_eq_zero_iff_of_coprime hcop).mp
    constructor
    · rw [← map_nsmul, hx, map_zero]
    · have hdy : d' • (n • y) = 0 := by
        rw [← mul_nsmul, hdprod]
        exact hd U y
      exact (congrArg (fun t : cohomology Q.X₂ 1 => d' • t) hy').symm.trans hdy
  exact ⟨r, fun E hDE => res_eq_zero_of_le A (IntermediateField.fixingSubgroup_antitone hDE) hz⟩

private theorem exists_res_eq_zero_torsion (m : ℕ) :
    0 < m → ∀ x : cohomology (unitsModule K Ω ⊗ X) 1, m • x = 0 →
      ∃ N : ℕ, 0 < N ∧ (∀ q, q.Prime → q ∣ N → q ∣ m) ∧
        ∀ E : IntermediateField K Ω, cyclotomicLayer K Ω N ≤ E →
          (res (unitsModule K Ω ⊗ X) E.fixingSubgroup 1).hom x = 0 := by
  let A : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K) := unitsModule K Ω ⊗ X
  induction m using Nat.recOnPrimeCoprime with
  | zero => exact fun hm => (Nat.lt_irrefl 0 hm).elim
  | prime_pow p a hp =>
    intro _ x hx
    cases a with
    | zero =>
      simp only [pow_zero, one_nsmul] at hx
      subst x
      exact ⟨1, Nat.one_pos, fun _ _ hq => by simpa only [pow_zero] using hq,
        fun E _ => map_zero (res A E.fixingSubgroup 1).hom⟩
    | succ a =>
      obtain ⟨r, hr⟩ := exists_res_eq_zero_prime_pow X hp (a + 1) x hx
      exact ⟨p ^ r, pow_pos hp.pos _, fun q hq hdiv =>
        dvd_pow (hq.dvd_of_dvd_pow hdiv) (Nat.succ_ne_zero a), hr⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ x hx
    have hax : a • (b • x) = 0 := by rw [← mul_nsmul, Nat.mul_comm b a, hx]
    have hbx : b • (a • x) = 0 := by rw [← mul_nsmul, hx]
    obtain ⟨M, hM, hMa, hME⟩ := iha (Nat.zero_lt_of_lt ha) (b • x) hax
    obtain ⟨N, hN, hNb, hNE⟩ := ihb (Nat.zero_lt_of_lt hb) (a • x) hbx
    refine ⟨M * N, Nat.mul_pos hM hN, ?_, fun E hE => ?_⟩
    · intro q hq hdiv
      rcases hq.dvd_mul.mp hdiv with h | h
      · exact dvd_mul_of_dvd_left (hMa q hq h) b
      · exact dvd_mul_of_dvd_right (hNb q hq h) a
    · have h₁ := hME E ((cyclotomicLayer_mono (dvd_mul_right M N)).trans hE)
      have h₂ := hNE E ((cyclotomicLayer_mono (dvd_mul_left N M)).trans hE)
      rw [map_nsmul] at h₁ h₂
      exact (nsmul_eq_zero_iff_of_coprime hab).mp ⟨h₂, h₁⟩

end Splitting

/-- A torsion cocycle with units–lattice coefficients becomes a coboundary
after adjoining roots of unity with orders supported on its annihilator. -/
theorem numberFieldUnitsLatticeCyclotomicSplitting :
    NumberFieldUnitsLatticeCyclotomicSplittingStatement.{u} := by
  intro K _ _ Ω _ _ _ X _ _ _ c hc hmul m hm hb
  let A : Rep.{u} (ULift.{u} ℤ) Gal(Ω/K) := unitsModule K Ω ⊗ X
  obtain ⟨z, hz⟩ := exists_cocycleOne A c hc hmul
  have hx : m • (cohomologyπ A 1).hom z = 0 := by
    obtain ⟨b, hb⟩ := hb
    exact (class_eq_zero_iff_coboundary A z m).2 ⟨b, fun σ => by rw [hz, hb]⟩
  obtain ⟨N, hN, hdiv, hsplit⟩ := exists_res_eq_zero_torsion X m hm _ hx
  refine ⟨N, hN, hdiv, fun E ⟨ζ, hζ, hprim⟩ => ?_⟩
  have : NeZero N := ⟨hN.ne'⟩
  let B := Rep.res E.fixingSubgroup.subtype A
  let φ := subgroupInclusion E.fixingSubgroup
  let z' := (cocyclesMap (A := A) φ (𝟙 B) 1).hom z
  have hx' : (cohomologyπ B 1).hom z' = 0 :=
    (cohomologyπ_map_apply (A := A) φ (𝟙 B) 1 z).symm.trans
      (hsplit E (cyclotomicLayer_le_of_isPrimitiveRoot hζ hprim))
  have hz' (σ : E.fixingSubgroup) : cocycleOneApplyG B z' σ = c σ :=
    (cocycleOneApplyG_map A B φ (𝟙 B) z σ).trans (hz σ)
  obtain ⟨b, hb⟩ := (class_eq_zero_iff_coboundary B z' 1).1 (by simpa only [one_nsmul] using hx')
  refine ⟨b, fun σ hσ => ?_⟩
  have h := hb ⟨σ, hσ⟩
  rw [one_nsmul, hz'] at h
  exact h

end

end Langlands.GaloisCohomology

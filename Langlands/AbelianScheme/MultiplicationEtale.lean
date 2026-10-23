import Langlands.AbelianScheme.MultiplicationEtaleStatement
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Etaleness of invertible multiplication on abelian schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.MultiplicationChart

open SquareZero InfinitesimalKernel

variable {S : Scheme.{u}} {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)
  {M : Over S} (f : M ⟶ M)
  (cU cV : Chart S₀ M) (hVU : cV.U ≤ f.left ⁻¹ᵁ cU.U)

/-- The map on affine chart rings, as a map over the base chart. -/
def chartMap : cU.Ring →ₐ[Γ(S, S₀)] cV.Ring :=
  { (f.left.appLE cU.U cV.U hVU).hom with
    commutes' := fun r => by
      have h := Scheme.Hom.appLE_comp_appLE f.left M.hom S₀ cU.U cV.U cU.le hVU
      have h' : M.hom.appLE S₀ cU.U cU.le ≫ f.left.appLE cU.U cV.U hVU =
          M.hom.appLE S₀ cV.U cV.le := by simpa only [Over.w] using h
      exact congrArg (fun k => CommRingCat.Hom.hom k r) h' }

/-- Composition with multiplication is described by its map on chart rings. -/
lemma pt_comp {D : Type u} [CommRing D] [Algebra Γ(S, S₀) D]
    (ψ : cV.Ring →ₐ[Γ(S, S₀)] D) :
    cV.pt hS₀ ψ ≫ f = cU.pt hS₀ (ψ.comp (chartMap f cU cV hVU)) := by
  ext1
  change (Spec.map _ ≫ cV.isAffine.fromSpec) ≫ f.left = Spec.map _ ≫ cU.isAffine.fromSpec
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f.left
    cU.isAffine cV.isAffine hVU]
  erw [← Spec.map_comp_assoc]
  rfl

variable [GrpObj M] [IsCommMonObj M] (n : ℕ)
  (hpow : ∀ {Y : Over S} (x : Y ⟶ M), x ≫ f = x ^ n)
  (hn : IsUnit (n : Γ(S, S₀))) (cW : Chart S₀ M)
  (hVW : cV.U ≤ (1 : M ⟶ M).left ⁻¹ᵁ cW.U)

include hS₀ hpow hn hVW in
/-- Multiplication is formally etale on compatible affine charts. -/
lemma formallyEtale [Algebra.FormallySmooth Γ(S, S₀) cV.Ring] :
    RingHom.FormallyEtale (f.left.appLE cU.U cV.U hVU).hom := by
  let : Algebra cU.Ring cV.Ring := (chartMap f cU cV hVU).toRingHom.toAlgebra
  let : IsScalarTower Γ(S, S₀) cU.Ring cV.Ring :=
    IsScalarTower.of_algHom (chartMap f cU cV hVU)
  change Algebra.FormallyEtale cU.Ring cV.Ring
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro D _ _ I hI
  let : Algebra Γ(S, S₀) D := Algebra.compHom D (algebraMap Γ(S, S₀) cU.Ring)
  let : IsScalarTower Γ(S, S₀) cU.Ring D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hp {E : Type u} [CommRing E] [Algebra cU.Ring E] [Algebra Γ(S, S₀) E]
      [IsScalarTower Γ(S, S₀) cU.Ring E] (φ : cV.Ring →ₐ[cU.Ring] E) :
      (cV.pt hS₀ (φ.restrictScalars Γ(S, S₀))) ^ n =
        cU.pt hS₀ (IsScalarTower.toAlgHom Γ(S, S₀) cU.Ring E) := by
    rw [← hpow, pt_comp]
    congr 1
    ext r
    exact φ.commutes r
  have hunit (φ : cV.Ring →ₐ[Γ(S, S₀)] D ⧸ I) :
      Set.range (1 : testObj hS₀ (D ⧸ I) ⟶ M).left ⊆ cW.U := by
    rw [← MonObj.comp_one (cV.pt hS₀ φ)]
    rintro _ ⟨z, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hVW (cV.range_pt hS₀ φ ⟨z, rfl⟩)
  have hnD : IsUnit (n : D) := by simpa using hn.map (algebraMap Γ(S, S₀) D)
  constructor
  · intro φ₁ φ₂ h
    have hred : (Ideal.Quotient.mkₐ Γ(S, S₀) I).comp (φ₁.restrictScalars Γ(S, S₀)) =
        (Ideal.Quotient.mkₐ Γ(S, S₀) I).comp (φ₂.restrictScalars Γ(S, S₀)) := by
      ext r
      exact congrArg (fun g : cV.Ring →ₐ[cU.Ring] D ⧸ I => g r) h
    have hr : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫
        (cV.pt hS₀ (φ₁.restrictScalars Γ(S, S₀)) *
          (cV.pt hS₀ (φ₂.restrictScalars Γ(S, S₀)))⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, cV.testHom_comp_pt, cV.testHom_comp_pt,
        hred, mul_inv_cancel]
    have hrn : (cV.pt hS₀ (φ₁.restrictScalars Γ(S, S₀)) *
        (cV.pt hS₀ (φ₂.restrictScalars Γ(S, S₀)))⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hp φ₁, hp φ₂, mul_inv_cancel]
    have h1 := eq_one_of_pow_eq_one hS₀ hI cW (hunit ((Ideal.Quotient.mkₐ Γ(S, S₀) I).comp
      (φ₁.restrictScalars Γ(S, S₀)))) n hnD _ hr hrn
    exact AlgHom.restrictScalars_injective Γ(S, S₀)
      (cV.pt_injective hS₀ (mul_inv_eq_one.mp h1))
  · intro φ
    let φ₀ := φ.restrictScalars Γ(S, S₀)
    have hInil : IsNilpotent I := ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩
    let x := cV.pt hS₀ (Algebra.FormallySmooth.lift I hInil φ₀)
    let y := cU.pt hS₀ (IsScalarTower.toAlgHom Γ(S, S₀) cU.Ring D)
    have hx₀ : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ x = cV.pt hS₀ φ₀ := by
      rw [cV.testHom_comp_pt, Algebra.FormallySmooth.comp_lift]
    have hy₀ : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ y =
        (cV.pt hS₀ φ₀) ^ n := by
      rw [hp φ, cU.testHom_comp_pt]
      rfl
    have hk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ (x ^ n * y⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_pow, hx₀, hy₀, mul_inv_cancel]
    obtain ⟨r, hr, hrn⟩ := exists_pow_eq hS₀ hI cW (hunit φ₀) n hnD _ hk
    have hxn : (x * r⁻¹) ^ n = y := by
      rw [mul_pow, inv_pow, hrn]
      simp only [mul_inv_rev, inv_inv]
      rw [mul_left_comm, mul_inv_cancel, mul_one]
    have hxmk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ (x * r⁻¹) =
        cV.pt hS₀ φ₀ := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, hx₀, hr, inv_one, mul_one]
    have hxrange : Set.range (x * r⁻¹).left ⊆ cV.U := by
      rw [← range_testHom_comp hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I)
        (Ideal.Quotient.mkₐ_surjective Γ(S, S₀) I) (isNilpotent_ker_mk hI) (x * r⁻¹), hxmk]
      exact cV.range_pt hS₀ φ₀
    obtain ⟨ψ, hψ⟩ := cV.exists_pt hS₀ (x * r⁻¹) hxrange
    have hψbase : ψ.comp (chartMap f cU cV hVU) =
        IsScalarTower.toAlgHom Γ(S, S₀) cU.Ring D := by
      apply cU.pt_injective hS₀
      rw [← pt_comp, hpow, hψ, hxn]
    let ψ' : cV.Ring →ₐ[cU.Ring] D :=
      { ψ.toRingHom with commutes' := fun b => congrArg (fun g => g b) hψbase }
    refine ⟨ψ', ?_⟩
    have hred : (Ideal.Quotient.mkₐ Γ(S, S₀) I).comp ψ = φ₀ := by
      apply cV.pt_injective hS₀
      rw [← cV.testHom_comp_pt, hψ, hxmk]
    ext b
    exact congrArg (fun g => g b) hred

end Langlands.AlgebraicGeometry.MultiplicationChart

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.GroupScheme

variable {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ)

/-- Multiplication is locally of finite presentation, by cancellation against the smooth
structure morphism. -/
lemma multiplication_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (multiplication A.toGrp (n : ℤ)).hom.hom.left := by
  have : LocallyOfFinitePresentation
      ((multiplication A.toGrp (n : ℤ)).hom.hom.left ≫ A.toGrp.X.hom) := by
    rw [Over.w]
    infer_instance
  exact locallyOfFinitePresentation_of_comp _ A.toGrp.X.hom

/-- Multiplication by an invertible natural number is etale. -/
theorem multiplication_etale (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (multiplication A.toGrp (n : ℤ)).hom.hom.left := by
  let f := (multiplication A.toGrp (n : ℤ)).hom.hom
  have hLFP := multiplication_locallyOfFinitePresentation A n
  change Etale f.left
  rw [HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
        RingHom.Etale.containsIdentities)).left]
  intro x
  obtain ⟨S₀, hS₀, hxS₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := A.toGrp.X.hom x) (U := ⊤) trivial
  have hfx : f.left x ∈ A.toGrp.X.hom ⁻¹ᵁ S₀ := by
    change A.toGrp.X.hom (f.left x) ∈ S₀
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hxS₀
  have h1x : (1 : A.toGrp.X ⟶ A.toGrp.X).left x ∈ A.toGrp.X.hom ⁻¹ᵁ S₀ := by
    change A.toGrp.X.hom ((1 : A.toGrp.X ⟶ A.toGrp.X).left x) ∈ S₀
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hxS₀
  obtain ⟨U, hU, hxU, hUS⟩ := exists_isAffineOpen_mem_and_subset hfx
  obtain ⟨W, hW, hxW, hWS⟩ := exists_isAffineOpen_mem_and_subset h1x
  obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := f.left ⁻¹ᵁ U ⊓ (1 : A.toGrp.X ⟶ A.toGrp.X).left ⁻¹ᵁ W)
    (TopologicalSpace.Opens.mem_inf.mpr ⟨hxU, hxW⟩)
  have hVU : V ≤ f.left ⁻¹ᵁ U := fun v hv => (TopologicalSpace.Opens.mem_inf.mp (hVsub hv)).1
  have hVS : V ≤ A.toGrp.X.hom ⁻¹ᵁ S₀ := by
    intro v hv
    have h := hUS (hVU hv)
    change A.toGrp.X.hom (f.left v) ∈ S₀ at h
    change A.toGrp.X.hom v ∈ S₀
    rwa [← Scheme.Hom.comp_apply, Over.w] at h
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, ?_⟩
  let cU : Chart S₀ A.toGrp.X := ⟨U, hU, hUS⟩
  let cV : Chart S₀ A.toGrp.X := ⟨V, hV, hVS⟩
  let cW : Chart S₀ A.toGrp.X := ⟨W, hW, hWS⟩
  have hnS₀ : IsUnit (n : Γ(S, S₀)) := by
    simpa using hn.map (S.presheaf.map (homOfLE le_top).op).hom
  have : Algebra.Smooth Γ(S, S₀) cV.Ring :=
    HasRingHomProperty.appLE @Smooth A.toGrp.X.hom inferInstance ⟨S₀, hS₀⟩ ⟨V, hV⟩ hVS
  have hfe := MultiplicationChart.formallyEtale hS₀ f cU cV hVU n
    (fun x => by simpa only [zpow_natCast] using points_multiplication A.toGrp (n : ℤ) _ x) hnS₀ cW
    (fun v hv => (TopologicalSpace.Opens.mem_inf.mp (hVsub hv)).2)
  have hfp := HasRingHomProperty.appLE @LocallyOfFinitePresentation f.left hLFP
    ⟨U, hU⟩ ⟨V, hV⟩ hVU
  let : Algebra Γ(A.toGrp.X.left, U) Γ(A.toGrp.X.left, V) :=
    (f.left.appLE U V hVU).hom.toAlgebra
  change Algebra.Etale Γ(A.toGrp.X.left, U) Γ(A.toGrp.X.left, V)
  exact ⟨hfe, hfp⟩

/-- Exact published target: positive multiplication is etale when invertible on the base. -/
theorem multiplicationEtale : MultiplicationEtaleStatement.{u} := by
  intro S A n _ hn
  exact multiplication_etale A n hn

end Langlands.AbelianScheme

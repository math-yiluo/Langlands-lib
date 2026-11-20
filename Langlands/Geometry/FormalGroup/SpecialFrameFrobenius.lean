import Langlands.Geometry.FormalGroup.SpecialFrameFrobeniusStatement
import Langlands.Geometry.FormalGroup.DelignePiAlgebra
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Langlands.Geometry.FormalGroup.ScalarIsogenyTensorInverse

/-! # Global rational inversion of relative Frobenius -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory FiniteKernelComposition

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type}

attribute [local instance] coefficientAlgebra coefficientScalarTower

open Langlands.DeligneFormalSpace in
/-- A finite tuple acquires roots of any common positive degree in an affine fppf cover. -/
private theorem exists_fppf_roots (m : ℕ) [NeZero m] (A : CommAlgCat.{v} R)
    (y : σ → A) (s : Finset σ) :
    ∃ (B : CommAlgCat.{v} R) (φ : A ⟶ B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧
        ∀ i ∈ s, ∃ z : B, z ^ m = φ.hom (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨A, 𝟙 A, ?_, ?_, by simp⟩
    · rw [CommAlgCat.hom_id]
      exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id
    · rw [CommAlgCat.hom_id]
      exact AlgHom.FinitePresentation.id R A
  | @insert i s _ ih =>
    obtain ⟨B, φ, hφff, hφfp, hs⟩ := ih
    let a := φ.hom (y i)
    let C := CommAlgCat.of R (PiAlgebra m a)
    let ψ : B ⟶ C := CommAlgCat.ofHom (AdjoinRoot.ofAlgHom R (piRelation m a))
    have hψff : ψ.hom.toRingHom.FaithfullyFlat := by
      change (algebraMap B (PiAlgebra m a)).FaithfullyFlat
      exact RingHom.faithfullyFlat_algebraMap_iff.mpr
        (Module.FaithfullyFlat.of_linearEquiv _ _ (PiAlgebra.basis m a).repr)
    have hψfp : ψ.hom.FinitePresentation := by
      change (algebraMap B (PiAlgebra m a)).FinitePresentation
      rw [RingHom.finitePresentation_algebraMap]
      infer_instance
    refine ⟨C, φ ≫ ψ, ?_, ?_, ?_⟩
    · rw [CommAlgCat.hom_comp]
      exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hφff hψff
    · rw [CommAlgCat.hom_comp]
      exact hψfp.comp hφfp
    · intro j hj
      rw [CommAlgCat.hom_comp, AlgHom.comp_apply]
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨PiAlgebra.pi m a, PiAlgebra.pi_pow⟩
      · obtain ⟨z, hz⟩ := hs j hj
        exact ⟨ψ.hom z, by rw [← map_pow, hz]⟩

variable [Finite σ] {M : ModuleLaw O R σ}
variable (p n : ℕ) [ExpChar R p] (θ : R →ₐ[O] R)
variable (hθ : θ.toRingHom = iterateFrobenius R p n)

private theorem coord_frobeniusHom {A : CommAlgCat.{v} R} (x : M.AlgebraPoint A) (i : σ) :
    coord (M.map θ) ((M.frobeniusHom p n θ hθ).onAlgebraPoints x) i =
      coord M x i ^ (p ^ n) := by
  let point : SeriesPoint A σ Empty := x
  change MvPowerSeries.constantCoeff ((SeriesPoint.eval
    ((CoordinateMap.frobeniusPow (R := R) p n).map (algebraMap R A)) point).val i) =
      MvPowerSeries.constantCoeff (point.val i) ^ (p ^ n)
  rw [SeriesPoint.eval_val, CoordinateMap.map_series, CoordinateMap.frobeniusPow_series,
    map_pow, MvPowerSeries.map_X, MvPowerSeries.subst_pow point.property,
    MvPowerSeries.subst_X point.property, map_pow]

private theorem frobeniusHom_locallySurjective :
    (M.frobeniusHom p n θ hθ).IsFppfLocallySurjective := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : NeZero (p ^ n) := ⟨pow_ne_zero n (expChar_ne_zero R p)⟩
  intro A y
  obtain ⟨B, φ, hφff, hφfp, hroots⟩ :=
    exists_fppf_roots (p ^ n) A (coord (M.map θ) y) Finset.univ
  choose z hz using fun i => hroots i (Finset.mem_univ i)
  let x : M.AlgebraPoint B := (M.algebraPointEquiv B).symm ⟨z, fun i => by
    apply IsNilpotent.of_pow (m := p ^ n)
    rw [hz]
    exact (coord_isNilpotent y i).map φ.hom.toRingHom⟩
  refine ⟨B, φ, hφff, hφfp, x, ext_coord fun i => ?_⟩
  have hx : coord M x i = z i :=
    congrArg (fun t => t.val i) ((M.algebraPointEquiv B).apply_symm_apply _)
  rw [coord_frobeniusHom, coord_algebraMapPoints, hx, hz]

/-- A sufficiently large scalar power factors in both directions through actual Frobenius. -/
private theorem frobeniusHom_exists_scalar_factor {π : O} (hM : M.IsPiPowerTorsion π) :
    ∃ (j : ℕ) (g : Hom (M.map θ) M),
      g.comp (M.frobeniusHom p n θ hθ) = M.scalarHom (π ^ j) ∧
      (M.frobeniusHom p n θ hθ).comp g = (M.map θ).scalarHom (π ^ j) := by
  let f := M.frobeniusHom p n θ hθ
  have hlift := frobeniusHom_locallySurjective (M := M) p n θ hθ
  obtain ⟨j, hj⟩ := hM (truncAlg R σ (p ^ n)) (truncPoint M (p ^ n))
  obtain ⟨g, hgf⟩ := Hom.exists_comp_eq (f := f) (h := M.scalarHom (π ^ j)) hlift (by
    intro A x hx
    have hp (i : σ) : coord M x i ^ (p ^ n) = 0 := by
      rw [← coord_frobeniusHom p n θ hθ,
        show (M.frobeniusHom p n θ hθ).onAlgebraPoints x = 0 from hx,
        coord_zero]
    rw [scalarHom_onAlgebraPoints]
    have h := congrArg (M.algebraMapPoints (truncLift x hp)) hj
    simpa only [map_smul, truncLift_point, map_zero] using h)
  refine ⟨j, g, hgf, hlift.comp_right_cancel ?_⟩
  rw [Hom.comp_assoc, hgf, Hom.comp_scalarHom]

end Langlands.FormalGroup.ModuleLaw

namespace Langlands.FormalGroup.LocalDivision.SpecialModule

open ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}

/-- Actual relative Frobenius is invertible in the global full-order rational Hom. -/
theorem relativeFrobeniusQuasiIsogeny
    (Φ : HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    (p n : ℕ) [ExpChar κ p] : RelativeFrobeniusQuasiIsogenyStatement Φ p n := by
  intro θ hθ
  let f := Φ.val.order.frobeniusHom p n θ hθ
  let z := OrderAction.RationalHom.ofHom (F := K) f
  obtain ⟨j, g, hgf, hfg⟩ :=
    frobeniusHom_exists_scalar_factor p n θ hθ Φ.property.2.piDivisible.torsion
  change g.comp f.val = Φ.val.formalModule.scalarHom (π ^ j) at hgf
  change f.val.comp g = (Φ.val.formalModule.map θ).scalarHom (π ^ j) at hfg
  let c := (algebraMap 𝒪[K] K π) ^ j
  have hc : c ≠ 0 := pow_ne_zero j fun h =>
    Φ.property.1.ne_zero (IsFractionRing.injective 𝒪[K] K (by simpa using h))
  let q : QuasiIsogeny K Φ.val.formalModule (Φ.val.formalModule.map θ) := {
    hom := z.val
    inv := c⁻¹ • RationalHom.ofHom g
    inv_hom := by
      change RationalHom.comp (c⁻¹ • RationalHom.ofHom g) (RationalHom.ofHom f.val) = _
      rw [RationalHom.smul_comp, ← RationalHom.ofHom_comp, hgf,
        RationalHom.ofHom_scalarHom, map_pow]
      exact inv_smul_smul₀ hc _
    hom_inv := by
      change RationalHom.comp (RationalHom.ofHom f.val) (c⁻¹ • RationalHom.ofHom g) = _
      rw [RationalHom.comp_smul, ← RationalHom.ofHom_comp, hfg,
        RationalHom.ofHom_scalarHom, map_pow]
      exact inv_smul_smul₀ hc _ }
  exact ⟨OrderAction.QuasiIsogeny.ofModuleQuasiIsogeny q z.commutes,
    OrderAction.RationalHom.ext rfl⟩

end Langlands.FormalGroup.LocalDivision.SpecialModule

import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedChamberStatement
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIntegralTwistStatement
import Langlands.GroupScheme.IntegralModel.IntegralPointDescent
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.Galois.Local.SpectralProof

/-! # The integral twist from a Galois-stable chamber -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

/-! ### Integral points over the maximal unramified extension -/

section Integrality

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

/-- Elements of the valuation ring of the maximal unramified extension are integral over
`𝒪[F]`. -/
theorem isIntegral_of_mem_fixedFieldIntegers (x : fixedFieldIntegers F) :
    IsIntegral 𝒪[F] (x : inertiaFixedField F) := by
  have hmem : (x : inertiaFixedField F) ∈ extensionIntegers F (inertiaFixedField F) := by
    rw [← fixedFieldIntegers_eq]
    exact x.property
  rw [LocalUnramified.isIntegral_iff_baseIntegers F (inertiaFixedField F)]
  exact spectral_integral F (inertiaFixedField F) ⟨_, hmem⟩

end Integrality

section IntegralCoordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A coefficient point over the maximal unramified extension whose rational point lies in
the image of the integral points of the unramified base change of `M` has integral generic
model coordinates. -/
theorem IntegralModel.hasIntegralCoordinates_of_mem_baseChangeUnramified
    (M : IntegralModel ↥𝒪[F] F G)
    (p : G.affinePoints (CommAlgCat.of F (inertiaFixedField F)))
    (hp : (baseChangeCoeffEquiv F (inertiaFixedField F) G).symm p ∈
      M.baseChangeUnramified.integralPoints) :
    M.HasIntegralCoordinates (inertiaFixedField F) p := by
  let _ : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
    Valuation.HasExtension.instAlgebraInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  have : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  have h₁ : p ∈ M.baseChangeUnramified.coefficientIntegralPoints F (inertiaFixedField F) :=
    (M.baseChangeUnramified.mem_coefficientIntegralPoints_iff F (inertiaFixedField F) p).mpr hp
  change p ∈ (M.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).coefficientIntegralPoints
    F (inertiaFixedField F) at h₁
  rw [M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates (fixedFieldIntegers F)
    (inertiaFixedField F)] at h₁
  intro a
  obtain ⟨y, hy⟩ := h₁ a
  rw [← hy]
  exact isIntegral_of_mem_fixedFieldIntegers y

end IntegralCoordinates

/-! ### Twisted stability of a chamber -/

/-- If `f` is a map intertwining the action of `H` through `s`, `Y₀` is `f`-stable, `Y = g • Y₀`,
and `Y` is stable under the twisted map `y ↦ c • f y`, then `Y₀` is stable under translation by
`g⁻¹ * c * s g`. -/
theorem image_smul_eq_self_of_twisted_stable {H X : Type*} [Group H] [MulAction H X]
    (f : X → X) (s : H → H) (hf : ∀ (g : H) (z : X), f (g • z) = s g • f z) {Y₀ Y : Set X} {g c : H}
    (hY₀ : f '' Y₀ = Y₀) (hg : (g • ·) '' Y₀ = Y) (hY : (fun y => c • f y) '' Y = Y) :
    ((g⁻¹ * c * s g) • ·) '' Y₀ = Y₀ := by
  have hpt : ∀ y, (g⁻¹ * c * s g) • f y = g⁻¹ • (c • f (g • y)) := by
    intro y
    rw [hf, mul_assoc, mul_smul, mul_smul]
  calc ((g⁻¹ * c * s g) • ·) '' Y₀ = ((g⁻¹ * c * s g) • ·) '' (f '' Y₀) := by rw [hY₀]
    _ = (g⁻¹ • ·) '' ((fun y => c • f y) '' ((g • ·) '' Y₀)) := by
        simp only [Set.image_image, hpt]
    _ = (g⁻¹ • ·) '' Y := by rw [hg, hY]
    _ = Y₀ := by
        rw [← hg, Set.image_image]
        simp only [inv_smul_smul, Set.image_id']

/-! ### The reduction -/

/-- **Reduction of the integral twist to the chamber input.** The chamber statement
`LocalSimplyConnectedUnramifiedChamberStatement` implies the integral-twist statement
`LocalSimplyConnectedUnramifiedIntegralTwistStatement`. -/
def LocalSimplyConnectedUnramifiedChamberReductionStatement : Prop :=
  LocalSimplyConnectedUnramifiedChamberStatement.{u} →
    LocalSimplyConnectedUnramifiedIntegralTwistStatement.{u}

set_option maxHeartbeats 800000 in
/-- Proof of the reduction: inflate the cocycle to `Gal(L/F)`, take a chamber stable under the
twisted action, move it to `Y₀`, and read off integrality from the stabilizer of `Y₀`. -/
theorem localSimplyConnectedUnramifiedChamberReduction :
    LocalSimplyConnectedUnramifiedChamberReductionStatement.{u} := by
  intro hC F _ _ _ _ G _ hG
  obtain ⟨C, D, M, Y₀, hsmooth, hconn, -, hY₀, hstab, htrans, htwist⟩ := hC F G hG
  refine ⟨M, hsmooth, hconn, ?_⟩
  intro E _ _ _ _ _ _ c hc
  let Φ := baseChangeCoeffEquiv F (inertiaFixedField F) G
  let c' : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G) := fun σ =>
    Φ.symm (GaloisPoint.relativeExtend F E (inertiaFixedField F) G (c (σ.restrictNormal E)))
  -- the inflated cocycle is a crossed homomorphism for the rational Galois action
  have hc' : ∀ σ τ, c' (σ * τ) =
      c' σ * rationalConjugate F (inertiaFixedField F) G σ (c' τ) := by
    intro σ τ
    have hmul : (σ * τ).restrictNormal E = σ.restrictNormal E * τ.restrictNormal E :=
      map_mul (AlgEquiv.restrictNormalHom (K₁ := inertiaFixedField F) E) σ τ
    apply Φ.injective
    simp only [c', Φ, map_mul, MulEquiv.apply_symm_apply, baseChangeCoeffEquiv_rationalConjugate]
    rw [hmul, hc, map_mul, GaloisPoint.relativeExtend_conjugate]
  -- it is trivial on the fixing subgroup of the image of `E`
  have hc_one : c 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, GaloisPoint.conjugate_one] at h
    exact mul_eq_left.mp h.symm
  have hfin : ∃ E' : IntermediateField F (inertiaFixedField F), FiniteDimensional F E' ∧
      ∀ σ ∈ E'.fixingSubgroup, c' σ = 1 := by
    refine ⟨(IsScalarTower.toAlgHom F E (inertiaFixedField F)).fieldRange,
      LinearEquiv.finiteDimensional
        (AlgHom.equivFieldRange (IsScalarTower.toAlgHom F E (inertiaFixedField F))).toLinearEquiv,
      ?_⟩
    intro σ hσ
    have hres : σ.restrictNormal E = 1 := by
      refine AlgEquiv.ext fun y => (algebraMap E (inertiaFixedField F)).injective ?_
      rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      exact (mem_fixingSubgroup_iff _).mp hσ (algebraMap E (inertiaFixedField F) y) ⟨y, rfl⟩
    simp only [c', hres, hc_one, map_one]
  obtain ⟨Y, hY, hYstable⟩ := htwist c' hc' hfin
  obtain ⟨g, hg⟩ := htrans Y hY
  refine ⟨Φ g, fun σ => ?_⟩
  have hY₀' : D.action σ '' Y₀ = Y₀ := hY₀ σ
  have hk := image_smul_eq_self_of_twisted_stable (D.action σ)
    (rationalConjugate F (inertiaFixedField F) G σ) (D.action_smul σ) hY₀' hg (hYstable σ)
  have hkmem : g⁻¹ * c' σ * rationalConjugate F (inertiaFixedField F) G σ g ∈
      M.baseChangeUnramified.integralPoints := (hstab _).mpr hk
  have hint := M.hasIntegralCoordinates_of_mem_baseChangeUnramified
    (Φ (g⁻¹ * c' σ * rationalConjugate F (inertiaFixedField F) G σ g))
    (by rw [MulEquiv.symm_apply_apply]; exact hkmem)
  have hc'σ : Φ (c' σ) = GaloisPoint.relativeExtend F E (inertiaFixedField F) G
      (c (σ.restrictNormal E)) := Φ.apply_symm_apply _
  have hΦσ : Φ (rationalConjugate F (inertiaFixedField F) G σ g) =
      GaloisPoint.conjugate F (inertiaFixedField F) G σ (Φ g) :=
    baseChangeCoeffEquiv_rationalConjugate F (inertiaFixedField F) G σ g
  have hinv : Φ g⁻¹ = (Φ g)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul Φ, inv_mul_cancel, map_one]
  rw [← hc'σ, ← hΦσ, ← hinv, ← map_mul Φ, ← map_mul Φ]
  exact hint

end Langlands.GroupScheme

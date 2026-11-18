import Langlands.GroupScheme.Cohomology.FlatRangeDescent
import Langlands.GroupScheme.Cohomology.RestrictedTestEvaluation
import Langlands.GroupScheme.Cohomology.MultiplicativeTypeVanishingStatement
import Langlands.GroupScheme.Cohomology.AffineCochainCoordinates
import Langlands.GroupScheme.Cohomology.BaseChange
import Langlands.GroupScheme.Cohomology.SourceTransport
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineChart
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry

/-! # Low-degree cohomology vanishing for groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Cohomology

open RelativeMultiplicativeType

/-- Over an affine base, a group of multiplicative type is split by flat algebras
whose spectra cover every point of the base. -/
theorem exists_flat_isDiagonalizable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}
    (hH : IsMultiplicativeType H) (p : PrimeSpectrum R) :
    ∃ K : CommAlgCat.{u} R, Module.Flat R K ∧
      (∃ q : PrimeSpectrum K, PrimeSpectrum.comap (algebraMap R K) q = p) ∧
        IsDiagonalizable ((GroupScheme.baseChange (algebraBaseMap R K)).obj H) := by
  obtain ⟨R₀, j, hj, ⟨t, ht⟩, -, -, R', φ, hφ, -, hdiag⟩ :=
    hH.exists_affine_chart (show Spec R from p)
  let ψ : R ⟶ R₀ := Spec.preimage j
  have hψ : Spec.map ψ = j := Spec.map_preimage j
  let : Algebra R R' := (ψ ≫ φ).hom.toAlgebra
  refine ⟨CommAlgCat.of R R', ?_, ?_, ?_⟩
  · have h1 : ψ.hom.Flat := by
      have : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
      exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 this
    have h2 : φ.hom.Flat := hφ.flat
    exact RingHom.Flat.comp h1 h2
  · obtain ⟨q, hq⟩ :=
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1 hφ).2 t
    refine ⟨q, ?_⟩
    have ht' : (Spec.map ψ).base t = p := by rw [hψ]; exact ht
    rw [← ht', ← hq]
    rfl
  · have hb : algebraBaseMap R (CommAlgCat.of R R') = Spec.map φ ≫ j := by
      rw [← hψ, ← Spec.map_comp]
      rfl
    rw [hb]
    exact hdiag

section Differentials

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} [IsAffineHom H.X.hom]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The degree-zero differential on universal coordinates: `m ↦ g • (1 ⊗ m) - 1 ⊗ m`
at the universal source point `g`. -/
def zeroDifferential (ρ : ModuleRepresentation M H) :
    M →ₗ[R] ModulePoints M (Lie.coordinateAlgebra H) :=
  (ρ.action _ (genericPoint H)).toLinearMap.restrictScalars R ∘ₗ
      constantPoints (Lie.coordinateAlgebra H) -
    constantPoints (Lie.coordinateAlgebra H)

/-- A one-cochain whose universal value lies in the range of the degree-zero
differential is a coboundary of an actual base-module element. -/
theorem OneCochain.isCoboundary_of_mem_range (ρ : ModuleRepresentation M H)
    (c : OneCochain M H)
    (hc : c.value _ (genericPoint H) ∈ LinearMap.range (zeroDifferential ρ)) :
    c.IsCoboundary ρ := by
  obtain ⟨m, hm⟩ := hc
  exact (oneCoboundary_iff_generic H M ρ c).2 ⟨m, hm.symm⟩

/-- The degree-one differential on universal coordinates: a coordinate tensor `w`
of a one-cochain `b` goes to `g₁ • b(g₂) + b(g₁) - b(g₁g₂)` at the independent
universal pair `(g₁, g₂)`. -/
def oneDifferential (ρ : ModuleRepresentation M H) :
    ModulePoints M (Lie.coordinateAlgebra H) →ₗ[R] ModulePoints M (pairCoordinateAlgebra H) :=
  (ρ.action _ (genericFirst H)).toLinearMap.restrictScalars R ∘ₗ
      modulePointMap M (pointSpecialization H (genericSecond H)) +
    modulePointMap M (pointSpecialization H (genericFirst H)) -
    modulePointMap M (pointSpecialization H (genericFirst H * genericSecond H))

/-- A two-cochain whose universal value lies in the range of the degree-one
differential is the coboundary of a natural one-cochain. -/
theorem TwoCochain.isCoboundary_of_mem_range (ρ : ModuleRepresentation M H)
    (c : TwoCochain M H)
    (hc : c.value _ (genericFirst H) (genericSecond H) ∈
      LinearMap.range (oneDifferential ρ)) :
    c.IsCoboundary ρ := by
  obtain ⟨w, hw⟩ := hc
  refine (twoCoboundary_iff_generic H M ρ c).2 ⟨oneCochainOfCoordinates H M w, ?_⟩
  change _ + modulePointMap M (pointSpecialization H _) w =
    ρ.action _ _ (modulePointMap M (pointSpecialization H _) w) +
      modulePointMap M (pointSpecialization H _) w
  rw [← hw]
  simp only [oneDifferential, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  abel

end Differentials

section Local

attribute [local instance] restrictedTestAlgebra restrictedTestTower

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} [IsAffineHom H.X.hom]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- If the base change of `H` to `K` has vanishing low-degree cohomology, then the
universal value of a one-cocycle lies in the range of the degree-zero differential
after tensoring with `K`. -/
theorem oneCocycle_mem_range_lTensor (K : CommAlgCat.{u} R)
    (hK : HasVanishingLowDegreeCohomology ((GroupScheme.baseChange (algebraBaseMap R K)).obj H))
    (ρ : ModuleRepresentation M H) (c : OneCochain M H) (hc : c.IsCocycle ρ) :
    (1 : K) ⊗ₜ[R] c.value _ (genericPoint H) ∈
      LinearMap.range ((zeroDifferential ρ).lTensor K) := by
  obtain ⟨m', hm'⟩ := (hK _ (ρ.baseChange K)).1 (c.baseChange K) (c.baseChange_isCocycle K ρ hc)
  let P := Lie.coordinateAlgebra H
  let A := tensorTest K P
  let φ := tensorTestInclusion K P
  let x := (Lie.affineBaseChangeEquiv R K H A).symm (H.affinePointMap φ (genericPoint H))
  have e := congrArg (scalarExtensionCancel K M A) (hm' A x)
  simp only [OneCochain.baseChange, ModuleRepresentation.baseChange,
    ModuleRepresentation.baseChangeAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, map_sub, LinearEquiv.apply_symm_apply, x,
    MulEquiv.apply_symm_apply] at e
  rw [scalarExtensionCancel_one_tmul φ, ← c.naturality, ← restrictedEval_one_tmul,
    restrictedEval_action, ← map_sub] at e
  refine ⟨m', restrictedEval_tensorTestInclusion_injective K P ?_⟩
  rw [e]
  congr 1
  simp only [zeroDifferential, LinearMap.lTensor_sub, LinearMap.lTensor_comp,
    LinearMap.sub_apply, LinearMap.comp_apply]
  rfl

/-- If the base change of `H` to `K` has vanishing low-degree cohomology, then the
universal value of a two-cocycle lies in the range of the degree-one differential
after tensoring with `K`. -/
theorem twoCocycle_mem_range_lTensor (K : CommAlgCat.{u} R)
    (hK : HasVanishingLowDegreeCohomology ((GroupScheme.baseChange (algebraBaseMap R K)).obj H))
    (ρ : ModuleRepresentation M H) (c : TwoCochain M H) (hc : c.IsCocycle ρ) :
    (1 : K) ⊗ₜ[R] c.value _ (genericFirst H) (genericSecond H) ∈
      LinearMap.range ((oneDifferential ρ).lTensor K) := by
  obtain ⟨b', hb'⟩ := (hK _ (ρ.baseChange K)).2 (c.baseChange K) (c.baseChange_isCocycle K ρ hc)
  let P := Lie.coordinateAlgebra H
  let A₁ := tensorTest K P
  let φ₁ := tensorTestInclusion K P
  let x₁ := (Lie.affineBaseChangeEquiv R K H A₁).symm (H.affinePointMap φ₁ (genericPoint H))
  have hx₁ : Lie.affineBaseChangeEquiv R K H A₁ x₁ = H.affinePointMap φ₁ (genericPoint H) :=
    MulEquiv.apply_symm_apply _ _
  obtain ⟨w', hw'⟩ := restrictedEval_tensorTestInclusion_surjective (M := M) K P
    (scalarExtensionCancel K M A₁ (b'.value A₁ x₁))
  -- The primitive `b'` is determined by its value at the universal point over `K ⊗ P`.
  have claim : ∀ (A : CommAlgCat.{u} K)
      (h' : ((GroupScheme.baseChange (algebraBaseMap R K)).obj H).affinePoints A),
      scalarExtensionCancel K M A (b'.value A h') =
        restrictedEval (pointSpecialization H (Lie.affineBaseChangeEquiv R K H A h')) w' := by
    intro A h'
    let F := tensorTestLift (pointSpecialization H (Lie.affineBaseChangeEquiv R K H A h'))
    have hF : ((GroupScheme.baseChange (algebraBaseMap R K)).obj H).affinePointMap F x₁ = h' := by
      apply (Lie.affineBaseChangeEquiv R K H A).injective
      refine (Lie.affineBaseChangeEquiv_naturality R K H F.hom x₁).trans ?_
      change H.affinePointMap (restrictedTestMap K F)
        (Lie.affineBaseChangeEquiv R K H A₁ x₁) = _
      rw [hx₁, ← MonoidHom.comp_apply, ← affinePointMap_comp, tensorTestInclusion_comp_lift,
        genericPoint_specialize]
    conv_lhs => rw [← hF]
    rw [← b'.naturality, scalarExtensionCancel_naturality, ← hw',
      restrictedEval_restrictedTestMap, tensorTestInclusion_comp_lift]
  let O₂ := pairCoordinateAlgebra H
  let A₂ := tensorTest K O₂
  let φ₂ := tensorTestInclusion K O₂
  let k₁ := H.affinePointMap φ₂ (genericFirst H)
  let k₂ := H.affinePointMap φ₂ (genericSecond H)
  have hb := congrArg (scalarExtensionCancel K M A₂)
    (hb' A₂ ((Lie.affineBaseChangeEquiv R K H A₂).symm k₁)
      ((Lie.affineBaseChangeEquiv R K H A₂).symm k₂))
  simp only [TwoCochain.baseChange, ModuleRepresentation.baseChange,
    ModuleRepresentation.baseChangeAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, map_add, LinearEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply] at hb
  rw [claim, claim, claim] at hb
  simp only [map_mul, MulEquiv.apply_symm_apply, k₁, k₂] at hb
  rw [← map_mul, pointSpecialization_naturality, pointSpecialization_naturality,
    pointSpecialization_naturality, ← restrictedEval_lTensor, ← restrictedEval_lTensor,
    ← restrictedEval_lTensor, restrictedEval_action, ← c.naturality,
    ← restrictedEval_one_tmul] at hb
  rw [← map_add, ← map_add] at hb
  have hb₃ := restrictedEval_tensorTestInclusion_injective K O₂ hb
  refine ⟨w', Eq.trans ?_ (eq_sub_of_add_eq hb₃).symm⟩
  simp only [oneDifferential, LinearMap.lTensor_sub, LinearMap.lTensor_add,
    LinearMap.lTensor_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]
  rfl

end Local

/-- **Low-degree cohomology vanishing for groups of multiplicative type.**
For every commutative ring `R` and every group of multiplicative type `H` over
`Spec R`, every regular one-cocycle with coefficients in an arbitrary `R`-module is
the coboundary of a base-module element, and every regular two-cocycle is the
coboundary of a natural one-cochain (Conrad, Appendix B.2, Remark B.2.4). -/
theorem multiplicativeTypeLowDegreeVanishing :
    MultiplicativeTypeLowDegreeVanishingStatement.{u} := by
  intro R H hH
  have := hH.isAffineHom
  have hloc : ∀ p : PrimeSpectrum R, ∃ K : CommAlgCat.{u} R, Module.Flat R K ∧
      (∃ q : PrimeSpectrum K, PrimeSpectrum.comap (algebraMap R K) q = p) ∧
        HasVanishingLowDegreeCohomology ((GroupScheme.baseChange (algebraBaseMap R K)).obj H) := by
    intro p
    obtain ⟨K, hf, hq, hd⟩ := exists_flat_isDiagonalizable hH p
    exact ⟨K, hf, hq, hasVanishingLowDegreeCohomology_of_isDiagonalizable hd⟩
  intro M _ _ ρ
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · apply OneCochain.isCoboundary_of_mem_range
    apply mem_range_of_flat_cover
    intro p
    obtain ⟨K, hf, hq, hK⟩ := hloc p
    exact ⟨K, inferInstance, inferInstance, hf, hq, oneCocycle_mem_range_lTensor K hK ρ c hc⟩
  · apply TwoCochain.isCoboundary_of_mem_range
    apply mem_range_of_flat_cover
    intro p
    obtain ⟨K, hf, hq, hK⟩ := hloc p
    exact ⟨K, inferInstance, inferInstance, hf, hq, twoCocycle_mem_range_lTensor K hK ρ c hc⟩

end Langlands.GroupScheme.Cohomology

import Langlands.Geometry.Manifold.SmoothGroupConjugationLie
import Langlands.Automorphic.GroupSchemeFiniteVectorDifferential
import Langlands.Automorphic.GroupSchemeCuspidalForms
import Langlands.Automorphic.GroupSchemeFormDifferential

/-! # Infinite right translation of the actual group-scheme forms

The adjoint action of the infinite adelic points on the actual enveloping algebra, the
covariance `R(g) D_a = D_(Ad(g) a) R(g)`, and the resulting stability of the actual forms,
uniform forms and cusp forms under right translation by a specified infinite subgroup. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Algebra.ComplexLieExtension

/-- The complex-linear extension of a real Lie algebra homomorphism. -/
def extendLieHom {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']
    (f : L →ₗ⁅ℝ⁆ L') : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ ℂ ⊗[ℝ] L' :=
  { LinearMap.baseChange ℂ f.toLinearMap with
    map_lie' := by
      intro x y
      change LinearMap.baseChange ℂ f.toLinearMap ⁅x, y⁆ =
        ⁅LinearMap.baseChange ℂ f.toLinearMap x, LinearMap.baseChange ℂ f.toLinearMap y⁆
      induction x using TensorProduct.inductionOn with
      | tmul a X =>
        induction y using TensorProduct.inductionOn with
        | tmul b Y =>
          simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.baseChange_tmul,
            LieHom.coe_toLinearMap, LieHom.map_lie]
        | add y₁ y₂ h₁ h₂ => rw [LieRing.lie_add, map_add, h₁, h₂, map_add, lie_add]
      | add x₁ x₂ h₁ h₂ => rw [LieRing.add_lie, map_add, h₁, h₂, map_add, add_lie] }

@[simp]
theorem extendLieHom_tmul {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L']
    [LieAlgebra ℝ L'] (f : L →ₗ⁅ℝ⁆ L') (z : ℂ) (X : L) :
    extendLieHom f (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] f X := rfl

end Langlands.Algebra.ComplexLieExtension

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local instance infiniteTranslationAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The actual adjoint automorphism of the enveloping algebra: the enveloping extension of
the complexified tangent conjugation. -/
def adelicEnvelopingConjugation (g : InfiniteAdelicGroupPoints F G) :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ] AdelicEnvelopingAlgebra F G hsmooth := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (Langlands.Algebra.ComplexLieExtension.extendLieHom
      (groupTangentConjugationLieEquiv 𝓘(ℝ, smoothModel F d) g).toLieHom))

/-- On pure generators the adjoint automorphism is the tangent conjugation. -/
theorem adelicEnvelopingConjugation_ι_tmul (g : InfiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    let := smoothLieGroup F G hsmooth
    let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    ∀ (z : ℂ) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
      adelicEnvelopingConjugation F G hsmooth g (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X)) =
        UniversalEnvelopingAlgebra.ι ℂ
          (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
          (z ⊗ₜ[ℝ] adelicTangentConjugation F G hsmooth g X) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  dsimp only
  intro z X
  unfold adelicEnvelopingConjugation
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    Langlands.Algebra.ComplexLieExtension.extendLieHom_tmul]
  rfl

theorem adelicTangentConjugation_mul_apply (g k : InfiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ X : smoothModel F d,
      adelicTangentConjugation F G hsmooth (g * k) X =
        adelicTangentConjugation F G hsmooth g (adelicTangentConjugation F G hsmooth k X) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  intro X
  exact congrArg (fun T : smoothModel F d →L[ℝ] smoothModel F d => T X)
    (groupTangentConjugation_mul 𝓘(ℝ, smoothModel F d) g k)

theorem adelicTangentConjugation_one_apply :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ X : smoothModel F d, adelicTangentConjugation F G hsmooth 1 X = X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  intro X
  exact congrArg (fun T : smoothModel F d →L[ℝ] smoothModel F d => T X)
    (groupTangentConjugation_one 𝓘(ℝ, smoothModel F d))

/-- The adjoint automorphisms compose like the group. -/
theorem adelicEnvelopingConjugation_mul (g k : InfiniteAdelicGroupPoints F G) :
    adelicEnvelopingConjugation F G hsmooth (g * k) =
      (adelicEnvelopingConjugation F G hsmooth g).comp
        (adelicEnvelopingConjugation F G hsmooth k) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro Z
  change adelicEnvelopingConjugation F G hsmooth (g * k) (UniversalEnvelopingAlgebra.ι ℂ Z) =
    adelicEnvelopingConjugation F G hsmooth g
      (adelicEnvelopingConjugation F G hsmooth k (UniversalEnvelopingAlgebra.ι ℂ Z))
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    rw [adelicEnvelopingConjugation_ι_tmul, adelicEnvelopingConjugation_ι_tmul,
      adelicEnvelopingConjugation_ι_tmul, adelicTangentConjugation_mul_apply]
  | add X Y hX hY => simp only [map_add, hX, hY]

theorem adelicEnvelopingConjugation_one :
    adelicEnvelopingConjugation F G hsmooth 1 = AlgHom.id ℂ _ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro Z
  change adelicEnvelopingConjugation F G hsmooth 1 (UniversalEnvelopingAlgebra.ι ℂ Z) =
    UniversalEnvelopingAlgebra.ι ℂ Z
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    rw [adelicEnvelopingConjugation_ι_tmul, adelicTangentConjugation_one_apply]
  | add X Y hX hY => simp only [map_add, hX, hY]

/-- The adjoint automorphism as an algebra automorphism, with inverse `Ad(g⁻¹)`. -/
def adelicEnvelopingConjugationEquiv (g : InfiniteAdelicGroupPoints F G) :
    AdelicEnvelopingAlgebra F G hsmooth ≃ₐ[ℂ] AdelicEnvelopingAlgebra F G hsmooth :=
  AlgEquiv.ofAlgHom (adelicEnvelopingConjugation F G hsmooth g)
    (adelicEnvelopingConjugation F G hsmooth g⁻¹)
    (by rw [← adelicEnvelopingConjugation_mul, mul_inv_cancel, adelicEnvelopingConjugation_one])
    (by rw [← adelicEnvelopingConjugation_mul, inv_mul_cancel, adelicEnvelopingConjugation_one])

@[simp]
theorem adelicEnvelopingConjugationEquiv_apply (g : InfiniteAdelicGroupPoints F G)
    (a : AdelicEnvelopingAlgebra F G hsmooth) :
    adelicEnvelopingConjugationEquiv F G hsmooth g a =
      adelicEnvelopingConjugation F G hsmooth g a :=
  rfl

@[simp]
theorem adelicEnvelopingConjugationEquiv_symm_apply (g : InfiniteAdelicGroupPoints F G)
    (a : AdelicEnvelopingAlgebra F G hsmooth) :
    (adelicEnvelopingConjugationEquiv F G hsmooth g).symm a =
      adelicEnvelopingConjugation F G hsmooth g⁻¹ a := rfl

/-- Covariance: positive infinite translation carries every actual enveloping derivative
to the derivative by the adjoint image. -/
theorem finitePlotSmoothRightAction_actualAdelicEnvelopingAction
    (g : InfiniteAdelicGroupPoints F G) (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : FinitePlotSmoothRationalFunctions F G) :
    finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g)
        (actualAdelicEnvelopingAction F G hsmooth a f) =
      actualAdelicEnvelopingAction F G hsmooth (adelicEnvelopingConjugation F G hsmooth g a)
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap z =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
  | «ι» Z =>
    change finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g)
        (actualAdelicEnvelopingAction F G hsmooth (UniversalEnvelopingAlgebra.ι ℂ Z) f) =
      actualAdelicEnvelopingAction F G hsmooth
        (adelicEnvelopingConjugation F G hsmooth g (UniversalEnvelopingAlgebra.ι ℂ Z))
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f)
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      rw [adelicEnvelopingConjugation_ι_tmul, actualAdelicEnvelopingAction_generator,
        actualAdelicEnvelopingAction_generator, actualAdelicComplexDifferential_tmul,
        actualAdelicComplexDifferential_tmul]
      simp only [LinearMap.smul_apply, map_smul]
      rw [finitePlotSmoothDifferentialAction_infiniteRightAction]
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply]
      rw [hX, hY]
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hx, hy]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]

theorem adelicEnvelopingConjugation_apply_inv (g : InfiniteAdelicGroupPoints F G)
    (a : AdelicEnvelopingAlgebra F G hsmooth) :
    adelicEnvelopingConjugation F G hsmooth g (adelicEnvelopingConjugation F G hsmooth g⁻¹ a) =
      a :=
  (adelicEnvelopingConjugationEquiv F G hsmooth g).apply_symm_apply a

/-- The adjoint automorphism preserves the center of the enveloping algebra. -/
theorem adelicEnvelopingConjugation_mem_center (g : InfiniteAdelicGroupPoints F G)
    {z : AdelicEnvelopingAlgebra F G hsmooth} (hz : z ∈ AdelicEnvelopingCenter F G hsmooth) :
    adelicEnvelopingConjugation F G hsmooth g z ∈ AdelicEnvelopingCenter F G hsmooth := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro b
  rw [← adelicEnvelopingConjugation_apply_inv F G hsmooth g b, ← map_mul, ← map_mul, hz]

/-- The adjoint automorphism restricted to the center. -/
def adelicCenterConjugation (g : InfiniteAdelicGroupPoints F G)
    (z : AdelicEnvelopingCenter F G hsmooth) : AdelicEnvelopingCenter F G hsmooth :=
  ⟨adelicEnvelopingConjugation F G hsmooth g z.val,
    adelicEnvelopingConjugation_mem_center F G hsmooth g z.property⟩

@[simp]
theorem adelicCenterConjugation_val (g : InfiniteAdelicGroupPoints F G)
    (z : AdelicEnvelopingCenter F G hsmooth) :
    (adelicCenterConjugation F G hsmooth g z).val =
      adelicEnvelopingConjugation F G hsmooth g z.val := rfl

variable (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- Positive infinite translation preserves finiteness of the actual center orbit. -/
theorem IsAdelicCenterFinite.infiniteRightAction {f : FinitePlotSmoothRationalFunctions F G}
    (hf : IsAdelicCenterFinite F G hsmooth hcalc f) (g : InfiniteAdelicGroupPoints F G) :
    IsAdelicCenterFinite F G hsmooth hcalc
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f) := by
  have hcov (z : AdelicEnvelopingCenter F G hsmooth) (h : FinitePlotSmoothRationalFunctions F G) :
      finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g)
          (adelicCenterAction F G hsmooth hcalc z h) =
        adelicCenterAction F G hsmooth hcalc (adelicCenterConjugation F G hsmooth g z)
          (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) h) :=
    finitePlotSmoothRightAction_actualAdelicEnvelopingAction F G hsmooth g z.val h
  have key : Langlands.FiniteVectors.orbitSpan (adelicCenterAction F G hsmooth hcalc).toMonoidHom
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f) =
    (Langlands.FiniteVectors.orbitSpan (adelicCenterAction F G hsmooth hcalc).toMonoidHom f).map
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g)) := by
    unfold Langlands.FiniteVectors.orbitSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext h
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨adelicCenterConjugation F G hsmooth g⁻¹ z, ?_⟩
      change finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g)
          (adelicCenterAction F G hsmooth hcalc (adelicCenterConjugation F G hsmooth g⁻¹ z) f) =
        adelicCenterAction F G hsmooth hcalc z
          (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f)
      rw [hcov]
      congr 2
      apply Subtype.ext
      exact adelicEnvelopingConjugation_apply_inv F G hsmooth g z.val
    · rintro ⟨z, rfl⟩
      exact ⟨adelicCenterConjugation F G hsmooth g z, (hcov z f).symm⟩
  have : Module.Finite ℂ
      (Langlands.FiniteVectors.orbitSpan (adelicCenterAction F G hsmooth hcalc).toMonoidHom f) := hf
  change Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan
    (adelicCenterAction F G hsmooth hcalc).toMonoidHom
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f))
  rw [key]
  infer_instance

/-- An element of an infinite subgroup preserves finiteness of that subgroup's orbit. -/
theorem IsAdelicInfiniteFinite.subgroupAction (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {f : FinitePlotSmoothRationalFunctions F G} (hf : IsAdelicInfiniteFinite F G Kinf f)
    (k : Kinf) :
    IsAdelicInfiniteFinite F G Kinf (finitePlotSmoothInfiniteSubgroupAction F G Kinf k f) :=
  Langlands.FiniteVectors.IsFiniteVector.action hf k

variable {N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))

/-- Positive infinite translation preserves one shared exponent for all derivatives. -/
theorem HasAdelicUniformPolynomialGrowth.infiniteRightAction (hN : 0 < N)
    {f : FinitePlotSmoothRationalFunctions F G}
    (hf : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f)
    (g : InfiniteAdelicGroupPoints F G) :
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf (adelicEnvelopingConjugation F G hsmooth g⁻¹ a)
  have hn0 (y : AdelicGroupPoints F G) : 0 ≤ RepresentationGrowth.adelicHeight F G rho y :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN y)
  refine ⟨C * RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofInfinite F G g) ^ e,
    mul_nonneg hC (pow_nonneg (hn0 _) e), fun x => ?_⟩
  have hcov := finitePlotSmoothRightAction_actualAdelicEnvelopingAction F G hsmooth g
    (adelicEnvelopingConjugation F G hsmooth g⁻¹ a) f
  rw [adelicEnvelopingConjugation_apply_inv] at hcov
  change ‖evaluate F G (actualAdelicEnvelopingAction F G hsmooth a
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f)).val x‖ ≤ _
  rw [← hcov]
  change ‖evaluate F G (actualAdelicEnvelopingAction F G hsmooth
      (adelicEnvelopingConjugation F G hsmooth g⁻¹ a) f).val
      (x * AdelicGroupPoints.ofInfinite F G g)‖ ≤ _
  calc
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho
        (x * AdelicGroupPoints.ofInfinite F G g) ^ e := hb _
    _ ≤ C * (RepresentationGrowth.adelicHeight F G rho x *
        RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofInfinite F G g)) ^ e :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hn0 _) (RepresentationGrowth.adelicHeight_mul_le
          F G rho hN x (AdelicGroupPoints.ofInfinite F G g)) e) hC
    _ = (C * RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofInfinite F G g) ^ e) *
        RepresentationGrowth.adelicHeight F G rho x ^ e := by rw [mul_pow]; ring

/-- Uniform growth is an invariant subspace for the whole infinite adelic group. -/
def adelicUniformGrowthInfiniteSubrepresentation (hN : 0 < N) :
    Subrepresentation ((finitePlotSmoothRightAction F G).comp
      (AdelicGroupPoints.ofInfinite F G).toMonoidHom) where
  toSubmodule := adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN
  apply_mem_toSubmodule g _f hf :=
    HasAdelicUniformPolynomialGrowth.infiniteRightAction F G hsmooth hcalc rho hN hf g

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  (hG : Langlands.GroupScheme.IsConnectedReductive G)
  (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N)

include hN in
/-- An actual form remains a form after right translation by the specified infinite
subgroup. -/
theorem IsAdelicAutomorphicForm.subgroupAction {f : FinitePlotSmoothRationalFunctions F G}
    (hf : IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f) (k : Kinf) :
    IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc
      (finitePlotSmoothInfiniteSubgroupAction F G Kinf k f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨IsAdelicInfiniteFinite.subgroupAction F G Kinf h1 k,
    IsAdelicCenterFinite.infiniteRightAction F G hsmooth hcalc h2 k.val, ?_⟩
  have h3' : f.val ∈ adelicGrowthSubrepresentation F G rho hN :=
    (mem_adelicGrowthSubrepresentation F G rho hN f.val).mpr h3
  exact (mem_adelicGrowthSubrepresentation F G rho hN _).mp
    ((adelicGrowthSubrepresentation F G rho hN).apply_mem_toSubmodule
      (AdelicGroupPoints.ofInfinite F G k.val) h3')

/-- The actual forms are an invariant subspace for the specified infinite subgroup. -/
def adelicAutomorphicInfiniteSubrepresentation :
    Subrepresentation (finitePlotSmoothInfiniteSubgroupAction F G Kinf) where
  toSubmodule :=
    (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule
  apply_mem_toSubmodule k f hf :=
    (mem_adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN _).mpr
      (IsAdelicAutomorphicForm.subgroupAction F G hsmooth hcalc rho Kinf hN
        ((mem_adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN
          f).mp hf) k)

/-- The actual uniform forms are an invariant subspace for the specified infinite subgroup. -/
def uniformAdelicAutomorphicInfiniteSubrepresentation :
    Subrepresentation (finitePlotSmoothInfiniteSubgroupAction F G Kinf) where
  toSubmodule := (uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK
    hN).toSubmodule
  apply_mem_toSubmodule k _f hf :=
    ⟨(adelicAutomorphicInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK
        hN).apply_mem_toSubmodule k hf.1,
      HasAdelicUniformPolynomialGrowth.infiniteRightAction F G hsmooth hcalc rho hN hf.2 k.val⟩

/-- The infinite subgroup and the actual enveloping action on uniform forms satisfy the
adjoint covariance `R(k) D_a = D_(Ad(k) a) R(k)`. -/
theorem uniformAdelicAutomorphicInfiniteSubrepresentation_envelopingAction (k : Kinf)
    (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : (uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK
      hN).toSubmodule) :
    (uniformAdelicAutomorphicInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK
        hN).toRepresentation k
        (uniformAdelicAutomorphicEnvelopingAction F G hsmooth hcalc Kinf rho hG hrho hK hN a f) =
      uniformAdelicAutomorphicEnvelopingAction F G hsmooth hcalc Kinf rho hG hrho hK hN
        (adelicEnvelopingConjugation F G hsmooth k.val a)
        ((uniformAdelicAutomorphicInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK
          hN).toRepresentation k f) :=
  Subtype.ext (finitePlotSmoothRightAction_actualAdelicEnvelopingAction F G hsmooth k.val a f.val)

variable [LocallyOfFiniteType G.X.hom] (hPD : Langlands.GroupScheme.ParabolicDynamicStatement.{u})

/-- The actual cusp forms are an invariant subspace for the specified infinite subgroup. -/
def adelicCuspidalInfiniteSubrepresentation :
    Subrepresentation (finitePlotSmoothInfiniteSubgroupAction F G Kinf) where
  toSubmodule :=
    (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule
  apply_mem_toSubmodule k _f hf :=
    ⟨(adelicAutomorphicInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK
        hN).apply_mem_toSubmodule k hf.1,
      (normalizedParabolicCuspidalSubrepresentation F G hPD hG).apply_mem_toSubmodule
        (AdelicGroupPoints.ofInfinite F G k.val) hf.2⟩

/-- The actual uniform cusp forms are an invariant subspace for the specified infinite
subgroup. -/
def uniformAdelicCuspidalInfiniteSubrepresentation :
    Subrepresentation (finitePlotSmoothInfiniteSubgroupAction F G Kinf) where
  toSubmodule := (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho
    hK hN).toSubmodule
  apply_mem_toSubmodule k _f hf :=
    ⟨(adelicCuspidalInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK hN
        hPD).apply_mem_toSubmodule k hf.1,
      HasAdelicUniformPolynomialGrowth.infiniteRightAction F G hsmooth hcalc rho hN hf.2 k.val⟩

end Langlands.Automorphic.GroupSchemeFunctions

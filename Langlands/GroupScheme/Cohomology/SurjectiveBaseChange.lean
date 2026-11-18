import Langlands.GroupScheme.Cohomology.BaseChange
import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor

/-! # Reflecting coboundaries through a surjective change of base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology.SurjectiveBaseChange

variable {R : CommRingCat.{u}} (K : CommAlgCat.{u} R)
attribute [local instance] restrictedTestAlgebra restrictedTestTower

variable (M : Type u) [AddCommGroup M] [Module R M] [Module K M]
  [IsScalarTower R K M]

/-- Scalar extension changes no coefficients when the original scalar map is
surjective and the module already carries the quotient-base action. -/
def coefficientEquiv (hK : Function.Surjective (algebraMap R K)) :
    K ⊗[R] M ≃ₗ[R] M where
  __ := ((LinearMap.id : M →ₗ[R] M).liftBaseChange K).restrictScalars R
  invFun m := (1 : K) ⊗ₜ[R] m
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul k m =>
      obtain ⟨r, rfl⟩ := hK k
      change (1 : K) ⊗ₜ[R] ((algebraMap R K r) • m) =
        algebraMap R K r ⊗ₜ[R] m
      rw [algebraMap_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      simp only [Algebra.smul_def, mul_one]
    | add x y hx hy =>
      change (1 : K) ⊗ₜ[R] ((LinearMap.id : M →ₗ[R] M).liftBaseChange K (x + y)) = x + y
      rw [map_add, TensorProduct.tmul_add]
      exact congrArg₂ (· + ·) hx hy
  right_inv m := by
    change (1 : K) • m = m
    exact one_smul K m

@[simp]
theorem coefficientEquiv_tmul (hK : Function.Surjective (algebraMap R K))
    (k : K) (m : M) : coefficientEquiv K M hK (k ⊗ₜ[R] m) = k • m := rfl

/-- The actual scalar-extension test algebra. -/
abbrev extensionTest (A : CommAlgCat.{u} R) : CommAlgCat.{u} K :=
  CommAlgCat.of K (K ⊗[R] A)

def extensionTestMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    extensionTest K A ⟶ extensionTest K B :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) f.hom)

/-- The right-factor inclusion, regarded as a map over the old base. -/
def testUnit (A : CommAlgCat.{u} R) :
    A ⟶ restrictedTest K (extensionTest K A) := by
  let q : A →+* (K ⊗[R] A) :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom
  letI := restrictedTestAlgebra K (extensionTest K A)
  exact CommAlgCat.ofHom {
    toRingHom := q
    commutes' r := by
      change (1 : K) ⊗ₜ[R] algebraMap R A r =
        algebraMap K (K ⊗[R] A) (algebraMap R K r)
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one] }

variable (H : GroupScheme (Spec R))

/-- Extend an actual source point and identify it with a point of the
base-changed group scheme. -/
def extensionPoint (A : CommAlgCat.{u} R) :
    H.affinePoints A →*
      ((GroupScheme.baseChange (algebraBaseMap R K)).obj H).affinePoints
        (extensionTest K A) := by
  letI := restrictedTestAlgebra K (extensionTest K A)
  letI := restrictedTestTower K (extensionTest K A)
  exact (Lie.affineBaseChangeEquiv R K H (extensionTest K A)).symm.toMonoidHom.comp
    (H.affinePointMap (testUnit K A))

theorem extensionPoint_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : H.affinePoints A) :
    ((GroupScheme.baseChange (algebraBaseMap R K)).obj H).affinePointMap
        (extensionTestMap K f) (extensionPoint K H A h) =
      extensionPoint K H B (H.affinePointMap f h) := by
  let := restrictedTestAlgebra K (extensionTest K A)
  let := restrictedTestTower K (extensionTest K A)
  let := restrictedTestAlgebra K (extensionTest K B)
  let := restrictedTestTower K (extensionTest K B)
  apply (Lie.affineBaseChangeEquiv R K H (extensionTest K B)).injective
  change Lie.affineBaseChangeEquiv R K H (extensionTest K B)
      (Lie.affineMap _ (extensionTestMap K f).hom (extensionPoint K H A h)) = _
  rw [Lie.affineBaseChangeEquiv_naturality]
  simp only [extensionPoint, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change H.affinePointMap (restrictedTestMap K (extensionTestMap K f))
      (H.affinePointMap (testUnit K A) h) =
    H.affinePointMap (testUnit K B) (H.affinePointMap f h)
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp,
    ← MonoidHom.comp_apply, ← affinePointMap_comp]
  congr 2

theorem extensionPoint_original (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    Lie.affineBaseChangeEquiv R K H (restrictedTest K (extensionTest K A))
        (extensionPoint K H A h) = H.affinePointMap (testUnit K A) h := by
  let := restrictedTestAlgebra K (extensionTest K A)
  let := restrictedTestTower K (extensionTest K A)
  change Lie.affineBaseChangeEquiv R K H (extensionTest K A)
    (extensionPoint K H A h) = _
  simp only [extensionPoint, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

local instance extensionRightAlgebra (A : CommAlgCat.{u} R) :
    Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra

/-- Cancel both the changed test algebra and the changed coefficient module. -/
def reflectionEquiv (hK : Function.Surjective (algebraMap R K))
    (A : CommAlgCat.{u} R) :
    ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) (extensionTest K A) ≃ₗ[A]
      ModulePoints M A :=
  Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.coefficientTensorEquiv.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (coefficientEquiv K M hK))

@[simp]
theorem reflectionEquiv_tmul (hK : Function.Surjective (algebraMap R K))
    (A : CommAlgCat.{u} R) (k l : K) (a : A) (m : M) :
    reflectionEquiv K M hK A ((k ⊗ₜ[R] a) ⊗ₜ[K] (l ⊗ₜ[R] m)) =
      a ⊗ₜ[R] ((k * l) • m) := by
  change a ⊗ₜ[R] coefficientEquiv K M hK (k • (l ⊗ₜ[R] m)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, coefficientEquiv_tmul]

/-- Cancellation commutes with every map of original test algebras. -/
theorem reflectionEquiv_naturality (hK : Function.Surjective (algebraMap R K))
    {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) (extensionTest K A)) :
    reflectionEquiv K M hK B
        (modulePointMap (R := CommRingCat.of K) (K ⊗[R] M) (extensionTestMap K f) x) =
      modulePointMap M f (reflectionEquiv K M hK A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t n =>
    induction t using TensorProduct.inductionOn with
    | tmul k a =>
      induction n using TensorProduct.inductionOn with
      | tmul l m =>
        change reflectionEquiv K M hK B
          ((k ⊗ₜ[R] f.hom a) ⊗ₜ[K] (l ⊗ₜ[R] m)) =
          modulePointMap M f
            (reflectionEquiv K M hK A ((k ⊗ₜ[R] a) ⊗ₜ[K] (l ⊗ₜ[R] m)))
        rw [reflectionEquiv_tmul, reflectionEquiv_tmul, modulePointMap_tmul]
      | add n n' hn hn' => simp only [TensorProduct.tmul_add, map_add, hn, hn']
    | add t t' ht ht' => simp only [TensorProduct.add_tmul, map_add, ht, ht']
  | add x y hx hy => simp only [map_add, hx, hy]

theorem reflectionEquiv_baseElement (hK : Function.Surjective (algebraMap R K))
    (A : CommAlgCat.{u} R) (n : K ⊗[R] M) :
    reflectionEquiv K M hK A ((1 : extensionTest K A) ⊗ₜ[K] n) =
      (1 : A) ⊗ₜ[R] coefficientEquiv K M hK n := by
  induction n using TensorProduct.inductionOn with
  | tmul k m =>
    change reflectionEquiv K M hK A (((1 : K) ⊗ₜ[R] (1 : A)) ⊗ₜ[K] (k ⊗ₜ[R] m)) = _
    rw [reflectionEquiv_tmul, coefficientEquiv_tmul, one_mul]
  | add n n' hn hn' =>
    simp only [TensorProduct.tmul_add, map_add, hn, hn']

/-- Coefficient extension along the right-factor inclusion is inverse to the
reflection equivalence. -/
theorem reflectionEquiv_unit (hK : Function.Surjective (algebraMap R K))
    (A : CommAlgCat.{u} R) (x : ModulePoints M A) :
    reflectionEquiv K M hK A
        ((scalarExtensionCancel K M (extensionTest K A)).symm
          (modulePointMap M (testUnit K A) x)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    change reflectionEquiv K M hK A
      (((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] m)) = a ⊗ₜ[R] m
    rw [reflectionEquiv_tmul, one_mul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem reflectionEquiv_symm (hK : Function.Surjective (algebraMap R K))
    (A : CommAlgCat.{u} R) (x : ModulePoints M A) :
    (reflectionEquiv K M hK A).symm x =
      (scalarExtensionCancel K M (extensionTest K A)).symm
        (modulePointMap M (testUnit K A) x) := by
  apply (reflectionEquiv K M hK A).injective
  rw [LinearEquiv.apply_symm_apply, reflectionEquiv_unit]

variable {M H}

/-- Reflection intertwines an original action and its actual base change at
the canonically extended source points. -/
theorem reflectionEquiv_action (hK : Function.Surjective (algebraMap R K))
    (ρ : ModuleRepresentation M H) (A : CommAlgCat.{u} R) (h : H.affinePoints A)
    (z : ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) (extensionTest K A)) :
    reflectionEquiv K M hK A
        ((ρ.baseChange K).action (extensionTest K A) (extensionPoint K H A h) z) =
      ρ.action A h (reflectionEquiv K M hK A z) := by
  obtain ⟨x, rfl⟩ := (reflectionEquiv K M hK A).symm.surjective z
  rw [LinearEquiv.apply_symm_apply, reflectionEquiv_symm]
  change reflectionEquiv K M hK A
    ((scalarExtensionCancel K M (extensionTest K A)).symm
      (ρ.action (restrictedTest K (extensionTest K A))
        (Lie.affineBaseChangeEquiv R K H (restrictedTest K (extensionTest K A))
          (extensionPoint K H A h))
        ((scalarExtensionCancel K M (extensionTest K A))
          ((scalarExtensionCancel K M (extensionTest K A)).symm
            (modulePointMap M (testUnit K A) x))))) = _
  rw [extensionPoint_original, LinearEquiv.apply_symm_apply,
    ← ρ.naturality, reflectionEquiv_unit]

/-- Any regular one-cochain on the changed base pulls back to the original
base when these coefficient modules are canonically identified. -/
def reflectOneCochain (hK : Function.Surjective (algebraMap R K))
    (b : OneCochain (R := CommRingCat.of K) (K ⊗[R] M)
      ((GroupScheme.baseChange (algebraBaseMap R K)).obj H)) : OneCochain M H where
  value A h := reflectionEquiv K M hK A
    (b.value (extensionTest K A) (extensionPoint K H A h))
  naturality f h := by
    rw [← reflectionEquiv_naturality, b.naturality, extensionPoint_naturality]

theorem reflectionEquiv_oneValue (hK : Function.Surjective (algebraMap R K))
    (c : OneCochain M H) (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    reflectionEquiv K M hK A
        ((c.baseChange K).value (extensionTest K A) (extensionPoint K H A h)) =
      c.value A h := by
  change reflectionEquiv K M hK A
    ((scalarExtensionCancel K M (extensionTest K A)).symm
      (c.value (restrictedTest K (extensionTest K A))
        (Lie.affineBaseChangeEquiv R K H (restrictedTest K (extensionTest K A))
          (extensionPoint K H A h)))) = _
  rw [extensionPoint_original, ← c.naturality, reflectionEquiv_unit]

theorem reflectionEquiv_twoValue (hK : Function.Surjective (algebraMap R K))
    (c : TwoCochain M H) (A : CommAlgCat.{u} R) (h k : H.affinePoints A) :
    reflectionEquiv K M hK A
        ((c.baseChange K).value (extensionTest K A)
          (extensionPoint K H A h) (extensionPoint K H A k)) =
      c.value A h k := by
  change reflectionEquiv K M hK A
    ((scalarExtensionCancel K M (extensionTest K A)).symm
      (c.value (restrictedTest K (extensionTest K A))
        (Lie.affineBaseChangeEquiv R K H (restrictedTest K (extensionTest K A))
          (extensionPoint K H A h))
        (Lie.affineBaseChangeEquiv R K H (restrictedTest K (extensionTest K A))
          (extensionPoint K H A k)))) = _
  rw [extensionPoint_original, extensionPoint_original, ← c.naturality,
    reflectionEquiv_unit]

/-- A base-changed one-coboundary has an actual primitive in the original
coefficient module. -/
theorem one_isCoboundary_of_baseChange
    (hK : Function.Surjective (algebraMap R K))
    (ρ : ModuleRepresentation M H) (c : OneCochain M H)
    (hc : (c.baseChange K).IsCoboundary (ρ.baseChange K)) :
    c.IsCoboundary ρ := by
  obtain ⟨n, hn⟩ := hc
  refine ⟨coefficientEquiv K M hK n, fun A h => ?_⟩
  have he := congrArg (reflectionEquiv K M hK A)
    (hn (extensionTest K A) (extensionPoint K H A h))
  rw [reflectionEquiv_oneValue, map_sub, reflectionEquiv_action,
    reflectionEquiv_baseElement] at he
  exact he

/-- A natural one-cochain primitive of the base-changed two-cocycle reflects
to an actual regular primitive on the original group scheme. -/
theorem two_isCoboundary_of_baseChange
    (hK : Function.Surjective (algebraMap R K))
    (ρ : ModuleRepresentation M H) (c : TwoCochain M H)
    (hc : (c.baseChange K).IsCoboundary (ρ.baseChange K)) :
    c.IsCoboundary ρ := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨reflectOneCochain K hK b, fun A h k => ?_⟩
  have ht := hb (extensionTest K A) (extensionPoint K H A h) (extensionPoint K H A k)
  rw [← map_mul] at ht
  have he := congrArg (reflectionEquiv K M hK A) ht
  rw [map_add, map_add, reflectionEquiv_twoValue, reflectionEquiv_action] at he
  exact he

/-- Low-degree vanishing after a surjective change of base contracts every
original regular cocycle whose coefficient module is already over that base. -/
theorem lowDegreeCoboundaries_of_baseChange
    (hK : Function.Surjective (algebraMap R K))
    (hH : HasVanishingLowDegreeCohomology
      ((GroupScheme.baseChange (algebraBaseMap R K)).obj H))
    (ρ : ModuleRepresentation M H) :
    (∀ c : OneCochain M H, c.IsCocycle ρ → c.IsCoboundary ρ) ∧
      (∀ c : TwoCochain M H, c.IsCocycle ρ → c.IsCoboundary ρ) := by
  obtain ⟨h₁, h₂⟩ := hH (K ⊗[R] M) (ρ.baseChange K)
  constructor
  · intro c hc
    exact one_isCoboundary_of_baseChange K hK ρ c
      (h₁ (c.baseChange K) (c.baseChange_isCocycle K ρ hc))
  · intro c hc
    exact two_isCoboundary_of_baseChange K hK ρ c
      (h₂ (c.baseChange K) (c.baseChange_isCocycle K ρ hc))

end Langlands.GroupScheme.Cohomology.SurjectiveBaseChange

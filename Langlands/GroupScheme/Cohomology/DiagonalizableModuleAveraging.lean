import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.GroupScheme.Torus.DiagonalizableAveraging

/-! # Coefficient averaging for arbitrary modules on diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cohomology.DiagonalizableModuleAveraging

variable {R : CommRingCat.{u}} (Λ : Type u) [AddCommGroup Λ]

/-- Extract the coefficient of the identity character. -/
def coefficientZero (A : CommAlgCat.{u} R) :
    AddMonoidAlgebra A Λ →ₗ[A] A where
  toFun x := x.coeff 0
  map_add' x y := by simp
  map_smul' a x := by simp

/-- The affine algebra carrying a universal diagonalizable point over `A`. -/
abbrev averagingAlgebra (A : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (AddMonoidAlgebra A Λ)

/-- Include constant coefficients in the averaging algebra. -/
abbrev coefficientInclusion (A : CommAlgCat.{u} R) : A ⟶ averagingAlgebra Λ A :=
  CommAlgCat.ofHom (Diagonalizable.Averaging.const R Λ A)

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Average module-valued functions by tensoring coefficient extraction with
the identity of the arbitrary coefficient module. -/
def average (A : CommAlgCat.{u} R) :
    ModulePoints M (averagingAlgebra Λ A) →ₗ[R] ModulePoints M A :=
  TensorProduct.map ((coefficientZero Λ A).restrictScalars R) LinearMap.id

@[simp]
theorem average_tmul (A : CommAlgCat.{u} R) (a : AddMonoidAlgebra A Λ) (m : M) :
    average Λ M A (a ⊗ₜ[R] m) = a.coeff 0 ⊗ₜ[R] m := rfl

/-- Averaging a constant module point recovers that point. -/
theorem average_coefficientInclusion (A : CommAlgCat.{u} R) (x : ModulePoints M A) :
    average Λ M A (modulePointMap M (coefficientInclusion Λ A) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    change (AddMonoidAlgebra.single 0 a).coeff 0 ⊗ₜ[R] m = a ⊗ₜ[R] m
    simp
  | add x y hx hy => simp [hx, hy]

/-- Averaging after a change of coefficient algebra commutes with that change. -/
theorem average_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : ModulePoints M (averagingAlgebra Λ A)) :
    average Λ M B
        (modulePointMap M (CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom Λ f.hom)) x) =
      modulePointMap M f (average Λ M A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    change (AddMonoidAlgebra.mapAlgHom Λ f.hom a).coeff 0 ⊗ₜ[R] m =
      f.hom (a.coeff 0) ⊗ₜ[R] m
    rw [AddMonoidAlgebra.coeff_mapAlgHom]
  | add x y hx hy => simp [hx, hy]

/-- Translation of the universal diagonalizable variable preserves the average. -/
theorem average_translation (A : CommAlgCat.{u} R)
    (h : Multiplicative Λ →* Aˣ)
    (x : ModulePoints M (averagingAlgebra Λ A)) :
    average Λ M A
        (modulePointMap M
          (CommAlgCat.ofHom ((Diagonalizable.Averaging.translation Λ h).restrictScalars R)) x) =
      average Λ M A x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    change (Diagonalizable.Averaging.translation Λ h a).coeff 0 ⊗ₜ[R] m =
      a.coeff 0 ⊗ₜ[R] m
    rw [Diagonalizable.Averaging.coeff_zero_translation]
  | add x y hx hy => simp [hx, hy]

/-- A scalar times a constant module point averages to its constant coefficient
times the original module point. -/
theorem average_smul_constant (A : CommAlgCat.{u} R) (a : AddMonoidAlgebra A Λ)
    (x : ModulePoints M A) :
    average Λ M A
        (a • modulePointMap M (coefficientInclusion Λ A) x) =
      a.coeff 0 • x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    change average Λ M A ((a * AddMonoidAlgebra.single 0 b) ⊗ₜ[R] m) =
      a.coeff 0 • (b ⊗ₜ[R] m)
    rw [average_tmul, TensorProduct.smul_tmul']
    congr 1
    change (a * AddMonoidAlgebra.single 0 b).coeff 0 = a.coeff 0 * b
    exact AddMonoidAlgebra.coeff_mul_single_zero a b 0
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Averaging commutes with the action of a constant group point. -/
theorem average_action {H : GroupScheme (Spec R)} (ρ : ModuleRepresentation M H)
    (A : CommAlgCat.{u} R) (h : H.affinePoints A)
    (x : ModulePoints M (averagingAlgebra Λ A)) :
    average Λ M A
        (ρ.action (averagingAlgebra Λ A)
          (H.affinePointMap (coefficientInclusion Λ A) h) x) =
      ρ.action A h (average Λ M A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    have ht : a ⊗ₜ[R] m =
        a • modulePointMap M (coefficientInclusion Λ A) ((1 : A) ⊗ₜ[R] m) := by
      simp [TensorProduct.smul_tmul', ← AddMonoidAlgebra.one_def]
    rw [ht, (ρ.action (averagingAlgebra Λ A)
      (H.affinePointMap (coefficientInclusion Λ A) h)).map_smul,
      ← ρ.naturality, average_smul_constant, average_smul_constant,
      (ρ.action A h).map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Extend all coefficients of the averaging algebra. -/
abbrev coefficientMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    averagingAlgebra Λ A ⟶ averagingAlgebra Λ B :=
  CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom Λ f.hom)

theorem coefficientInclusion_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    coefficientInclusion Λ A ≫ coefficientMap Λ f =
      f ≫ coefficientInclusion Λ B := by
  ext a
  simp [coefficientMap, coefficientInclusion, Diagonalizable.Averaging.const,
    AddMonoidAlgebra.coe_algebraMap]

local notation "D" => CommGroupScheme.toGrp (Diagonalizable.groupScheme R Λ)

/-- The actual universal point on the averaging algebra. -/
abbrev averagingPoint (A : CommAlgCat.{u} R) :
    affinePoints D (averagingAlgebra Λ A) :=
  Diagonalizable.Averaging.point R Λ A

theorem averagingPoint_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    affinePointMap D (coefficientMap Λ f) (averagingPoint Λ A) =
      averagingPoint Λ B := by
  change Lie.affineMap D (AddMonoidAlgebra.mapAlgHom Λ f.hom)
      (Lie.affineMap D (Diagonalizable.Averaging.scalars R Λ A)
        (Diagonalizable.Averaging.universalPoint R Λ)) =
    Lie.affineMap D (Diagonalizable.Averaging.scalars R Λ B)
      (Diagonalizable.Averaging.universalPoint R Λ)
  rw [← Lie.affineMap_comp]
  congr 1
  unfold Diagonalizable.Averaging.scalars
  rw [← AddMonoidAlgebra.mapRangeAlgHom_comp]
  exact congrArg (fun f : R →ₐ[R] B => Lie.affineMap D (AddMonoidAlgebra.mapAlgHom Λ f))
    (Subsingleton.elim _ _)

theorem extendedPoint_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : affinePoints D A) :
    affinePointMap D (coefficientMap Λ f)
        (affinePointMap D (coefficientInclusion Λ A) h) =
      affinePointMap D (coefficientInclusion Λ B) (affinePointMap D f h) := by
  change ((affinePointMap D (coefficientMap Λ f)).comp
      (affinePointMap D (coefficientInclusion Λ A))) h =
    ((affinePointMap D (coefficientInclusion Λ B)).comp (affinePointMap D f)) h
  rw [← affinePointMap_comp, coefficientInclusion_naturality, affinePointMap_comp]

/-- Average the second variable of a regular two-cochain. -/
def averageTwo (c : TwoCochain M D) : OneCochain M D where
  value A h :=
    average Λ M A (c.value (averagingAlgebra Λ A)
      (affinePointMap D (coefficientInclusion Λ A) h) (averagingPoint Λ A))
  naturality f h := by
    rw [← average_naturality Λ M f, c.naturality,
      extendedPoint_naturality, averagingPoint_naturality]

/-- Translation invariance when the first cochain variable is constant. -/
theorem averageTwo_translate (c : TwoCochain M D) (A : CommAlgCat.{u} R)
    (h k : affinePoints D A) :
    average Λ M A (c.value (averagingAlgebra Λ A)
        (affinePointMap D (coefficientInclusion Λ A) h)
        (affinePointMap D (coefficientInclusion Λ A) k * averagingPoint Λ A)) =
      (averageTwo Λ M c).value A h := by
  let τ : averagingAlgebra Λ A ⟶ averagingAlgebra Λ A :=
    CommAlgCat.ofHom
      ((Diagonalizable.Averaging.translation Λ
        (Diagonalizable.Averaging.pointsEquiv R Λ A k)).restrictScalars R)
  have hc := c.naturality τ
    (affinePointMap D (coefficientInclusion Λ A) h) (averagingPoint Λ A)
  have ht₁ :
      affinePointMap D τ (affinePointMap D (coefficientInclusion Λ A) h) =
        affinePointMap D (coefficientInclusion Λ A) h :=
    Diagonalizable.Averaging.translation_const R Λ _ h
  have ht₂ : affinePointMap D τ (averagingPoint Λ A) =
      affinePointMap D (coefficientInclusion Λ A) k * averagingPoint Λ A :=
    Diagonalizable.Averaging.translation_point R Λ k
  rw [ht₁, ht₂] at hc
  change _ = average Λ M A _
  rw [← hc]
  exact average_translation Λ M A _ _

/-- The average contracts every regular two-cocycle on a diagonalizable group
with arbitrary quasi-coherent coefficients over an arbitrary ring. -/
theorem averageTwo_coboundary (ρ : ModuleRepresentation M D)
    (c : TwoCochain M D) (hc : c.IsCocycle ρ)
    (A : CommAlgCat.{u} R) (h k : affinePoints D A) :
    c.value A h k + (averageTwo Λ M c).value A (h * k) =
      ρ.action A h ((averageTwo Λ M c).value A k) + (averageTwo Λ M c).value A h := by
  have hh := congrArg (average Λ M A)
    (hc (averagingAlgebra Λ A)
      (affinePointMap D (coefficientInclusion Λ A) h)
      (affinePointMap D (coefficientInclusion Λ A) k) (averagingPoint Λ A))
  rw [map_add, map_add, ← c.naturality (coefficientInclusion Λ A) h k,
    average_coefficientInclusion, average_action,
    averageTwo_translate] at hh
  simpa only [map_mul, averageTwo] using hh

theorem twoCocycle_isCoboundary (ρ : ModuleRepresentation M D)
    (c : TwoCochain M D) (hc : c.IsCocycle ρ) : c.IsCoboundary ρ :=
  ⟨averageTwo Λ M c, averageTwo_coboundary Λ M ρ c hc⟩

/-- Average a regular one-cochain to a module point over the coefficient ring. -/
def averageOne (c : OneCochain M D) (A : CommAlgCat.{u} R) : ModulePoints M A :=
  average Λ M A (c.value (averagingAlgebra Λ A) (averagingPoint Λ A))

theorem averageOne_naturality (c : OneCochain M D)
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    modulePointMap M f (averageOne Λ M c A) = averageOne Λ M c B := by
  rw [averageOne, averageOne, ← average_naturality Λ M f,
    c.naturality, averagingPoint_naturality]

theorem averageOne_translate (c : OneCochain M D) (A : CommAlgCat.{u} R)
    (h : affinePoints D A) :
    average Λ M A (c.value (averagingAlgebra Λ A)
        (affinePointMap D (coefficientInclusion Λ A) h * averagingPoint Λ A)) =
      averageOne Λ M c A := by
  let τ : averagingAlgebra Λ A ⟶ averagingAlgebra Λ A :=
    CommAlgCat.ofHom
      ((Diagonalizable.Averaging.translation Λ
        (Diagonalizable.Averaging.pointsEquiv R Λ A h)).restrictScalars R)
  have hc := c.naturality τ (averagingPoint Λ A)
  have ht : affinePointMap D τ (averagingPoint Λ A) =
      affinePointMap D (coefficientInclusion Λ A) h * averagingPoint Λ A :=
    Diagonalizable.Averaging.translation_point R Λ h
  rw [ht] at hc
  unfold averageOne
  rw [← hc]
  exact average_translation Λ M A _ _

/-- Averaging the one-cocycle equation gives its explicit coboundary formula. -/
theorem averageOne_cocycle (ρ : ModuleRepresentation M D)
    (c : OneCochain M D) (hc : c.IsCocycle ρ)
    (A : CommAlgCat.{u} R) (h : affinePoints D A) :
    averageOne Λ M c A = c.value A h + ρ.action A h (averageOne Λ M c A) := by
  have hh := congrArg (average Λ M A)
    (hc (averagingAlgebra Λ A)
      (affinePointMap D (coefficientInclusion Λ A) h) (averagingPoint Λ A))
  rw [averageOne_translate, map_add, ← c.naturality (coefficientInclusion Λ A) h,
    average_coefficientInclusion, average_action] at hh
  exact hh

/-- Extension of a base module tensor is the constant tensor of its image
under the canonical `R ⊗ M ≃ M` comparison. -/
theorem modulePointMap_base (A : CommAlgCat.{u} R)
    (x : ModulePoints M (CommAlgCat.of R R)) :
    modulePointMap M (CommAlgCat.ofHom (Algebra.ofId R A)) x =
      (1 : A) ⊗ₜ[R] (TensorProduct.lid R M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    change (algebraMap R A r) ⊗ₜ[R] m = (1 : A) ⊗ₜ[R] (r • m)
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul r (1 : A) m)
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

/-- Every regular one-cocycle on a diagonalizable group is a coboundary of
an actual element of the arbitrary base module. -/
theorem oneCocycle_isCoboundary (ρ : ModuleRepresentation M D)
    (c : OneCochain M D) (hc : c.IsCocycle ρ) : c.IsCoboundary ρ := by
  let m : M := -(TensorProduct.lid R M (averageOne Λ M c (CommAlgCat.of R R)))
  refine ⟨m, fun A h => ?_⟩
  have hm : (1 : A) ⊗ₜ[R] m = -averageOne Λ M c A := by
    dsimp only [m]
    rw [TensorProduct.tmul_neg, ← modulePointMap_base,
      averageOne_naturality]
    rfl
  rw [hm, map_neg, sub_neg_eq_add]
  have hh := averageOne_cocycle Λ M ρ c hc A h
  have he : c.value A h =
      averageOne Λ M c A - ρ.action A h (averageOne Λ M c A) :=
    (eq_sub_iff_add_eq).mpr hh.symm
  simpa only [sub_eq_add_neg, add_comm] using he

/-- Both positive degrees needed for homomorphism deformation vanish for every
diagonalizable group, with arbitrary quasi-coherent module coefficients. -/
theorem hasVanishingLowDegreeCohomology :
    HasVanishingLowDegreeCohomology D := by
  intro M _ _ ρ
  exact ⟨fun c hc => oneCocycle_isCoboundary Λ M ρ c hc,
    fun c hc => twoCocycle_isCoboundary Λ M ρ c hc⟩

end Langlands.GroupScheme.Cohomology.DiagonalizableModuleAveraging

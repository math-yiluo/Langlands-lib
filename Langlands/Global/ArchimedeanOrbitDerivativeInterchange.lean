import Langlands.Global.ArchimedeanCompactOrbitSmoothness
import Langlands.Analysis.MixedParameterDerivatives

/-! # Parameter differentiation of genuine derivative orbits -/

noncomputable section
universe u
open scoped Classical Topology TensorProduct Manifold ContDiff Matrix.Norms.Operator
open Filter Set
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

omit [NumberField K] in
/-- Left real generators, addition and complex scaling suffice for induction. -/
theorem enveloping_real_left_induction {P : EnvelopingAlgebra K n → Prop}
    (h1 : P 1)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (z : ℂ) a, P a → P (z • a))
    (hgen : ∀ X a, P a →
      P (envelopingGenerator K n (complexify K n X) * a))
    (a : EnvelopingAlgebra K n) : P a := by
  have hcomplex (X : ComplexLieAlgebra K n) :
      ∀ a, P a → P (envelopingGenerator K n X * a) := by
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      intro a ha
      have ht : z ⊗ₜ[ℝ] X = z • complexify K n X := by
        simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul, smul_mul_assoc]
      exact hsmul z _ (hgen X a ha)
    | add X Y hX hY =>
      intro a ha
      rw [map_add, add_mul]
      exact hadd _ _ (hX a ha) (hY a ha)
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra K n)
  have hq (t : TensorAlgebra ℂ (ComplexLieAlgebra K n)) :
      ∀ b, P b → P (q t * b) := by
    induction t using TensorAlgebra.induction with
    | algebraMap z =>
      intro b hb
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact hsmul z b hb
    | ι X => exact hcomplex X
    | mul t s ht hs =>
      intro b hb
      rw [map_mul, mul_assoc]
      exact ht _ (hs b hb)
    | add t s ht hs =>
      intro b hb
      rw [map_add, add_mul]
      exact hadd _ _ (ht b hb) (hs b hb)
  change P (q t)
  simpa only [mul_one] using hq t 1 h1

theorem matrixDerivativeRightOrbitValue_apply
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n)
    (g x : ArchimedeanGL K n) :
    matrixDerivativeRightOrbitValue K n f a
        ((g : ArchimedeanMatrix K n), (x : ArchimedeanMatrix K n)) =
      (envelopingAction K n a (smoothRightAction K n
        ((archimedeanGLCoordinates K n).symm g)
        (DerivativeSmoothFunctions.toSmooth K n f))).val
          ((archimedeanGLCoordinates K n).symm x) := by
  simp only [matrixDerivativeRightOrbitValue, matrixRightOrbit_apply,
    coordinateExtension_apply]
  rfl

theorem matrixDerivativeRightOrbitValue_one
    (f : DerivativeSmoothFunctions K n) (g x : ArchimedeanGL K n) :
    matrixDerivativeRightOrbitValue K n f 1
        ((g : ArchimedeanMatrix K n), (x : ArchimedeanMatrix K n)) =
      coordinateExtension K n (DerivativeSmoothFunctions.toSmooth K n f)
        ((x : ArchimedeanMatrix K n) * (g : ArchimedeanMatrix K n)) := by
  rw [matrixDerivativeRightOrbitValue_apply, envelopingAction_one,
    smoothRightAction_apply, ← Units.val_mul, coordinateExtension_apply]
  simp only [map_mul]

theorem matrixDerivativeRightOrbitValue_fst_contDiffAt
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n)
    (g x : ArchimedeanGL K n) :
    ContDiffAt ℝ ∞
      (fun y => matrixDerivativeRightOrbitValue K n f a
        (y, (x : ArchimedeanMatrix K n))) (g : ArchimedeanMatrix K n) := by
  have h : ContDiffAt ℝ ∞ (matrixDerivativeRightOrbitValue K n f a)
      ((g : ArchimedeanMatrix K n), (x : ArchimedeanMatrix K n)) :=
    (matrixDerivativeRightOrbitValue_contDiffOn K n f a).contDiffAt
    (((isOpen_matrixUnitDomain K n).prod (isOpen_matrixUnitDomain K n)).mem_nhds
      ⟨⟨g, rfl⟩, ⟨x, rfl⟩⟩)
  have hi : ContDiffAt ℝ ∞
      (fun y : ArchimedeanMatrix K n => (y, (x : ArchimedeanMatrix K n)))
      (g : ArchimedeanMatrix K n) := contDiffAt_id.prodMk contDiffAt_const
  exact h.comp (g : ArchimedeanMatrix K n) hi

theorem matrixDerivativeRightOrbitValue_snd_contDiffAt
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n)
    (g x : ArchimedeanGL K n) :
    ContDiffAt ℝ ∞
      (fun y => matrixDerivativeRightOrbitValue K n f a
        ((g : ArchimedeanMatrix K n), y)) (x : ArchimedeanMatrix K n) := by
  change ContDiffAt ℝ ∞ (coordinateExtension K n
    (envelopingAction K n a (DerivativeSmoothFunctions.toSmooth K n
      (matrixRightOrbit K n f (g : ArchimedeanMatrix K n)))))
    (x : ArchimedeanMatrix K n)
  exact coordinateExtension_contDiffAt K n _ x

/-- The evaluation partial derivative is exactly left multiplication by a real
generator in the enveloping index. -/
theorem matrixDerivativeRightOrbitValue_snd_derivative
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n)
    (g : ArchimedeanMatrix K n) (x : ArchimedeanGL K n)
    (Y : RealLieAlgebra K n) :
    fderiv ℝ (fun y => matrixDerivativeRightOrbitValue K n f a (g, y))
        (x : ArchimedeanMatrix K n)
        ((x : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n Y) =
      matrixDerivativeRightOrbitValue K n f
        (envelopingGenerator K n (complexify K n Y) * a)
        (g, (x : ArchimedeanMatrix K n)) := by
  simp only [matrixDerivativeRightOrbitValue, envelopingAction_mul,
    envelopingAction_real_generator, coordinateExtension_apply,
    smoothDifferential_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The first parameter derivative of the undifferentiated orbit follows from
the actual multiplication map, with direction `g*X`. -/
theorem matrixDerivativeRightOrbitValue_one_parameter_derivative
    (f : DerivativeSmoothFunctions K n) (g x : ArchimedeanGL K n)
    (X : RealLieAlgebra K n) :
    fderiv ℝ (fun y => matrixDerivativeRightOrbitValue K n f 1
        (y, (x : ArchimedeanMatrix K n)))
        (g : ArchimedeanMatrix K n)
        ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X) =
      matrixDerivativeRightOrbitValue K n
        (DerivativeSmoothFunctions.operator K n
          (envelopingGenerator K n (complexify K n X)) f) 1
        ((g : ArchimedeanMatrix K n), (x : ArchimedeanMatrix K n)) := by
  have heq :
      (fun y => matrixDerivativeRightOrbitValue K n f 1
        (y, (x : ArchimedeanMatrix K n))) =ᶠ[𝓝 (g : ArchimedeanMatrix K n)]
      (fun y => coordinateExtension K n (DerivativeSmoothFunctions.toSmooth K n f)
        ((x : ArchimedeanMatrix K n) * y)) := by
    filter_upwards [(isOpen_matrixUnitDomain K n).mem_nhds ⟨g, rfl⟩] with y hy
    obtain ⟨h, rfl⟩ := hy
    exact matrixDerivativeRightOrbitValue_one K n f h x
  rw [heq.fderiv_eq, matrixDerivativeRightOrbitValue_one,
    DerivativeSmoothFunctions.toSmooth_operator]
  have hf : DifferentiableAt ℝ
      (coordinateExtension K n (DerivativeSmoothFunctions.toSmooth K n f))
      ((x : ArchimedeanMatrix K n) * (g : ArchimedeanMatrix K n)) := by
    simpa only [Units.val_mul] using ((coordinateExtension_contDiffAt K n
      (DerivativeSmoothFunctions.toSmooth K n f) (x * g)).differentiableAt (by simp))
  have hm : DifferentiableAt ℝ
      (fun y : ArchimedeanMatrix K n => (x : ArchimedeanMatrix K n) * y)
      (g : ArchimedeanMatrix K n) := differentiableAt_id.const_mul _
  rw [fderiv_fun_comp (g : ArchimedeanMatrix K n) hf hm]
  change fderiv ℝ (coordinateExtension K n (DerivativeSmoothFunctions.toSmooth K n f))
    ((x : ArchimedeanMatrix K n) * (g : ArchimedeanMatrix K n))
    (fderiv ℝ ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n))
      (x : ArchimedeanMatrix K n)) (g : ArchimedeanMatrix K n)
      ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X)) = _
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.mul_apply']
  rw [← Units.val_mul, coordinateExtension_apply, envelopingAction_real_generator,
    smoothDifferential_apply]
  simp only [map_mul, ContinuousMulEquiv.apply_symm_apply, Units.val_mul, mul_assoc]

theorem matrixDerivativeRightOrbitValue_add
    (f : DerivativeSmoothFunctions K n) (a b : EnvelopingAlgebra K n)
    (p : ArchimedeanMatrix K n × ArchimedeanMatrix K n) :
    matrixDerivativeRightOrbitValue K n f (a + b) p =
      matrixDerivativeRightOrbitValue K n f a p +
        matrixDerivativeRightOrbitValue K n f b p := by
  simp [matrixDerivativeRightOrbitValue, coordinateExtension, LinearMap.add_apply]

theorem matrixDerivativeRightOrbitValue_smul
    (f : DerivativeSmoothFunctions K n) (z : ℂ) (a : EnvelopingAlgebra K n)
    (p : ArchimedeanMatrix K n × ArchimedeanMatrix K n) :
    matrixDerivativeRightOrbitValue K n f (z • a) p =
      z • matrixDerivativeRightOrbitValue K n f a p := by
  simp [matrixDerivativeRightOrbitValue, coordinateExtension, LinearMap.smul_apply]

/-- Parameter differentiation commutes with every actual enveloping operator.
The translating direction is `g*X`; the resulting vector is `R(g)D(X)f`. -/
theorem matrixDerivativeRightOrbitValue_parameter_derivative
    (a : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) (g x : ArchimedeanGL K n)
    (X : RealLieAlgebra K n) :
    fderiv ℝ (fun y => matrixDerivativeRightOrbitValue K n f a
        (y, (x : ArchimedeanMatrix K n)))
        (g : ArchimedeanMatrix K n)
        ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X) =
      matrixDerivativeRightOrbitValue K n
        (DerivativeSmoothFunctions.operator K n
          (envelopingGenerator K n (complexify K n X)) f) a
        ((g : ArchimedeanMatrix K n), (x : ArchimedeanMatrix K n)) := by
  let P : EnvelopingAlgebra K n → Prop := fun b =>
    ∀ (v : DerivativeSmoothFunctions K n) (h q : ArchimedeanGL K n)
      (Z : RealLieAlgebra K n),
      fderiv ℝ (fun y => matrixDerivativeRightOrbitValue K n v b
          (y, (q : ArchimedeanMatrix K n)))
          (h : ArchimedeanMatrix K n)
          ((h : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n Z) =
        matrixDerivativeRightOrbitValue K n
          (DerivativeSmoothFunctions.operator K n
            (envelopingGenerator K n (complexify K n Z)) v) b
          ((h : ArchimedeanMatrix K n), (q : ArchimedeanMatrix K n))
  suffices h : P a from h f g x X
  apply enveloping_real_left_induction K n
  · exact matrixDerivativeRightOrbitValue_one_parameter_derivative K n
  · intro b c hb hc v h q Z
    simp_rw [matrixDerivativeRightOrbitValue_add]
    rw [fderiv_fun_add
      ((matrixDerivativeRightOrbitValue_fst_contDiffAt K n v b h q).differentiableAt
        (by simp))
      ((matrixDerivativeRightOrbitValue_fst_contDiffAt K n v c h q).differentiableAt
        (by simp))]
    simp only [add_apply, hb v h q Z, hc v h q Z]
  · intro z b hb v h q Z
    simp_rw [matrixDerivativeRightOrbitValue_smul]
    rw [fderiv_fun_const_smul
      ((matrixDerivativeRightOrbitValue_fst_contDiffAt K n v b h q).differentiableAt
        (by simp))]
    simp only [smul_apply, hb v h q Z]
  · intro Y b hb v h q Z
    let d := (h : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n Z
    let e := (q : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n Y
    let v' := DerivativeSmoothFunctions.operator K n
      (envelopingGenerator K n (complexify K n Z)) v
    have heq :
        (fun y => fderiv ℝ (fun z => matrixDerivativeRightOrbitValue K n v b (z, y))
          (h : ArchimedeanMatrix K n) d) =ᶠ[𝓝 (q : ArchimedeanMatrix K n)]
        (fun y => matrixDerivativeRightOrbitValue K n v' b
          ((h : ArchimedeanMatrix K n), y)) := by
      filter_upwards [(isOpen_matrixUnitDomain K n).mem_nhds ⟨q, rfl⟩] with y hy
      obtain ⟨q', rfl⟩ := hy
      exact hb v h q' Z
    calc
      _ = fderiv ℝ
          (fun z => fderiv ℝ (fun y => matrixDerivativeRightOrbitValue K n v b (z, y))
            (q : ArchimedeanMatrix K n) e) (h : ArchimedeanMatrix K n) d := by
        congr 2
        funext z
        exact (matrixDerivativeRightOrbitValue_snd_derivative K n v b z q Y).symm
      _ = fderiv ℝ
          (fun y => fderiv ℝ (fun z => matrixDerivativeRightOrbitValue K n v b (z, y))
            (h : ArchimedeanMatrix K n) d) (q : ArchimedeanMatrix K n) e :=
        Langlands.Analysis.fderiv_fst_snd_comm
          (isOpen_matrixUnitDomain K n) (isOpen_matrixUnitDomain K n)
          (matrixDerivativeRightOrbitValue_contDiffOn K n v b)
          ⟨h, rfl⟩ ⟨q, rfl⟩ d e
      _ = fderiv ℝ
          (fun y => matrixDerivativeRightOrbitValue K n v' b
            ((h : ArchimedeanMatrix K n), y)) (q : ArchimedeanMatrix K n) e := by
        rw [heq.fderiv_eq]
      _ = _ := matrixDerivativeRightOrbitValue_snd_derivative K n v' b _ q Y

end Langlands.Global.ArchimedeanGL

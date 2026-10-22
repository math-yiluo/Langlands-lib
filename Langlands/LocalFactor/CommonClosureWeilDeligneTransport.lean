import Langlands.LocalFactor.CommonClosureWeilDeligne
import Langlands.LocalFactor.WeilDeligneTransport
import Langlands.ClassFieldTheory.Local.ReciprocityTransport
import Langlands.Weil.Local.Parameters
import Langlands.Weil.Representation.InductionContinuity

/-!
# Actual standalone transport of common-closure Weil–Deligne pairs

The published Weil comparison identifies the norm character and actual inertia.
Restriction retains the vector space and monodromy, giving the standalone pair
and the comparison of its rational factors.
-/

noncomputable section

universe uF uE uV

namespace Langlands.LocalFactor.CommonClosureWeilDeligne.Transport

open Weil.Local LocalClassField WeilDeligneRepresentation

variable {p : ℕ} [Fact p.Prime]
  (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The actual common-closure covariance character pulls back to the standalone one. -/
theorem normCharacter_comp :
    (normCharacter F (extensionFiniteIntermediate F E f)).toMonoidHom.comp
      (extensionImageWeilEquiv F E f).toMonoidHom =
        (localNormCharacter E).toMonoidHom := by
  apply MonoidHom.ext
  intro w
  exact extensionImageWeilEquiv_normCharacter F E f w

/-- The inverse image of actual common-closure inertia is actual standalone inertia. -/
theorem inertia_comap :
    (inertia F (extensionFiniteIntermediate F E f)).comap
      (extensionImageWeilEquiv F E f).toMonoidHom = localInertia E := by
  ext w
  exact extensionWeilMap_mem_localInertia F E f w

/-- The existing restriction, with covariance expressed by the actual standalone norm. -/
def standalonePair (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    LocalWeilDeligneRepresentation.{uE, max uF uV} E := by
  let B := restrict (extensionImageWeilEquiv F E f).toMonoidHom A
  exact
    { toFiniteRepresentation := B.toFiniteRepresentation
      monodromy := B.monodromy
      nilpotent := B.nilpotent
      covariance := fun w => by
        change B.representation w * B.monodromy * B.representation w⁻¹ =
          (localNormCharacter E w : ℂ) • B.monodromy
        rw [← extensionImageWeilEquiv_normCharacter F E f w]
        exact B.covariance w }

@[simp]
theorem standalonePair_representation
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    (standalonePair F E f A).representation w =
      A.representation (extensionImageWeilEquiv F E f w) := rfl

@[simp]
theorem standalonePair_monodromy
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    (standalonePair F E f A).monodromy = A.monodromy := rfl

/-- Usual-topology continuity is retained by the actual continuous Weil comparison. -/
theorem standalonePair_isContinuous
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (hA : A.toFiniteRepresentation.IsContinuous) :
    (standalonePair F E f A).toFiniteRepresentation.IsContinuous :=
  FiniteRepresentation.isContinuous_restrict
    (extensionImageWeilEquiv F E f).toMonoidHom
    (extensionImageWeilEquiv F E f).continuous hA

/-- An actual equivalence of common-closure pairs induces a standalone pair equivalence. -/
def standalonePairEquiv
    {A B : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)}
    (e : WeilDeligneRepresentation.Equiv A B) :
    WeilDeligneRepresentation.Equiv (standalonePair F E f A) (standalonePair F E f B) where
  representationEquiv :=
    (restrictEquiv (extensionImageWeilEquiv F E f).toMonoidHom e).representationEquiv
  comm_monodromy :=
    (restrictEquiv (extensionImageWeilEquiv F E f).toMonoidHom e).comm_monodromy

private theorem standalonePair_kernelRepresentation
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    (standalonePair F E f A).kernelRepresentation =
      (restrict (extensionImageWeilEquiv F E f).toMonoidHom A).kernelRepresentation := by
  rfl

private theorem standalonePair_quotientRepresentation
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (I : Subgroup (localWeilGroup E)) [I.Normal] :
    WeilDeligne.quotientRepresentation (standalonePair F E f A) I =
      WeilDeligne.quotientRepresentation
        (restrict (extensionImageWeilEquiv F E f).toMonoidHom A) I := by
  rfl

/-- Comparison of the actual inertia-fixed representations, with unchanged vectors. -/
def invariantsEquiv (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    FiniteRepresentation.Equiv
      (WeilDeligne.inertiaRepresentation (standalonePair F E f A) (localInertia E))
      (FiniteRepresentation.restrict (extensionImageWeilEquiv F E f).toMonoidHom
        (WeilDeligne.inertiaRepresentation A (inertia F (extensionFiniteIntermediate F E f)))) := by
  simpa only [inertia_comap F E f, standalonePair, restrict,
    WeilDeligne.inertiaRepresentation] using
      WeilDeligne.Transport.invariantsEquiv (extensionImageWeilEquiv F E f).toMulEquiv
        A.toFiniteRepresentation (inertia F (extensionFiniteIntermediate F E f))

/-- Comparison of the actual inertia-fixed monodromy kernels. -/
def kernelEquiv (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    FiniteRepresentation.Equiv
      ((standalonePair F E f A).inertiaKernelRepresentation (localInertia E))
      (FiniteRepresentation.restrict (extensionImageWeilEquiv F E f).toMonoidHom
        (A.inertiaKernelRepresentation (inertia F (extensionFiniteIntermediate F E f)))) := by
  simpa only [inertiaKernelRepresentation, standalonePair_kernelRepresentation,
    inertia_comap F E f] using
      WeilDeligne.Transport.kernelEquiv (extensionImageWeilEquiv F E f).toMulEquiv
        A (inertia F (extensionFiniteIntermediate F E f))

/-- Comparison of the actual quotients of invariants by fixed monodromy kernels. -/
def quotientEquiv (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    FiniteRepresentation.Equiv
      (WeilDeligne.quotientRepresentation (standalonePair F E f A) (localInertia E))
      (FiniteRepresentation.restrict (extensionImageWeilEquiv F E f).toMonoidHom
        (WeilDeligne.quotientRepresentation A
          (inertia F (extensionFiniteIntermediate F E f)))) := by
  simpa only [standalonePair_quotientRepresentation, inertia_comap F E f] using
    WeilDeligne.Transport.quotientEquiv (extensionImageWeilEquiv F E f).toMulEquiv
      A (inertia F (extensionFiniteIntermediate F E f))

theorem conductorCorrection_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    WeilDeligne.conductorCorrection (standalonePair F E f A) (localInertia E) =
      WeilDeligne.conductorCorrection A (inertia F (extensionFiniteIntermediate F E f)) :=
  (quotientEquiv F E f A).toLinearEquiv.finrank_eq

theorem eulerPolynomial_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.eulerPolynomial (standalonePair F E f A) (localInertia E) w =
      WeilDeligne.eulerPolynomial A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) := by
  have hp := LocalFactor.eulerPolynomial_conj (kernelEquiv F E f A).toLinearEquiv
    (WeilDeligne.kernelOperator (standalonePair F E f A) (localInertia E) w)
  rw [Representation.Equiv.conj_apply_self] at hp
  exact hp.symm

theorem rationalLFactor_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.rationalLFactor (standalonePair F E f A) (localInertia E) w =
      WeilDeligne.rationalLFactor A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) := by
  change (algebraMap (Polynomial ℂ) (RatFunc ℂ)
    (WeilDeligne.eulerPolynomial (standalonePair F E f A) (localInertia E) w))⁻¹ =
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (WeilDeligne.eulerPolynomial A (inertia F (extensionFiniteIntermediate F E f))
          (extensionImageWeilEquiv F E f w)))⁻¹
  rw [eulerPolynomial_standalonePair]

theorem quotientDeterminant_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.quotientDeterminant (standalonePair F E f A) (localInertia E) w =
      WeilDeligne.quotientDeterminant A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) := by
  have hc := Representation.Equiv.conj_apply_self w (quotientEquiv F E f A)
  have hd := LinearMap.det_conj
    (-WeilDeligne.quotientOperator (standalonePair F E f A) (localInertia E) w)
    (quotientEquiv F E f A).toLinearEquiv
  change LinearMap.det ((quotientEquiv F E f A).toLinearEquiv.conj
    (-WeilDeligne.quotientOperator (standalonePair F E f A) (localInertia E) w)) =
      WeilDeligne.quotientDeterminant (standalonePair F E f A) (localInertia E) w at hd
  rw [map_neg, hc] at hd
  exact hd.symm

theorem quotientCorrectionPolynomial_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.quotientCorrectionPolynomial (standalonePair F E f A) (localInertia E) w =
      WeilDeligne.quotientCorrectionPolynomial A
        (inertia F (extensionFiniteIntermediate F E f)) (extensionImageWeilEquiv F E f w) := by
  simp only [WeilDeligne.quotientCorrectionPolynomial, conductorCorrection_standalonePair,
    quotientDeterminant_standalonePair]

theorem quotientCorrection_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.quotientCorrection (standalonePair F E f A) (localInertia E) w =
      WeilDeligne.quotientCorrection A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) := by
  simp only [WeilDeligne.quotientCorrection, quotientCorrectionPolynomial_standalonePair]

theorem quotientConstantCorrection_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.quotientConstantCorrection (standalonePair F E f A) (localInertia E) w =
      WeilDeligne.quotientConstantCorrection A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) := by
  apply Units.ext
  exact quotientDeterminant_standalonePair F E f A w

theorem quotientCorrectionValue_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (w : localWeilGroup E) (z : ℂˣ) :
    WeilDeligne.quotientCorrectionValue (standalonePair F E f A) (localInertia E) w z =
      WeilDeligne.quotientCorrectionValue A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) z := by
  apply Units.ext
  simp only [WeilDeligne.quotientCorrectionValue_eq_eval,
    quotientCorrectionPolynomial_standalonePair]

/-- The actual scalar regular domains correspond without changing the scalar. -/
def regularPointEquiv
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E) :
    WeilDeligne.RegularPoint (standalonePair F E f A) (localInertia E) w ≃
      WeilDeligne.RegularPoint A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) where
  toFun z := ⟨z.val, by
    change (WeilDeligne.eulerPolynomial A (inertia F (extensionFiniteIntermediate F E f))
      (extensionImageWeilEquiv F E f w)).eval z.val ≠ 0
    rw [← eulerPolynomial_standalonePair F E f A w]
    exact z.property⟩
  invFun z := ⟨z.val, by
    change (WeilDeligne.eulerPolynomial (standalonePair F E f A) (localInertia E) w).eval
      z.val ≠ 0
    rw [eulerPolynomial_standalonePair]
    exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem regularPointEquiv_val
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E)
    (z : WeilDeligne.RegularPoint (standalonePair F E f A) (localInertia E) w) :
    (regularPointEquiv F E f A w z).val = z.val := rfl

theorem regularLValue_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f)) (w : localWeilGroup E)
    (z : WeilDeligne.RegularPoint (standalonePair F E f A) (localInertia E) w) :
    WeilDeligne.regularLValue (standalonePair F E f A) (localInertia E) w z =
      WeilDeligne.regularLValue A (inertia F (extensionFiniteIntermediate F E f))
        (extensionImageWeilEquiv F E f w) (regularPointEquiv F E f A w z) := by
  apply Units.ext
  change ((WeilDeligne.eulerPolynomial (standalonePair F E f A) (localInertia E) w).eval
    z.val)⁻¹ = ((WeilDeligne.eulerPolynomial A (inertia F (extensionFiniteIntermediate F E f))
      (extensionImageWeilEquiv F E f w)).eval z.val)⁻¹
  rw [eulerPolynomial_standalonePair]

end Langlands.LocalFactor.CommonClosureWeilDeligne.Transport

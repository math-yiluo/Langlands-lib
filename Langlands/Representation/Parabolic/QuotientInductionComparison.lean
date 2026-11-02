import Langlands.Representation.Parabolic.QuotientJacquetComparison
import Langlands.Representation.Induction.Equivalences

/-! Actual induction from the quotient Levi, and its unchanged GL K0 composite. -/

noncomputable section

open CategoryTheory

namespace Langlands.GeneralLinear.BlockShape

universe uF uV uW

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : BlockShape n)

/-- Change the actual quotient acting group back to the product Levi. -/
def quotientToProductLevi :
    SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F) :=
  SmoothRep.pullbackFunctor (B.parabolicQuotientLeviContinuous F).symm

/-- The quotient-Levi action inflated through the actual quotient projection. -/
def quotientInducingRepresentation (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) V) :
    Representation ℂ (B.parabolic F) V :=
  twist (B.inflateCharacter χ).toMonoidHom
    (ρ.comp (QuotientGroup.mk' (B.unipotentRadical F)))

@[simp] theorem quotientInducingRepresentation_apply
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) V)
    (g : B.parabolic F) (v : V) :
    B.quotientInducingRepresentation χ ρ g v =
      (χ.toMonoidHom (B.leviProjection F g) : ℂ) • ρ (QuotientGroup.mk g) v := rfl

/-- Direct quotient inflation equals the existing product-Levi inducing action. -/
theorem quotientInducingRepresentation_eq
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) V) :
    B.quotientInducingRepresentation χ ρ =
      B.inducingRepresentation χ
        (ρ.comp (B.parabolicQuotientLevi F).symm.toMonoidHom) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (χ.toMonoidHom (B.leviProjection F g) : ℂ) • ρ (QuotientGroup.mk g) v =
    (χ.toMonoidHom (B.leviProjection F g) : ℂ) •
      ρ ((B.parabolicQuotientLevi F).symm (B.leviProjection F g)) v
  exact congrArg (fun q => (χ.toMonoidHom (B.leviProjection F g) : ℂ) • ρ q v)
    ((B.parabolicQuotientLevi F).symm_apply_apply (QuotientGroup.mk g)).symm

/-- Actual smooth induction after the inverse change of Levi model. -/
def normalizedQuotientInductionFunctorOf
    (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) :=
  B.quotientToProductLevi ⋙ B.normalizedInductionFunctorOf χ

/-- The direct quotient covariance model compares by identity on original vectors. -/
def quotientInducingEquiv
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) V) :
    (B.quotientInducingRepresentation χ ρ).Equiv
      (B.inducingRepresentation χ
        (ρ.comp (B.parabolicQuotientLevi F).symm.toMonoidHom)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
    rw [B.quotientInducingRepresentation_eq]
    rfl

/-- Every induced function is retained pointwise by the comparison. -/
def quotientInducedEquiv
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) V) :
    (Induction.smoothInduced (B.parabolic F)
      (B.quotientInducingRepresentation χ ρ)).Equiv
        (B.normalizedInducedOf χ
          (ρ.comp (B.parabolicQuotientLevi F).symm.toMonoidHom)) :=
  Induction.smoothInducedEquiv _ (B.quotientInducingEquiv χ ρ)

@[simp] theorem quotientInducedEquiv_eval
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.parabolic F ⧸ B.unipotentRadical F) V)
    (f : Induction.SmoothFunctions (B.parabolic F) (B.quotientInducingRepresentation χ ρ))
    (g : GeneralLinear n F) :
    Induction.eval (B.parabolic F)
      (B.inducingRepresentation χ (ρ.comp (B.parabolicQuotientLevi F).symm.toMonoidHom))
      (B.quotientInducedEquiv χ ρ f) g =
        Induction.eval (B.parabolic F) (B.quotientInducingRepresentation χ ρ) f g := rfl

/-- Intertwiners of the quotient model still act by postcomposition on functions. -/
theorem normalizedQuotientInductionFunctorOf_map_eval
    (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {A C : SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F)}
    (f : A ⟶ C) (φ : (B.normalizedQuotientInductionFunctorOf χ).obj A)
    (g : GeneralLinear n F) :
    Induction.eval (B.parabolic F) _
      (SmoothRep.hom ((B.normalizedQuotientInductionFunctorOf χ).map f) φ) g =
        SmoothRep.hom f (Induction.eval (B.parabolic F) _ φ g) := rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

private theorem quotientInduction_isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Actual quotient-Levi induction with the existing positive block half modulus. -/
def normalizedQuotientInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.parabolic F.Carrier ⧸ B.unipotentRadical F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := quotientInduction_isTopologicalRing F T
  B.normalizedQuotientInductionFunctorOf (T.leviHalfCharacter B)

/-- Actual quotient-Levi induction preserves finite length at the existing universe. -/
theorem normalizedQuotientInductionK0_hasFiniteLength :
    letI := T.topology
    SmoothRep.PreservesFiniteLength
      (normalizedQuotientInductionFunctor.{uF, max uF uV} F T B) := by
  let := T.topology
  let := quotientInduction_isTopologicalRing F T
  exact (SmoothRep.pullbackFunctor_preservesFiniteLength
    (B.parabolicQuotientLeviContinuous F.Carrier).symm).comp
      (normalizedInductionK0_hasFiniteLength.{uF, uV} F T B)

/-- Induction from the quotient Levi on full actual exact finite-length K0. -/
def normalizedQuotientInductionK0 :
    letI := T.topology
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
      (B.parabolic F.Carrier ⧸ B.unipotentRadical F.Carrier) →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  letI := quotientInduction_isTopologicalRing F T
  SmoothRep.FiniteLengthGrothendieckGroup.map
    (normalizedQuotientInductionFunctor F T B)
    ((SmoothRep.pullbackFunctor_preservesFiniteLength
      (B.parabolicQuotientLeviContinuous F.Carrier).symm).comp
        (normalizedInductionK0_hasFiniteLength.{uF, uV} F T B))
    (SmoothRep.PreservesFiniteLengthShortExact.comp
      (SmoothRep.pullbackFunctor_preservesFiniteLength
        (B.parabolicQuotientLeviContinuous F.Carrier).symm)
      (SmoothRep.pullbackFunctor_preservesShortExact
        (B.parabolicQuotientLeviContinuous F.Carrier).symm)
      (FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact F T B))

/-- The quotient induction map sends every actual class to its actual induction. -/
theorem normalizedQuotientInductionK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ
        (B.parabolic F.Carrier ⧸ B.unipotentRadical F.Carrier))
      (hA : A.HasFiniteLength)
      (hOut : ((normalizedQuotientInductionFunctor F T B).obj A).HasFiniteLength),
      normalizedQuotientInductionK0.{uF, uV} F T B
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
          GeneralLinear.finiteLengthClass n F.Carrier
            ((normalizedQuotientInductionFunctor F T B).obj A) hOut := by
  let := T.topology
  let := quotientInduction_isTopologicalRing F T
  intro A hA hOut
  unfold normalizedQuotientInductionK0
  exact SmoothRep.FiniteLengthGrothendieckGroup.map_ofRepresentation _ _ _ A hA

/-- Equality of whole exact-K0 maps after inverse actual Levi transport. -/
theorem normalizedQuotientInductionK0_eq :
    letI := T.topology
    letI := quotientInduction_isTopologicalRing F T
    normalizedQuotientInductionK0.{uF, uV} F T B =
      (normalizedInductionK0.{uF, uV} F T B).comp
        (quotientLeviK0Equiv B).symm.toLinearMap := by
  let := T.topology
  let := quotientInduction_isTopologicalRing F T
  exact SmoothRep.FiniteLengthGrothendieckGroup.map_comp _ _
    (SmoothRep.pullbackFunctor_preservesFiniteLength
      (B.parabolicQuotientLeviContinuous F.Carrier).symm)
    (SmoothRep.pullbackFunctor_preservesShortExact
      (B.parabolicQuotientLeviContinuous F.Carrier).symm)
    (normalizedInductionK0_hasFiniteLength.{uF, uV} F T B)
    (FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact F T B)
    _ _

/-- The quotient-Levi induction--Jacquet composite is the existing GL composite. -/
theorem normalizedQuotientInductionJacquetK0_eq :
    letI := T.topology
    (normalizedQuotientInductionK0.{uF, uV} F T B).comp
      (normalizedQuotientJacquetK0.{uF, uV} F T B) =
        (normalizedInductionK0.{uF, uV} F T B).comp
          (normalizedJacquetK0.{uF, uV} F T B) := by
  let := T.topology
  let := quotientInduction_isTopologicalRing F T
  rw [normalizedQuotientInductionK0_eq, normalizedQuotientJacquetK0_eq]
  apply LinearMap.ext
  intro x
  exact congrArg (normalizedInductionK0.{uF, uV} F T B)
    ((quotientLeviK0Equiv B).symm_apply_apply (normalizedJacquetK0.{uF, uV} F T B x))

end Langlands.Parabolic

namespace Langlands.Aubert

universe uF uV

/-- Reexpress the unchanged GL operator through actual quotient-Levi functors. -/
theorem alternatingOperator_eq_quotientLevi_sum
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) [Fintype (GeneralLinear.BlockShape n)] :
    letI := T.topology
    alternatingOperator.{uF, uV} F T n =
      ∑ B : GeneralLinear.BlockShape n, ((-1 : ℤ) ^ (n - B.length)) •
        (Parabolic.normalizedQuotientInductionK0.{uF, uV} F T B).comp
          (Parabolic.normalizedQuotientJacquetK0.{uF, uV} F T B) := by
  let := T.topology
  rw [alternatingOperator_eq_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [Parabolic.normalizedQuotientInductionJacquetK0_eq]

end Langlands.Aubert

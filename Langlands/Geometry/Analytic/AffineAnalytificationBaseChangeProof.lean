import Langlands.Geometry.Analytic.AnalytificationCenterComparison
import Langlands.Geometry.Analytic.AffineAnalytificationBaseChangeStatement
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.ValuedField.TensorSeminorm
import Langlands.Geometry.Analytic.Spectrum.NonarchimedeanDominationProof
import Langlands.Geometry.Analytic.ValuedField.SeminormRealizationProof

/-! # Ground-field extension of affine analytification -/

noncomputable section

universe u u' v

namespace Langlands.Analytic.AffineAnalytification

open Set Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct

namespace BaseChangeComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A]

/-- Realize a scalar-normalized seminorm by a norm-preserving algebra map. -/
theorem normedRealization (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν) :
    ∃ (H : Type v) (_ : NormedField H) (_ : IsUltrametricDist H)
      (_ : CompleteSpace H) (_ : NormedAlgebra K H) (f : A →ₐ[K] H),
      ∀ a, ‖f a‖ = ν a := by
  obtain ⟨H, _, _, _, f, hf⟩ :=
    seminormRealization A ν (SeminormComparison.add_le_max hν)
  let : Algebra K H := (f.comp (algebraMap K A)).toAlgebra
  have hc (c : K) : ‖algebraMap K H c‖ = ‖c‖ := (hf _).trans (hν c)
  let : NormedAlgebra K H := {
    norm_smul_le c a := by rw [Algebra.smul_def, norm_mul, hc]
  }
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
    { toRingHom := f, commutes' := fun _ => rfl }, hf⟩

/-- Restrict a multiplicative seminorm along a ring homomorphism. -/
def pullback {R S : Type*} [CommRing R] [CommRing S]
    (ν : MulRingSeminorm S) (f : R →+* S) : MulRingSeminorm R where
  toFun a := ν (f a)
  map_zero' := by rw [map_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  add_le' a b := by rw [map_add]; exact map_add_le_add ν _ _
  neg' a := by rw [map_neg, map_neg_eq_map]

/-- A contractive restriction of a multiplicative seminorm to a field is its norm. -/
theorem field_restriction {F R : Type*} [NormedField F] [CommRing R]
    (ν : MulRingSeminorm R) (f : F →+* R) (hf : ∀ a, ν (f a) ≤ ‖a‖) (a : F) :
    ν (f a) = ‖a‖ := by
  let x : BanachSpectrum F := {
    toMulRingSeminorm := pullback ν f
    le_norm := hf
  }
  exact BanachSpectrum.field_apply x a

variable (K) (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

/-- Extend a scalar-normalized seminorm to the scalar extension of its algebra. -/
theorem exists_extension (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν) :
    ∃ μ : MulRingSeminorm (L ⊗[K] A), ExtendsNorm L μ ∧
      ∀ a, μ ((1 : L) ⊗ₜ[K] a) = ν a := by
  obtain ⟨H, _, _, _, _, f, hf⟩ := normedRealization ν hν
  obtain ⟨p, hp1, hpna, hpL, hpH⟩ :=
    exists_ultrametricTensorSeminorm (E := K) (F := L) (G := H)
  obtain ⟨q, _, hqp⟩ := BanachSpectrum.nonarchimedeanDomination (L ⊗[K] H) p hp1 hpna
  have hL (l : L) : q (l ⊗ₜ[K] (1 : H)) = ‖l‖ :=
    field_restriction q Algebra.TensorProduct.includeLeftRingHom
      (fun l => (hqp _).trans (hpL l)) l
  have hH (h : H) : q ((1 : L) ⊗ₜ[K] h) = ‖h‖ :=
    field_restriction q Algebra.TensorProduct.includeRight.toRingHom
      (fun h => (hqp _).trans (hpH h)) h
  let g : L ⊗[K] A →ₐ[L] L ⊗[K] H :=
    Algebra.TensorProduct.map (AlgHom.id L L) f
  refine ⟨pullback q g.toRingHom, ?_, ?_⟩
  · intro l
    change q (g (algebraMap L (L ⊗[K] A) l)) = ‖l‖
    rw [g.commutes]
    exact hL l
  · intro a
    change q (g ((1 : L) ⊗ₜ[K] a)) = ν a
    rw [Algebra.TensorProduct.map_tmul]
    exact (hH (f a)).trans (hf a)

variable [CompleteSpace K] [CompleteSpace L] (P : FinitePolynomialPresentation K A)

/-- Every seminorm on the original coordinate algebra lifts to the scalar extension. -/
theorem surjective_baseChangeMap : Function.Surjective (baseChangeMap K L P) := by
  intro x
  obtain ⟨μ, hμ, hμx⟩ :=
    exists_extension K L (pointSeminorm K P x) (pointSeminorm_extendsNorm K P x)
  have hmem : μ ∈ range (pointSeminorm L (baseChangePresentation K L P)) := by
    rw [SeminormComparison.range_pointSeminorm]
    exact hμ
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, SeminormComparison.pointSeminorm_injective K P ?_⟩
  ext a
  rw [pointSeminorm_baseChangeMap, hy, hμx]

/-- The algebraic character on the scalar extension of a rational point. -/
def rationalLift (φ : AlgPoint K A K) : L ⊗[K] A →ₐ[L] L :=
  Algebra.TensorProduct.liftEquivRight K L A L
    (AlgPoint.mapCoefficients (Algebra.ofId K L) φ).toAlgHom

omit [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K] [CompleteSpace L] in
theorem rationalLift_tmul (φ : AlgPoint K A K) (l : L) (a : A) :
    rationalLift K L φ (l ⊗ₜ[K] a) = l * algebraMap K L (φ a) :=
  rfl

theorem baseChangeMap_analyticPoint (φ : AlgPoint K A K) :
    baseChangeMap K L P
      (analyticPoint L (baseChangePresentation K L P) (AlgPoint.ofAlgHom (rationalLift K L φ))) =
        analyticPoint K P φ := by
  apply SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [pointSeminorm_baseChangeMap, CenterComparison.pointSeminorm_analyticPoint,
    CenterComparison.pointSeminorm_analyticPoint]
  change ‖rationalLift K L φ ((1 : L) ⊗ₜ[K] a)‖ = ‖φ a‖
  rw [rationalLift_tmul, one_mul, norm_algebraMap']

/-- A point above a rational point has the rationally extended character's seminorm. -/
theorem eq_analyticPoint_of_baseChangeMap (φ : AlgPoint K A K)
    (y : Space L (baseChangePresentation K L P))
    (hy : baseChangeMap K L P y = analyticPoint K P φ) :
    y = analyticPoint L (baseChangePresentation K L P) (AlgPoint.ofAlgHom (rationalLift K L φ)) := by
  obtain ⟨H, _, _, _, _, f, hf⟩ := normedRealization
    (pointSeminorm L (baseChangePresentation K L P) y)
    (pointSeminorm_extendsNorm L (baseChangePresentation K L P) y)
  have ha (a : A) :
      f ((1 : L) ⊗ₜ[K] a) = algebraMap L H (algebraMap K L (φ a)) := by
    have hzero : ‖f ((1 : L) ⊗ₜ[K] (a - algebraMap K A (φ a)))‖ = 0 := by
      rw [hf, ← pointSeminorm_baseChangeMap, hy, CenterComparison.pointSeminorm_analyticPoint]
      change ‖φ.toAlgHom (a - algebraMap K A (φ a))‖ = 0
      rw [map_sub, φ.toAlgHom.commutes]
      change ‖φ a - φ a‖ = 0
      rw [sub_self, norm_zero]
    have hz := norm_eq_zero.mp hzero
    rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at hz
    calc
      f ((1 : L) ⊗ₜ[K] a) = f ((1 : L) ⊗ₜ[K] algebraMap K A (φ a)) := hz
      _ = algebraMap L H (algebraMap K L (φ a)) := by
        rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply K L,
          f.commutes]
  have heq : f = (Algebra.ofId L H).comp (rationalLift K L φ) := by
    apply AlgHom.ext
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul l a =>
      have h1 : f ((1 : L) ⊗ₜ[K] a) =
          ((Algebra.ofId L H).comp (rationalLift K L φ)) ((1 : L) ⊗ₜ[K] a) := by
        change f ((1 : L) ⊗ₜ[K] a) =
          algebraMap L H (rationalLift K L φ ((1 : L) ⊗ₜ[K] a))
        rw [rationalLift_tmul, one_mul]
        exact ha a
      have ht : l ⊗ₜ[K] a = l • ((1 : L) ⊗ₜ[K] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul, map_smul, h1]
    | add b c hb hc => simp only [map_add, hb, hc]
  apply SeminormComparison.pointSeminorm_injective L (baseChangePresentation K L P)
  ext b
  rw [CenterComparison.pointSeminorm_analyticPoint, ← hf, heq]
  change ‖algebraMap L H (rationalLift K L φ b)‖ = ‖rationalLift K L φ b‖
  exact norm_algebraMap' H _

end BaseChangeComparison

open BaseChangeComparison in
/-- Ground-field extension is surjective and has singleton fibres over rational points. -/
theorem affineAnalytificationBaseChange : AffineAnalytificationBaseChangeStatement.{u, u', v} := by
  intro K _ _ _ L _ _ _ _ A _ _ P
  refine ⟨surjective_baseChangeMap K L P, fun φ => ?_⟩
  ext y
  change baseChangeMap K L P y = analyticPoint K P φ ↔
    y = analyticPoint L (baseChangePresentation K L P) (AlgPoint.ofAlgHom (rationalLift K L φ))
  constructor
  · exact eq_analyticPoint_of_baseChangeMap K L P φ y
  · rintro rfl
    exact baseChangeMap_analyticPoint K L P φ

end Langlands.Analytic.AffineAnalytification

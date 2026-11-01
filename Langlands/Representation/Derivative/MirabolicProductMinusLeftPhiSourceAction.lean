import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization

/-! The actual normalized source-Phi tensor quotient on the lower left subgroup. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  Jacquet.Localization MixedProductTensor

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

variable (k r : ℕ) (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (B : letI := T.topology
  SmoothRep.{0, uF, uW} ℂ (mirabolic (r + 1) F.Carrier))

/-- The actual higher coefficient restricted to the lower successor pair, with
the full ambient Phi normalization included. -/
def leftPhiHigherSectionRepresentation :
    letI := T.topology
    Representation ℂ (leftSubgroup (k + 1) r F.Carrier) (V ⊗[ℂ] B) :=
  letI := T.topology
  twist (leftPhiSectionCharacter T (k + 1) r)
    (leftInducingRepresentation ρ (B.representation.comp successor))

/-- The inducing coefficient of the lower left mixed product, using the actual
normalized source Phi-minus object. -/
def leftPhiSourceCoefficient :
    letI := T.topology
    Representation ℂ (leftSubgroup (k + 1) r F.Carrier)
      (V ⊗[ℂ] (Mirabolic.phiMinus T ψ r).obj B) :=
  letI := T.topology
  twist (T.leftCharacter (k + 1) r).toMonoidHom
    (leftInducingRepresentation ρ ((Mirabolic.phiMinus T ψ r).obj B).representation)

/-- The source Phi action combines with the lower covariance character to give
exactly the higher section character, with no remaining scalar. -/
theorem leftPhiSourceCoefficient_tmul_quotient
    (h : leftSubgroup (k + 1) r F.Carrier) (v : V) (w : B) :
    letI := T.topology
    leftPhiSourceCoefficient T k r ψ ρ B h
        (v ⊗ₜ[ℂ] Mirabolic.phiMinusQuotient T ψ r B w) =
      (leftPhiSectionCharacter T (k + 1) r h : ℂ) •
        (ρ (leftProjection h).1 v ⊗ₜ[ℂ]
          Mirabolic.phiMinusQuotient T ψ r B
            (B.representation (successor (leftProjection h).2) w)) := by
  let := T.topology
  change (T.leftLeviCharacter (k + 1) r (leftProjection h) : ℂ) •
      (ρ (leftProjection h).1 v ⊗ₜ[ℂ]
        ((Mirabolic.phiMinus T ψ r).obj B).representation (leftProjection h).2
          (Mirabolic.phiMinusQuotient T ψ r B w)) = _
  rw [Mirabolic.phiMinus_action]
  change (T.leftLeviCharacter (k + 1) r (leftProjection h) : ℂ) •
      (ρ (leftProjection h).1 v ⊗ₜ[ℂ]
        ((Mirabolic.phiMinusCharacter T r (leftProjection h).2 : ℂ) •
          Mirabolic.phiMinusQuotient T ψ r B
            (B.representation (successor (leftProjection h).2) w))) =
    (leftPhiSectionCharacter T (k + 1) r h : ℂ) •
      (ρ (leftProjection h).1 v ⊗ₜ[ℂ]
        Mirabolic.phiMinusQuotient T ψ r B
          (B.representation (successor (leftProjection h).2) w))
  rw [TensorProduct.tmul_smul, smul_smul]
  have hc := DFunLike.congr_fun (leftPhiSectionCharacter_eq T (k + 1) r) h
  change leftPhiSectionCharacter T (k + 1) r h =
    T.leftLeviCharacter (k + 1) r (leftProjection h) *
      Mirabolic.phiMinusCharacter T r (leftProjection h).2 at hc
  rw [hc, Units.val_mul]

/-- Tensoring the actual source Phi quotient gives an intertwiner between the
actual normalized higher-section and lower-inducing representations. -/
def leftPhiSourceQuotient :
    letI := T.topology
    (leftPhiHigherSectionRepresentation T k r ρ B).IntertwiningMap
      (leftPhiSourceCoefficient T k r ψ ρ B) :=
  letI := T.topology
  {
  toLinearMap := TensorProduct.map LinearMap.id (Mirabolic.phiMinusQuotient T ψ r B)
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro v w
    change TensorProduct.map LinearMap.id (Mirabolic.phiMinusQuotient T ψ r B)
        ((leftPhiSectionCharacter T (k + 1) r h : ℂ) •
          (ρ (leftProjection h).1 v ⊗ₜ[ℂ]
            B.representation (successor (leftProjection h).2) w)) = _
    rw [map_smul, TensorProduct.map_tmul, LinearMap.id_apply]
    exact (leftPhiSourceCoefficient_tmul_quotient T k r ψ ρ B h v w).symm
  }

@[simp] theorem leftPhiSourceQuotient_tmul (v : V) (w : B) :
    letI := T.topology
    leftPhiSourceQuotient T k r ψ ρ B (v ⊗ₜ[ℂ] w) =
      v ⊗ₜ[ℂ] Mirabolic.phiMinusQuotient T ψ r B w := rfl

/-- As a linear map, this is precisely the published orbit quotient followed
by its identity-orbit tensor equivalence. -/
theorem leftPhiSourceQuotient_factor :
    letI := T.topology
    (leftPhiSourceQuotient T k r ψ ρ B).toLinearMap =
      (leftPhiTensorEquiv k r ψ ρ B.representation).toLinearMap ∘ₗ
        leftPhiCoefficientMk k r ψ ρ B.representation 1 := by
  let := T.topology
  apply TensorProduct.ext'
  intro v w
  rfl

/-- The normalized intertwiner is onto the entire tensor with the source
Phi carrier, including zero and infinite-dimensional representations. -/
theorem leftPhiSourceQuotient_surjective :
    letI := T.topology
    Function.Surjective (leftPhiSourceQuotient T k r ψ ρ B) := by
  let := T.topology
  change Function.Surjective (leftPhiSourceQuotient T k r ψ ρ B).toLinearMap
  rw [leftPhiSourceQuotient_factor]
  exact (leftPhiTensorEquiv k r ψ ρ B.representation).surjective.comp
    (mk_surjective (leftPhiOrbitRepresentation k r ρ B.representation 1) ⊤
      (leftPhiOrbitCharacter k r ψ 1))

/-- Its kernel is exactly the actual identity-orbit radical relation span. -/
theorem ker_leftPhiSourceQuotient :
    letI := T.topology
    LinearMap.ker (leftPhiSourceQuotient T k r ψ ρ B).toLinearMap =
      relations (leftPhiOrbitRepresentation k r ρ B.representation 1) ⊤
        (leftPhiOrbitCharacter k r ψ 1) := by
  let := T.topology
  rw [leftPhiSourceQuotient_factor]
  ext x
  change leftPhiTensorEquiv k r ψ ρ B.representation
      (leftPhiCoefficientMk k r ψ ρ B.representation 1 x) = 0 ↔ _
  rw [← (leftPhiTensorEquiv k r ψ ρ B.representation).map_zero,
    (leftPhiTensorEquiv k r ψ ρ B.representation).injective.eq_iff]
  exact mk_eq_zero (leftPhiOrbitRepresentation k r ρ B.representation 1) ⊤
    (leftPhiOrbitCharacter k r ψ 1) x

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {B' : letI := T.topology
  SmoothRep.{0, uF, uW'} ℂ (mirabolic (r + 1) F.Carrier)}

/-- Arbitrary maps in both coefficient factors intertwine the higher normalized
section action, with independent carrier universes. -/
def leftPhiHigherSectionMap
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation) :
    letI := T.topology
    (leftPhiHigherSectionRepresentation T k r ρ B).IntertwiningMap
      (leftPhiHigherSectionRepresentation T k r ρ' B') :=
  letI := T.topology
  twistIntertwining (leftPhiSectionCharacter T (k + 1) r)
    (pullbackMap leftProjection (externalMap f (pullbackMap successor g)))

/-- The normalized source quotient commutes with arbitrary input intertwiners;
the map of the source quotient is its actual relation-quotient map. -/
theorem leftPhiSourceQuotient_naturality
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation)
    (x : V ⊗[ℂ] B) :
    letI := T.topology
    leftPhiSourceQuotient T k r ψ ρ' B'
        (leftPhiHigherSectionMap T k r ρ B f g x) =
      TensorProduct.map f.toLinearMap
        (mapLinear (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) g)
        (leftPhiSourceQuotient T k r ψ ρ B x) := by
  let := T.topology
  have hm :
      (leftPhiSourceQuotient T k r ψ ρ' B').toLinearMap ∘ₗ
          (leftPhiHigherSectionMap T k r ρ B f g).toLinearMap =
        TensorProduct.map f.toLinearMap
            (mapLinear (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) g) ∘ₗ
          (leftPhiSourceQuotient T k r ψ ρ B).toLinearMap := by
    apply TensorProduct.ext'
    intro v w
    rfl
  exact LinearMap.congr_fun hm x

/-- The input tensor map descends to an intertwiner of the actual normalized
lower coefficients, including input maps between independent universes. -/
def leftPhiSourceCoefficientMap
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation) :
    letI := T.topology
    (leftPhiSourceCoefficient T k r ψ ρ B).IntertwiningMap
      (leftPhiSourceCoefficient T k r ψ ρ' B') :=
  letI := T.topology
  {
  toLinearMap := TensorProduct.map f.toLinearMap
    (mapLinear (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) g)
  isIntertwining' h := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := leftPhiSourceQuotient_surjective T k r ψ ρ B z
    let q := leftPhiSourceQuotient T k r ψ ρ B
    let q' := leftPhiSourceQuotient T k r ψ ρ' B'
    let a := leftPhiHigherSectionMap T k r ρ B f g
    let m := TensorProduct.map f.toLinearMap
      (mapLinear (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) g)
    change m (leftPhiSourceCoefficient T k r ψ ρ B h (q x)) =
      leftPhiSourceCoefficient T k r ψ ρ' B' h (m (q x))
    refine (congrArg m
      (Representation.IntertwiningMap.isIntertwining _ _ q h x).symm).trans ?_
    refine (leftPhiSourceQuotient_naturality T k r ψ ρ B f g
      (leftPhiHigherSectionRepresentation T k r ρ B h x)).symm.trans ?_
    refine (congrArg q'
      (Representation.IntertwiningMap.isIntertwining _ _ a h x)).trans ?_
    refine (Representation.IntertwiningMap.isIntertwining _ _ q' h (a x)).trans ?_
    exact congrArg (leftPhiSourceCoefficient T k r ψ ρ' B' h)
      (leftPhiSourceQuotient_naturality T k r ψ ρ B f g x)
  }

/-- Naturality as an equality involving the two actual coefficient intertwiners. -/
theorem leftPhiSourceQuotient_natural
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation)
    (x : V ⊗[ℂ] B) :
    letI := T.topology
    leftPhiSourceQuotient T k r ψ ρ' B'
        (leftPhiHigherSectionMap T k r ρ B f g x) =
      leftPhiSourceCoefficientMap T k r ψ ρ B f g
        (leftPhiSourceQuotient T k r ψ ρ B x) :=
  leftPhiSourceQuotient_naturality T k r ψ ρ B f g x

end Langlands.Derivative.MirabolicProductMinus

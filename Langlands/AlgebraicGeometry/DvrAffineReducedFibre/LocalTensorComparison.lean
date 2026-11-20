import Langlands.CommutativeAlgebra.IntegralClosureTransfer
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.CompleteBaseLocalCriterion

/-! # Tensor comparison for normalization at an original prime -/

open IsLocalRing TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section IntegralClosure

variable {D H D' H' : Type*} [CommRing D] [CommRing H] [Algebra D H]
    [CommRing D'] [CommRing H'] [Algebra D' H']

end IntegralClosure

section Exchange

variable (R S B Q X : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra R B] [CommRing Q] [Algebra R Q] [Algebra B Q]
    [IsScalarTower R B Q] [CommRing X] [Algebra R X] [Algebra B X] [IsScalarTower R B X]

local instance : Algebra X (S ⊗[R] X) := Algebra.TensorProduct.rightAlgebra
local instance : Algebra B (S ⊗[R] X) := Algebra.compHom _ (algebraMap B X)
local instance : Algebra B (X ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
local instance : Algebra R (Q ⊗[B] X) := Algebra.TensorProduct.leftAlgebra

private def tensorCommOverRight : S ⊗[R] X ≃ₐ[B] X ⊗[R] S :=
  { (Algebra.TensorProduct.comm R S X).toRingEquiv with commutes' := fun _ => rfl }

/-- Exchanging the order of two scalar extensions, with one factor over the
base of the original algebra. -/
def tensorScalarExchangeEquiv :
    Q ⊗[B] (S ⊗[R] X) ≃+* S ⊗[R] (Q ⊗[B] X) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Q ≃ₐ[B] Q)
    (tensorCommOverRight R S B X)).toRingEquiv.trans
    ((Algebra.TensorProduct.assoc R B B Q X S).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm R (Q ⊗[B] X) S).toRingEquiv)

@[simp]
theorem tensorScalarExchangeEquiv_tmul (q : Q) (s : S) (x : X) :
    tensorScalarExchangeEquiv R S B Q X (q ⊗ₜ[B] (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (q ⊗ₜ[B] x) := rfl

end Exchange

section Normalization

variable (R S B Q G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra R B] [CommRing Q] [Algebra R Q] [Algebra B Q]
    [IsScalarTower R B Q] [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]

local notation "D" => S ⊗[R] B
local notation "H" => S ⊗[R] G
local notation "G'" => Q ⊗[B] G
local notation "D₁" => Q ⊗[B] D
local notation "H₁" => Q ⊗[B] H
local notation "D₂" => S ⊗[R] Q
local notation "H₂" => S ⊗[R] G'

local instance : Algebra D H := tensorBaseChangeAlgebra R S B (B := G)
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S B (B := G)
local instance : Algebra B D := Algebra.TensorProduct.rightAlgebra
local instance : Algebra G H := Algebra.TensorProduct.rightAlgebra
local instance : Algebra B H := Algebra.compHom H (algebraMap B G)
local instance : IsScalarTower B D H := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance : Algebra R G' := Algebra.TensorProduct.leftAlgebra
local instance : IsScalarTower R Q G' := TensorProduct.isScalarTower_left
local instance : Algebra D₁ H₁ := tensorBaseChangeAlgebra B Q D (B := H)
local instance : Algebra D₂ H₂ := tensorBaseChangeAlgebra R S Q (B := G')
local instance : IsScalarTower S D₂ H₂ := tensorBaseChangeAlgebra_isScalarTower R S Q (B := G')

private def tensorScalarExchangeSelfEquiv : D₁ ≃+* D₂ :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Q ≃ₐ[B] Q)
    (tensorCommOverRight R S B B)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange R B B Q S).toRingEquiv.trans
      (Algebra.TensorProduct.comm R Q S).toRingEquiv)

private theorem tensorScalarExchange_commutes (x : D₁) :
    tensorScalarExchangeEquiv R S B Q G (algebraMap D₁ H₁ x) =
      algebraMap D₂ H₂ (tensorScalarExchangeSelfEquiv R S B Q x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q d =>
    induction d using TensorProduct.inductionOn with
    | tmul s b =>
      change s ⊗ₜ[R] (q ⊗ₜ[B] algebraMap B G b) = s ⊗ₜ[R] ((b • q) ⊗ₜ[B] (1 : G))
      rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The two orders of forming the tensor extensions give the same
integral closure. -/
def tensorScalarExchangeIntegralClosureEquiv :
    integralClosure D₁ H₁ ≃+* integralClosure D₂ H₂ :=
  Langlands.CommutativeAlgebra.IntegralClosureTransfer.integralClosureEquiv (tensorScalarExchangeSelfEquiv R S B Q)
    (tensorScalarExchangeEquiv R S B Q G)
    (tensorScalarExchange_commutes R S B Q G)

end Normalization

section MaximalLocalizations

variable (C : Type*) [CommRing C]

/-- The scalar generates the maximal ideal in every maximal localization. -/
abbrev UniformizerAtMaximalLocalizations (x : C) : Prop :=
  ∀ (J : Ideal C) (hJ : J.IsMaximal), letI : J.IsPrime := hJ.isPrime
    Ideal.span {algebraMap C (Localization.AtPrime J) x} =
      maximalIdeal (Localization.AtPrime J)

variable {C} {C' : Type*} [CommRing C']

private theorem uniformizerAtMaximalLocalizations_of_ringEquiv (e : C ≃+* C') (x : C)
    (h : UniformizerAtMaximalLocalizations C' (e x)) :
    UniformizerAtMaximalLocalizations C x := by
  intro J hJ
  have : J.IsPrime := hJ.isPrime
  let q := J.comap e.symm.toRingHom
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm e.symm.surjective
  have : q.IsPrime := hq.isPrime
  have hJq : J = q.comap e.toRingHom := (Ideal.comap_of_equiv e).symm
  let f := Localization.localRingEquiv J q e hJq
  have hf : f (algebraMap C (Localization.AtPrime J) x) =
      algebraMap C' (Localization.AtPrime q) (e x) :=
    Localization.localRingHom_to_map J q e.toRingHom hJq x
  have hf' : f.symm (algebraMap C' (Localization.AtPrime q) (e x)) =
      algebraMap C (Localization.AtPrime J) x := by
    rw [← hf, f.symm_apply_apply]
  have hm := congrArg (Ideal.map f.symm.toRingHom) (h q hq)
  rw [Ideal.map_span, Set.image_singleton] at hm
  exact (congrArg (fun z : Localization.AtPrime J => Ideal.span {z}) hf'.symm).trans
    (hm.trans (IsLocalRing.map_ringEquiv_maximalIdeal f.symm))

/-- The generation test at maximal ideals is invariant under a ring
isomorphism carrying the chosen scalar. -/
theorem uniformizerAtMaximalLocalizations_iff (e : C ≃+* C') (x : C) :
    UniformizerAtMaximalLocalizations C' (e x) ↔ UniformizerAtMaximalLocalizations C x := by
  refine ⟨uniformizerAtMaximalLocalizations_of_ringEquiv e x, fun h => ?_⟩
  exact uniformizerAtMaximalLocalizations_of_ringEquiv e.symm (e x) (by simpa only
    [e.symm_apply_apply] using h)

end MaximalLocalizations

section AtPrime

variable (R S B G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra R B] [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]
    (p : Ideal B) [p.IsPrime]

local notation "Q" => Localization.AtPrime p
local notation "D" => S ⊗[R] Q
local notation "H" => S ⊗[R] (Q ⊗[B] G)
local instance : Algebra R (Q ⊗[B] G) := Algebra.TensorProduct.leftAlgebra
local instance : IsScalarTower R Q (Q ⊗[B] G) := TensorProduct.isScalarTower_left
local instance : Algebra D H := tensorBaseChangeAlgebra R S Q
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S Q
local instance : CommRing (integralClosure D H) :=
  @Subalgebra.toCommRing D H _ _ _ (integralClosure D H)

/-- The local tensor normalization agrees with the integral closure of the
base change of the original local ring in the base change of its localized
ambient algebra. -/
def localTensorNormalizationEquiv :
    localTensorNormalization R S B G p ≃+* integralClosure D H :=
  tensorScalarExchangeIntegralClosureEquiv R S B Q G

theorem localTensorNormalizationEquiv_baseMap (s : S) :
    localTensorNormalizationEquiv R S B G p (localTensorNormalizationBaseMap R S B G p s) =
      algebraMap S (integralClosure D H) s := by
  rfl

set_option maxHeartbeats 800000 in
/-- The local test can be made in the normalization of the base change of the
original local ring. -/
theorem localUniformizerTest_iff (t : S) :
    LocalUniformizerTest R S B G t p ↔
      UniformizerAtMaximalLocalizations (integralClosure D H)
        (algebraMap S (integralClosure D H) t) := by
  let e := localTensorNormalizationEquiv R S B G p
  let x := localTensorNormalizationBaseMap R S B G p t
  have h := uniformizerAtMaximalLocalizations_iff e x
  exact h.symm.trans (iff_of_eq (congrArg
    (UniformizerAtMaximalLocalizations (integralClosure D H))
    (localTensorNormalizationEquiv_baseMap R S B G p t)))

end AtPrime

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre

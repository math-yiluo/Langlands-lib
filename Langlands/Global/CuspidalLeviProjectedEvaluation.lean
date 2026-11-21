import Langlands.Global.CuspidalLeviPeriodEvaluation
import Langlands.Automorphic.HeckeTwist.ContragredientTwist

/-! # Restored cuspidal projections of a Levi coefficient tensor -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 120000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F]

local instance leviProjectionRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance leviProjectionContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance leviProjectionSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance leviProjectionFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance leviProjectionStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance leviProjectionRealizationGroup {d : ℕ} (S : OperatorRealization F d) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance leviProjectionOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

section TwistMap

variable {n : ℕ} {S T : OperatorRealization F n}
  (p : S.representation.IntertwiningMap T.representation) (ν : HeckeCharacter F)

private abbrev twistEquiv (S : OperatorRealization F n) :=
  (S.heckeDeterminantTwistEquiv ν).toLinearEquiv

/-- Transport a full block intertwiner through the same determinant twist on both sides. -/
def twistedBlockProjection : (S.heckeDeterminantTwist ν).Space →ₗ[ℂ] (T.heckeDeterminantTwist ν).Space :=
  (twistEquiv ν T).toLinearMap.comp (p.toLinearMap.comp (twistEquiv ν S).symm.toLinearMap)

@[simp]
theorem twistedBlockProjection_apply_twist (x : S.Space) :
    twistedBlockProjection p ν (twistEquiv ν S x) = twistEquiv ν T (p.toLinearMap x) := by
  simp only [twistedBlockProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem twistedBlockProjection_compact (k : standardInfiniteCompact F n) :
    (twistedBlockProjection p ν).comp ((S.heckeDeterminantTwist ν).compactRepresentation k) =
      ((T.heckeDeterminantTwist ν).compactRepresentation k).comp (twistedBlockProjection p ν) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (twistEquiv ν S).surjective y
  let a : ℂ := (ν.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ)
  have hs : (S.heckeDeterminantTwist ν).compactRepresentation k (twistEquiv ν S x) =
      a • twistEquiv ν S (S.compactRepresentation k x) := S.heckeDeterminantTwistEquiv_compact ν k x
  have hT : (T.heckeDeterminantTwist ν).compactRepresentation k (twistEquiv ν T (p.toLinearMap x)) =
      a • twistEquiv ν T (T.compactRepresentation k (p.toLinearMap x)) :=
    T.heckeDeterminantTwistEquiv_compact ν k (p.toLinearMap x)
  have hp : p.toLinearMap (S.compactRepresentation k x) =
      T.compactRepresentation k (p.toLinearMap x) :=
    LinearMap.congr_fun (p.isIntertwining' (compactOperator F n k)) x
  change twistedBlockProjection p ν ((S.heckeDeterminantTwist ν).compactRepresentation k
    (twistEquiv ν S x)) = (T.heckeDeterminantTwist ν).compactRepresentation k
      (twistedBlockProjection p ν (twistEquiv ν S x))
  let P := twistedBlockProjection p ν
  calc
    _ = P (a • twistEquiv ν S (S.compactRepresentation k x)) := congrArg (fun y => P y) hs
    _ = a • P (twistEquiv ν S (S.compactRepresentation k x)) := P.map_smul _ _
    _ = a • twistEquiv ν T (p.toLinearMap (S.compactRepresentation k x)) :=
      congrArg (a • ·) (twistedBlockProjection_apply_twist p ν _)
    _ = a • twistEquiv ν T (T.compactRepresentation k (p.toLinearMap x)) :=
      congrArg (fun z => a • twistEquiv ν T z) hp
    _ = _ := hT.symm.trans (congrArg (fun z => (T.heckeDeterminantTwist ν).compactRepresentation k z)
      (twistedBlockProjection_apply_twist p ν x).symm)

theorem twistedBlockProjection_realLie (X : RealLieAlgebra F n) :
    (twistedBlockProjection p ν).comp ((S.heckeDeterminantTwist ν).lieAction X) =
      ((T.heckeDeterminantTwist ν).lieAction X).comp (twistedBlockProjection p ν) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (twistEquiv ν S).surjective y
  let a := OperatorRealization.heckeLieShift ν X
  have hs : (S.heckeDeterminantTwist ν).lieAction X (twistEquiv ν S x) =
      twistEquiv ν S (S.lieAction X x + a • x) :=
    S.lieAction_heckeDeterminantTwistEquiv ν X (OperatorRealization.heckeLieShift_spec ν X) x
  have hT : (T.heckeDeterminantTwist ν).lieAction X (twistEquiv ν T (p.toLinearMap x)) =
      twistEquiv ν T (T.lieAction X (p.toLinearMap x) + a • p.toLinearMap x) :=
    T.lieAction_heckeDeterminantTwistEquiv ν X (OperatorRealization.heckeLieShift_spec ν X) _
  have hp : p.toLinearMap (S.lieAction X x) = T.lieAction X (p.toLinearMap x) :=
    LinearMap.congr_fun (p.isIntertwining' (differentialOperator F n
      (envelopingGenerator F n (complexify F n X)))) x
  change twistedBlockProjection p ν ((S.heckeDeterminantTwist ν).lieAction X (twistEquiv ν S x)) =
    (T.heckeDeterminantTwist ν).lieAction X (twistedBlockProjection p ν (twistEquiv ν S x))
  let P := twistedBlockProjection p ν
  have haux : p.toLinearMap (S.lieAction X x + a • x) =
      T.lieAction X (p.toLinearMap x) + a • p.toLinearMap x :=
    (p.toLinearMap.map_add _ _).trans (congrArg₂ (· + ·) hp (p.toLinearMap.map_smul a x))
  calc
    _ = P (twistEquiv ν S (S.lieAction X x + a • x)) := congrArg (fun y => P y) hs
    _ = twistEquiv ν T (p.toLinearMap (S.lieAction X x + a • x)) :=
      twistedBlockProjection_apply_twist p ν _
    _ = twistEquiv ν T (T.lieAction X (p.toLinearMap x) + a • p.toLinearMap x) :=
      congrArg (fun y => twistEquiv ν T y) haux
    _ = _ := hT.symm.trans (congrArg (fun z => (T.heckeDeterminantTwist ν).lieAction X z)
      (twistedBlockProjection_apply_twist p ν x).symm)

end TwistMap

section Projection

variable {n : ℕ} (B : BlockShape n)
  (R T : ∀ i, OperatorRealization F (B.size i))
  (p : ∀ i, (R i).representation.IntertwiningMap (T i).representation)
  (ν : Fin B.length → HeckeCharacter F)
  {W : Type u} [AddCommGroup W] [Module ℂ W]
  (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), ↥((R i).Space)))

/-- The selected coefficient map first projects to the chosen factors and then
restores the determinant twists on those factors. -/
def projectedRestoredLeviCoefficient :
    W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), ↥(((T i).heckeDeterminantTwist (ν i)).Space)) :=
  (PiTensorProduct.congr fun i => twistEquiv (ν i) (T i)).toLinearMap.comp
    ((PiTensorProduct.map fun i => (p i).toLinearMap).comp ev)

private theorem projectedRestoredLeviCoefficient_eq (w : W) :
    projectedRestoredLeviCoefficient B R T p ν ev w =
      PiTensorProduct.map (fun i => twistedBlockProjection (p i) (ν i))
        (PiTensorProduct.congr (fun i => twistEquiv (ν i) (R i)) (ev w)) := by
  let p₀ := PiTensorProduct.map (fun i => (p i).toLinearMap)
  let p₁ := PiTensorProduct.map (fun i => twistedBlockProjection (p i) (ν i))
  let e₀ := PiTensorProduct.congr (fun i => twistEquiv (ν i) (R i))
  let e₁ := PiTensorProduct.congr (fun i => twistEquiv (ν i) (T i))
  have h : e₁.toLinearMap.comp p₀ = p₁.comp e₀.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change e₁ (p₀ (PiTensorProduct.tprod ℂ x)) = p₁ (e₀ (PiTensorProduct.tprod ℂ x))
    simp only [e₁, p₀, p₁, e₀, PiTensorProduct.map_tprod,
      PiTensorProduct.congr_tprod, twistedBlockProjection_apply_twist]
  exact LinearMap.congr_fun h (ev w)

variable (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)
  (S : OperatorRealization F n) (j : W →ₗ[ℂ] TranslatedBlockConstantTerms F B S)
  (χ : Fin B.length → HeckeCharacter F)

local notation "ν₀" => fun i => (χ i)⁻¹
local notation "T₂" => fun i => OperatorRealization.heckeDeterminantTwist (T i) ((χ i)⁻¹)
local notation "D" => periodRealLieOperator A
local notation "κ" => A.toMonoidHom.comp (compactOperator F n)

/-- Projection to the chosen actual factors preserves the restored compact,
real Lie and radical identities of the Levi coefficient. -/
theorem projectedRestoredLeviCoefficient_operatorEquations
    (hj : ∀ a w, j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (h : ∀ w (m : AdelicBlockParabolic.FullLevi F B),
      functionTensorEvaluation (fun i => operatorRealizationFunctionEvaluation (R i)) (ev w) m =
        (∏ i, ((χ i).adelicDeterminant (B.size i) (m i) : ℂ)) *
          translatedBlockLeviRestriction F B S (j w) m) :
    let e := projectedRestoredLeviCoefficient B R T p ν₀ ev
    IsBlockPeriodCompactEvaluation B κ (fun i => ((T₂) i).compactRepresentation) e ∧
    (∀ X, IsStrictUpperBlockLie F B X → ∀ w, e (D X w) = 0) ∧
    ∀ i X w, e (D (blockShapeRealLieInclusion F B i X) w) =
      tensorCoordinateEnd i (((T₂) i).lieAction X) (e w) := by
  let e := projectedRestoredLeviCoefficient B R T p ν₀ ev
  let R' i := (R i).heckeDeterminantTwist ((χ i)⁻¹)
  let E := (PiTensorProduct.congr fun i => twistEquiv ((χ i)⁻¹) (R i)).toLinearMap.comp ev
  let q i := twistedBlockProjection (p i) ((χ i)⁻¹)
  have hE : IsRealizedLeviPeriodCoefficient B S R' j E :=
    isRealizedLeviPeriodCoefficient_of_twistedEvaluation B S R j ev χ h
  have he (w : W) : e w = PiTensorProduct.map q (E w) :=
    projectedRestoredLeviCoefficient_eq B R T p ν₀ ev w
  have hK := isBlockPeriodCompactEvaluation_of_realizedLeviCoefficient B S R' j E A hj hE
  have hU := blockPeriodStrictUpperEvaluation_of_realizedLeviCoefficient B S R' j E A hj hE
  have hL := blockPeriodRealLieEvaluation_of_realizedLeviCoefficient B S R' j E A hj hE
  let Q₁ := PiTensorProduct.map q
  have transport (i : Fin B.length) (a : Module.End ℂ (R' i).Space)
      (b : Module.End ℂ (((T₂) i).Space)) (hab : (q i).comp a = b.comp (q i))
      (w' w : W) (hw : E w' = tensorCoordinateEnd i a (E w)) :
      e w' = tensorCoordinateEnd i b (e w) := by
    let b₁ := tensorCoordinateEnd (V := fun j => ↥(((T₂) j).Space)) i b
    calc
      _ = Q₁ (E w') := he w'
      _ = Q₁ (tensorCoordinateEnd i a (E w)) := congrArg (fun z => Q₁ z) hw
      _ = b₁ (Q₁ (E w)) := tensorCoordinateEnd_intertwines q i a b hab (E w)
      _ = b₁ (e w) := congrArg (fun z => b₁ z) (he w).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i k w
    let w' := κ (blockShapeInfiniteCompactEmbedding B F i k) w
    change e w' = tensorCoordinateEnd i (((T₂) i).compactRepresentation k) (e w)
    exact transport i ((R' i).compactRepresentation k) (((T₂) i).compactRepresentation k)
      (twistedBlockProjection_compact (p i) ((χ i)⁻¹) k) w' w (hK i k w)
  · intro X hX w
    change e (D X w) = 0
    exact (he (D X w)).trans ((congrArg (fun z => Q₁ z) (hU X hX w)).trans Q₁.map_zero)
  · intro i X w
    let w' := D (blockShapeRealLieInclusion F B i X) w
    change e w' = tensorCoordinateEnd i (((T₂) i).lieAction X) (e w)
    exact transport i ((R' i).lieAction X) (((T₂) i).lieAction X)
      (twistedBlockProjection_realLie (p i) ((χ i)⁻¹) X) w' w (hL i X w)

end Projection

end Langlands.Global

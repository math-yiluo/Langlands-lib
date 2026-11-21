import Langlands.Global.CuspidalLeviProjectedEvaluation

/-! # Finite covariance of restored cuspidal projections -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 140000
set_option maxHeartbeats 1600000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL FiniteParametrizedBlockInduction
open FiniteVectors

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance commonRealizationRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance commonRealizationContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance commonRealizationSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance commonRealizationFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance commonRealizationStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance commonRealizationSpaceGroup {d : ℕ} (S : OperatorRealization F d) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance commonRealizationOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

section Normalization

private theorem map_scalar_tensor_equiv {I : Type*} [Fintype I] {V W : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (e : ∀ i, V i ≃ₗ[ℂ] W i) (a : ∀ i, Module.End ℂ (V i)) (b : ∀ i, Module.End ℂ (W i)) (c : I → ℂ)
    (h : ∀ i x, b i (e i x) = c i • e i (a i x)) (t : ⨂[ℂ] i, V i) :
    PiTensorProduct.congr e ((∏ i, c i) • PiTensorProduct.map a t) =
      PiTensorProduct.map b (PiTensorProduct.congr e t) := by
  let E := (PiTensorProduct.congr e).toLinearMap
  have hE : E.comp ((∏ i, c i) • PiTensorProduct.map a) = (PiTensorProduct.map b).comp E := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change PiTensorProduct.congr e ((∏ i, c i) • PiTensorProduct.map a (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.map b (PiTensorProduct.congr e (PiTensorProduct.tprod ℂ x))
    simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod, h,
      (PiTensorProduct.tprod ℂ).map_smul_univ]
  exact LinearMap.congr_fun hE t

variable {r c : ℕ} {m : Fin c → ℕ} (hm : ∑ i, (m i + 1) = r + 1)

private abbrev commonBlockShape : BlockShape (r + 1) :=
  ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

local notation "B" => commonBlockShape hm
local notation "N" => r + 1

variable (ν : Fin c → HeckeCharacter F)

abbrev restoringWeight (p : AdelicBlockParabolic.Finite F B) : ℂ :=
  ∏ i, ((ν i).finiteAdelicDeterminant (m i + 1) ((B).leviProjection (FiniteAdeles F) p i) : ℂ)

variable (S : ∀ i, OperatorRealization F (m i + 1)) (T : ∀ i, CuspidalOperatorRealization F (m i))
  (a : ∀ i, (S i).representation.IntertwiningMap (T i).realization.representation)

local notation "T₀" => fun i => CuspidalOperatorRealization.heckeDeterminantTwist (T i) (ν i)

theorem finiteCovariance_projectedRestored
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    (g : W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥((S i).Space)))
    (ρ : Representation ℂ (FiniteAdelicGL F N) W)
    (h : ∀ (p : AdelicBlockParabolic.Finite F B) (w : W),
      g (ρ p.val w) = restoringWeight hm ν p • ((B).blockTensor (fun i => (S i).finiteRepresentation))
        ((B).leviProjection (FiniteAdeles F) p) (g w))
    (p : AdelicBlockParabolic.Finite F B) (w : W) :
    let e := projectedRestoredLeviCoefficient B S (fun i => (T i).realization) a ν g
    let e₁ := (normalizedCuspidalCoefficientEquiv hm (T₀)).toLinearEquiv.toLinearMap.comp e
    e₁ (ρ p.val w) = finiteCoefficient F B
      (fun i => ((normalizedCuspidalBlocks hm (T₀)) i).realization.finiteRepresentation) p (e₁ w) := by
  let P := FiniteTensor.externalMap (fun i =>
    (⟨(a i).toLinearMap, fun d => (a i).isIntertwining' (finiteOperator F (m i + 1) d)⟩ :
      (S i).finiteRepresentation.IntertwiningMap (T i).realization.finiteRepresentation))
  let E := PiTensorProduct.congr (fun i => ((T i).realization.heckeDeterminantTwistEquiv (ν i)).toLinearEquiv)
  let Z := normalizedCuspidalCoefficientEquiv hm (T₀)
  let d := (B).leviProjection (FiniteAdeles F) p
  let A := ((B).blockTensor (fun i => (S i).finiteRepresentation)) d
  let A' := ((B).blockTensor (fun i => (T i).realization.finiteRepresentation)) d
  let A₀ := ((B).blockTensor (fun i => ((T₀) i).realization.finiteRepresentation)) d
  have hP : P.toLinearMap (A (g w)) = A' (P.toLinearMap (g w)) :=
    LinearMap.congr_fun (P.isIntertwining' d) (g w)
  have hPE : E (restoringWeight hm ν p • A' (P.toLinearMap (g w))) = A₀ (E (P.toLinearMap (g w))) :=
    map_scalar_tensor_equiv (fun i => ((T i).realization.heckeDeterminantTwistEquiv (ν i)).toLinearEquiv)
      (fun i => (T i).realization.finiteRepresentation (d i))
      (fun i => ((T₀) i).realization.finiteRepresentation (d i))
      (fun i => ((ν i).finiteAdelicDeterminant (m i + 1) (d i) : ℂ))
      (fun i x => (T i).realization.heckeDeterminantTwistEquiv_finite (ν i) (d i) x) _
  change Z (E (P.toLinearMap (g (ρ p.val w)))) = _
  calc
    _ = Z (E (P.toLinearMap (restoringWeight hm ν p • A (g w)))) :=
      congrArg (fun t => Z (E (P.toLinearMap t))) (h p w)
    _ = Z (E (restoringWeight hm ν p • P.toLinearMap (A (g w)))) :=
      congrArg (fun t => Z (E t)) (P.toLinearMap.map_smul _ _)
    _ = Z (E (restoringWeight hm ν p • A' (P.toLinearMap (g w)))) :=
      congrArg (fun t => Z (E (restoringWeight hm ν p • t))) hP
    _ = Z (A₀ (E (P.toLinearMap (g w)))) := congrArg (fun t => Z t) hPE
    _ = _ := LinearMap.congr_fun (Z.toIntertwiningMap.isIntertwining' p) (E (P.toLinearMap (g w)))

end Normalization

end Langlands.Global

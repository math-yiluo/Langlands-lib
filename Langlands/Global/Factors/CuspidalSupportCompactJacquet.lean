import Langlands.Global.Factors.CuspidalSupportArchimedeanTensor
import Langlands.Representation.Archimedean.CompactJacquetStandardTensor

/-! # Place constituents from compact Jacquet probes -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

universe u uW uI uV uM uH

section TensorRange

variable {R : Type*} [RCLike R] {n : ℕ}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {M : Type uM} [AddCommGroup M] [Module ℂ M]
  {H : Type uH} [AddCommGroup H] [Module ℂ H]

local notation "K" => Matrix.unitaryGroup (Fin n) R
local notation "L" => Matrix (Fin n) (Fin n) R

/-- Equivariance of a place quotient map for the compact group and the
Lie operators in real matrix directions. -/
def IsPlaceQuotientIntertwining
    (κ : Representation ℂ K W) (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (κQ : Representation ℂ K H) (πQ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ H)
    (q : W →ₗ[ℂ] H) : Prop :=
  (∀ k w, q (κ k w) = κQ k (q w)) ∧
    ∀ (X : L) w, q (π (1 ⊗ₜ X) w) = πQ (1 ⊗ₜ X) (q w)

private theorem exists_surjective_placeTensor_of_embedding
    (κ : Representation ℂ K W) (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (ρ : Representation ℂ K V) (τ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (κQ : Representation ℂ K H) (πQ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ H)
    (q : W →ₗ[ℂ] H) (hq : Function.Surjective q)
    (hqOps : IsPlaceQuotientIntertwining κ π κQ πQ q)
    (e : W →ₗ[ℂ] V ⊗[ℂ] M) (he : Function.Injective e)
    (heK : ∀ k w, e (κ k w) = TensorProduct.map (ρ k) LinearMap.id (e w))
    (heL : ∀ (X : L) w, e (π (1 ⊗ₜ X) w) =
      TensorProduct.map (τ (1 ⊗ₜ X)) LinearMap.id (e w)) :
    ∃ (S : Submodule ℂ (V ⊗[ℂ] M)) (qS : S →ₗ[ℂ] H),
      IsPlaceTensorIntertwining ρ τ κQ πQ qS ∧ Function.Surjective qS := by
  let b := LinearEquiv.ofInjective e he
  let qS := q.comp b.symm.toLinearMap
  have apply_b (w : W) : qS (b w) = q w := by simp [qS]
  have step (A : Module.End ℂ W) (B : Module.End ℂ (V ⊗[ℂ] M)) (C : Module.End ℂ H)
      (hA : ∀ w, e (A w) = B (e w)) (hC : ∀ w, q (A w) = C (q w)) (z : LinearMap.range e) :
      ∃ hz : B z.val ∈ LinearMap.range e, qS ⟨_, hz⟩ = C (qS z) := by
    obtain ⟨w, rfl⟩ := b.surjective z
    have hz : B (b w).val ∈ LinearMap.range e := ⟨A w, hA w⟩
    have hb : (⟨_, hz⟩ : LinearMap.range e) = b (A w) := Subtype.ext (hA w).symm
    exact ⟨hz, by rw [hb, apply_b, apply_b, hC]⟩
  refine ⟨LinearMap.range e, qS, ⟨?_, ?_⟩, hq.comp b.symm.surjective⟩
  · intro k
    exact step _ _ _ (heK k) (hqOps.1 k)
  · intro X
    exact step _ _ _ (heL X) (hqOps.2 X)

end TensorRange

namespace OperatorSubquotient

variable {F : Type u} [Field F] [NumberField F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {I : Type uI}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (T : OperatorRealization F n) : AddCommGroup T.Space := Submodule.addCommGroup _

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

section Real

open RealLeviSlices RealBlockPosition

variable {c : ℕ} (ds : Fin c → List RealBlock)

local notation "N" => (∑ i, sz ds i)
local notation "RK" => Matrix.unitaryGroup (Fin N) ℝ
local notation "RM" => Matrix (Fin N) (Fin N) ℝ

set_option synthInstance.maxHeartbeats 100000 in
/-- A surjective real place realization with separating compact Jacquet probes
gives a constituent of the standard module of the ordered block concatenation. -/
theorem hasRealPlaceStandardConstituent_of_compactJacquet
    (Q : OperatorSubquotient F N) [Nontrivial Q.Space]
    (hQ : Q.IsIrreducible) (hAdm : Q.IsJointlyAdmissible) (v : RP)
    {κ : Representation ℂ RK W} {π : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hgk : IsRealGKModule N κ π)
    (q : W →ₗ[ℂ] Q.Space) (hq : Function.Surjective q)
    (hqOps : IsPlaceQuotientIntertwining κ π
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) q)
    (probe : I → W →ₗ[ℂ] ℂ)
    (hJ : ∀ a, IsRealJacquetFunctional N κ π (probe a)
      (shiftedExponent N (flat ds)) (positionSign N (flat ds)))
    (hs : ∀ a, HasRealCompactBlockSlices ds κ (probe a))
    (hsep : ∀ w, (∀ a k, probe a (κ k w) = 0) → w = 0) :
    Q.HasRealPlaceStandardConstituent v (flat ds) := by
  obtain ⟨e, he, heK, heL⟩ := exists_realStandardTensor_of_compactJacquet ds hgk probe hJ hs hsep
  obtain ⟨S, qS, hqS, hsS⟩ := exists_surjective_placeTensor_of_embedding κ π
    (realStandardRep N (flat ds)) (realStandardLie N (flat ds))
    (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) q hq hqOps e he heK heL
  exact Q.hasRealPlaceStandardConstituent_of_surjective_tensor hQ hAdm v (flat ds)
    (realRank_flat ds) qS hqS hsS

end Real

section Complex

variable {n : ℕ} (d : Fin n → ComplexCharacterData)

local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- A surjective complex place realization with separating compact Jacquet probes
gives a constituent of the standard module with the specified ordered characters. -/
theorem hasComplexPlaceStandardConstituent_of_compactJacquet
    (Q : OperatorSubquotient F n) [Nontrivial Q.Space]
    (hQ : Q.IsIrreducible) (hAdm : Q.IsJointlyAdmissible) (v : CP)
    {κ : Representation ℂ CK W} {π : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hgk : IsComplexGKModule n κ π)
    (q : W →ₗ[ℂ] Q.Space) (hq : Function.Surjective q)
    (hqOps : IsPlaceQuotientIntertwining κ π
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) q)
    (probe : I → W →ₗ[ℂ] ℂ)
    (hJ : ∀ a, IsComplexJacquetFunctional n π (probe a) (complexShiftedExponent d)
      (fun j => Complex.I * ((d j).weight : ℂ)))
    (hsep : ∀ w, (∀ a k, probe a (κ k w) = 0) → w = 0) :
    Q.HasComplexPlaceStandardConstituent v (List.ofFn d) := by
  obtain ⟨e, he, heK, heL⟩ := exists_complexStandardTensor_of_compactJacquet d hgk probe hJ hsep
  obtain ⟨S, qS, hqS, hsS⟩ := exists_surjective_placeTensor_of_embedding κ π
    (complexStandardRep n (List.ofFn d)) (complexStandardLie n (List.ofFn d))
    (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) q hq hqOps e he heK heL
  exact Q.hasComplexPlaceStandardConstituent_of_surjective_tensor hQ hAdm v (List.ofFn d)
    (List.length_ofFn) qS hqS hsS

end Complex

end OperatorSubquotient

end Langlands.Automorphic

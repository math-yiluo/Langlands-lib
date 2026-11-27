import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Group.LeftQuotientInversion

/-! # The tensor of the fixed normalized compact pictures -/

noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe uG uV uI

open scoped TensorProduct NNReal

namespace Langlands.Plancherel

open Aubert.General Induction

section DualTwist

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (A : SmoothRep.{0, uG, uV} ℂ M)

local notation "B(" z ")" => A.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
local notation "Bᵛ(" z ")" => A.contragredient.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)

/-- Smooth contragredience replaces the unramified parameter by its inverse, with the
same underlying functional. -/
def normalizedDualTwistEquiv (z : unramifiedCharacters ν) :
    (B(z)).contragredient.representation.Equiv (Bᵛ(z⁻¹)).representation :=
  smoothContragredientTwistEquiv z.val.toMonoidHom A.representation
    (unramifiedCharacter_isOpen_ker ν z)

end DualTwist

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (A : SmoothRep.{0, uG, uV} ℂ M)

local notation "B(" z ")" => A.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
local notation "C₁" => CompactInductionPicture h K A
local notation "C₂" => CompactInductionPicture h K A.contragredient
local notation "C" => ProductInducedCompactPicture h K A
local notation "κ(" z ")" => unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr z

/-- The fixed compact chart of the induced dual uses restriction after the inverse-parameter
identification on the inducing smooth dual. -/
def normalizedDualCompactEquiv (z : unramifiedCharacters ν) :
    (normalizedInductionFunctor h hU).obj (B(z)).contragredient ≃ₗ[ℂ] C₂ :=
  (normalizedInductionEquivOfEquiv h hU (normalizedDualTwistEquiv ν A z)).toLinearEquiv.trans
    (κ(z⁻¹) A.contragredient).toLinearEquiv

local notation "κᵛ(" z ")" => normalizedDualCompactEquiv ν h K hU hP hK hPK hν hr A z

@[simp]
theorem normalizedDualCompactEquiv_eval (z : unramifiedCharacters ν)
    (f : (normalizedInductionFunctor h hU).obj (B(z)).contragredient) (k : K) :
    eval _ _ (κᵛ(z) f) k = normalizedDualTwistEquiv ν A z (eval _ _ f (k : G)) :=
  rfl

variable [SecondCountableTopology G]

local notation "κ₂(" z ")" => productInducedCompactEquiv ν h K hP hK hν hr hU hPK z A
local notation "j₂(" z ")" => normalizedProductInductionTensorEquiv h h hU hU (B(z)) (B(z)).contragredient

/-- Apply the tensor-to-product comparison in the actual twisted induction and transport the
three spaces to their fixed compact charts. -/
def normalizedCompactProductChart (z : unramifiedCharacters ν) : C₁ ⊗[ℂ] C₂ ≃ₗ[ℂ] C :=
  let := compactSpace_leftQuotient_of_compact_representatives P hK (fun g => by
    obtain ⟨p, k, h⟩ := hPK g
    exact ⟨p, p.property, k, k.property, h⟩)
  (TensorProduct.congr (κ(z) A).toLinearEquiv.symm (κᵛ(z)).symm).trans
    ((j₂(z)).toLinearEquiv.trans (κ₂(z)).toLinearEquiv)

local notation "chart" => normalizedCompactProductChart ν h K hU hP hK hPK hν hr A

/-- Evaluation of the compact chart is the pointwise tensor of the two compact sections. -/
theorem normalizedCompactProductChart_tmul_eval (z : unramifiedCharacters ν)
    (v : C₁) (w : C₂) (k : K.prod K) :
    eval _ _ (chart z (v ⊗ₜ[ℂ] w)) k =
      eval _ _ v ⟨k.val.1, k.property.1⟩ ⊗ₜ[ℂ] eval _ _ w ⟨k.val.2, k.property.2⟩ := by
  let := compactSpace_leftQuotient_of_compact_representatives P hK (fun g => by
    obtain ⟨p, l, h⟩ := hPK g
    exact ⟨p, p.property, l, l.property, h⟩)
  let f := (κ(z) A).symm v
  let g := (κᵛ(z)).symm w
  let k₁ : K := ⟨k.val.1, k.property.1⟩
  let k₂ : K := ⟨k.val.2, k.property.2⟩
  have hv : eval _ _ v k₁ = eval _ _ f (k₁ : G) := by
    have he := unramifiedNormalizedInductionCompactEquiv_eval h K hU hP hK hPK ν hν hr z A f k₁
    change eval _ _ ((κ(z) A) ((κ(z) A).symm v)) k₁ = _ at he
    rw [Representation.Equiv.apply_symm_apply] at he
    exact he
  have hw : eval _ _ w k₂ = normalizedDualTwistEquiv ν A z (eval _ _ g (k₂ : G)) := by
    have he := normalizedDualCompactEquiv_eval ν h K hU hP hK hPK hν hr A z g k₂
    change eval _ _ (κᵛ(z) ((κᵛ(z)).symm w)) k₂ = _ at he
    rw [LinearEquiv.apply_symm_apply] at he
    exact he
  change eval _ _ (κ₂(z) ((j₂(z)) (f ⊗ₜ[ℂ] g))) k =
    eval _ _ v k₁ ⊗ₜ[ℂ] eval _ _ w k₂
  refine (productInducedCompactEquiv_eval ν h K hP hK hν hr hU hPK z A _ k).trans ?_
  have he := normalizedProductInductionTensorEquiv_tmul_eval h h hU hU (B(z)) (B(z)).contragredient
    f g (k : G × G)
  refine (congrArg (productCompactTwistTensorEquiv ν z A) he).trans ?_
  rw [hv, hw]
  rfl

/-- The tensor-to-product chart is a fixed map of the compact pictures across all unramified
parameters. -/
theorem normalizedCompactProductChart_eq (z w : unramifiedCharacters ν) :
    chart z = chart w := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  ext f g k
  exact (normalizedCompactProductChart_tmul_eval ν h K hU hP hK hPK hν hr A z f g k).trans
    (normalizedCompactProductChart_tmul_eval ν h K hU hP hK hPK hν hr A w f g k).symm

end Langlands.Plancherel

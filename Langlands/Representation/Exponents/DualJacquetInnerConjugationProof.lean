import Langlands.Representation.Exponents.DualJacquetInnerConjugationStatement

/-!
# Inner-conjugation invariance of the actual opposite-dual Jacquet spectrum

An equivalence of representations `e : A ≃ A'` carries opposite-invariant
source functionals of `A` to those of `A'` by precomposition with `e⁻¹`.
Read through the full-dual identification
`splitCentreDualJacquetSourceEquiv`, this is an injective linear map between
the full algebraic duals of the normalized opposite Jacquet modules which
preserves every actual dual eigenspace with the same character. For a
concrete conjugate pair `P`, the operator `A.ρ P.conjugator` is such an
equivalence from `A` to `P.pullbackRep A`, with inverse `A.ρ P.conjugator⁻¹`.
-/

noncomputable section

namespace Langlands

universe uF uV

namespace Exponents.ConjugateBlockPair

variable {n : ℕ} {F : Type uF} [Field F]

/-- The actual inner-action operator `A.ρ g`, for `g = P.conjugator`, is an
equivalence from `A` to its pullback into the standard coordinates of `P`,
with inverse `A.ρ g⁻¹`. -/
def pullbackEquiv (P : ConjugateBlockPair n F) (A : Rep.{uV} ℂ (GeneralLinear n F)) :
    A.ρ.Equiv (P.pullbackRep A).ρ where
  toLinearMap := A.ρ P.conjugator
  invFun := A.ρ P.conjugator⁻¹
  left_inv v := by
    change (A.ρ P.conjugator⁻¹ * A.ρ P.conjugator) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change (A.ρ P.conjugator * A.ρ P.conjugator⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  isIntertwining' h := by
    change A.ρ P.conjugator * A.ρ h =
      A.ρ (P.conjugator * h * P.conjugator⁻¹) * A.ρ P.conjugator
    rw [← map_mul, ← map_mul]
    congr 1
    group

@[simp] theorem pullbackEquiv_apply (P : ConjugateBlockPair n F)
    (A : Rep.{uV} ℂ (GeneralLinear n F)) (v : A) :
    P.pullbackEquiv A v = A.ρ P.conjugator v := rfl

end Exponents.ConjugateBlockPair

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Precomposition with the inverse of an equivalence of representations
preserves invariance under every subgroup. -/
theorem comp_symm_mem_subgroupInvariantDual
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ)
    (N : Subgroup (GeneralLinear n F.Carrier)) {f : Module.Dual ℂ A}
    (hf : f ∈ Jacquet.subgroupInvariantDual A.ρ N) :
    e.symm.toLinearMap.dualMap f ∈ Jacquet.subgroupInvariantDual A'.ρ N := by
  intro x w
  have h : e.symm (A'.ρ x w) = A.ρ x (e.symm w) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap x w
  change f (e.symm (A'.ρ x w)) = f (e.symm w)
  rw [h]
  exact hf x (e.symm w)

/-- The full transpose-dual transport of opposite Jacquet functionals along an
equivalence of representations, through the actual opposite-invariant source
functionals: `f ↦ f ∘ e⁻¹`. -/
def dualJacquetTransport {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    (e : A.ρ.Equiv A'.ρ) :
    Module.Dual ℂ (T.splitCentreOppositeJacquet B A) →ₗ[ℂ]
      Module.Dual ℂ (T.splitCentreOppositeJacquet B A') :=
  (T.splitCentreDualJacquetSourceEquiv B A').symm.toLinearMap ∘ₗ
    (e.symm.toLinearMap.dualMap.restrict
      (fun _ hf => comp_symm_mem_subgroupInvariantDual e _ hf)) ∘ₗ
    (T.splitCentreDualJacquetSourceEquiv B A).toLinearMap

/-- On actual quotient classes the transport is evaluation after `e⁻¹`. -/
@[simp] theorem dualJacquetTransport_apply_mk
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)) (w : A') :
    T.dualJacquetTransport B e φ (T.splitCentreOppositeJacquetMk B A' w) =
      φ (T.splitCentreOppositeJacquetMk B A (e.symm w)) := by
  change (T.splitCentreDualJacquetSourceEquiv B A'
    (T.dualJacquetTransport B e φ)).val w = _
  simp only [dualJacquetTransport, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The transport kills no nonzero functional. -/
theorem dualJacquetTransport_injective
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ) :
    Function.Injective (T.dualJacquetTransport B e) := by
  intro φ ψ h
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := T.splitCentreOppositeJacquetMk_surjective B A q
  have hv := congrArg
    (fun f : Module.Dual ℂ (T.splitCentreOppositeJacquet B A') =>
      f (T.splitCentreOppositeJacquetMk B A' (e v))) h
  simpa only [dualJacquetTransport_apply_mk, Representation.Equiv.symm_apply_apply]
    using hv

/-- The transport preserves the actual dual eigenspace of every character,
with literally the same character. -/
theorem dualJacquetTransport_mem_eigenspace
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    {φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A)}
    (hφ : φ ∈ commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1) :
    T.dualJacquetTransport B e φ ∈
      commutativeCharacterSpace (T.splitCentreDualJacquet B A').ρ χ 1 := by
  rw [T.mem_dualJacquet_eigenspace_iff] at hφ ⊢
  intro a w
  have h : e.symm (A'.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) w) =
      A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) (e.symm w) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap _ w
  rw [dualJacquetTransport_apply_mk, dualJacquetTransport_apply_mk, h]
  exact hφ a (e.symm w)

/-- Equivalent representations have the same actual dual exponents, with the
same character on the same ordered block shape. -/
theorem isDualJacquetExponent_of_equiv
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (h : T.IsDualJacquetExponent B A χ) : T.IsDualJacquetExponent B A' χ := by
  refine ⟨h.1, ?_⟩
  obtain ⟨φ, hφ, hφ0⟩ : ∃ φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A),
      φ ∈ commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1 ∧ φ ≠ 0 := by
    by_contra! h0
    exact h.2 (eq_bot_iff.mpr fun φ hφ => (Submodule.mem_bot ℂ).mpr (h0 φ hφ))
  intro hbot
  have hm := T.dualJacquetTransport_mem_eigenspace B e χ hφ
  rw [hbot] at hm
  have h0 : T.dualJacquetTransport B e φ = 0 := (Submodule.mem_bot ℂ).mp hm
  exact hφ0 (T.dualJacquetTransport_injective B e (h0.trans (map_zero _).symm))

theorem isDualJacquetExponent_iff_of_equiv
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) :
    T.IsDualJacquetExponent B A' χ ↔ T.IsDualJacquetExponent B A χ :=
  ⟨T.isDualJacquetExponent_of_equiv B e.symm χ, T.isDualJacquetExponent_of_equiv B e χ⟩

/-- The norm-one condition concerns only the unchanged character. -/
theorem isUnitaryDualJacquetExponent_iff_of_equiv
    {A A' : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (e : A.ρ.Equiv A'.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) :
    T.IsUnitaryDualJacquetExponent B A' χ ↔ T.IsUnitaryDualJacquetExponent B A χ :=
  and_congr_left' (T.isDualJacquetExponent_iff_of_equiv B e χ)

end PadicField.TopologicalData

/-- Inner pullback preserves every actual dual Jacquet exponent. -/
theorem glDualJacquetInnerConjugationNonunitary :
    GLDualJacquetInnerConjugationNonunitaryStatement.{uF, uV} := by
  intro p _ F T n P A χ
  exact T.isDualJacquetExponent_iff_of_equiv P.shape (P.pullbackEquiv A) χ

/-- Inner pullback preserves every actual unitary dual Jacquet exponent. -/
theorem glDualJacquetInnerConjugation :
    GLDualJacquetInnerConjugationStatement.{uF, uV} := by
  intro p _ F T n P A χ
  exact T.isUnitaryDualJacquetExponent_iff_of_equiv P.shape (P.pullbackEquiv A) χ

end Langlands

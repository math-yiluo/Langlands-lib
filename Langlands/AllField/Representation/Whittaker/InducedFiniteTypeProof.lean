import Langlands.Representation.Whittaker.InducedFiniteTypeProof
import Langlands.AllField.Representation.Classification.FiniteLengthProof
import Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.AllField.Representation.Induction.BlockCharacterAbsorption
import Langlands.AllField.Representation.Induction.SingleBlockSupplement
import Langlands.AllField.Representation.Whittaker.InducedStatement
noncomputable section

namespace Langlands.AllField

universe uR uG uF uV uW

private theorem finiteLength_twist
    {R : Type uR} [CommRing R] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module R V]
    (χ : G →* Rˣ) (ρ : Representation R G V)
    (h : IsFiniteLength (MonoidAlgebra R G) ρ.asModule) :
    IsFiniteLength (MonoidAlgebra R G) (twist χ ρ).asModule := by
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm |>.trans
    ((twistSubrepresentationOrderIso χ ρ).trans
      (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := twist χ ρ)))
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨isNoetherian_mk (e.symm.toOrderEmbedding.dual.wellFounded hN.wf),
    e.symm.toOrderEmbedding.wellFounded hA⟩

private theorem finite_of_finiteLength_equiv
    {R : Type uR} [CommRing R] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module R V]
    {W : Type uW} [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {τ : Representation R G W}
    (e : ρ.Equiv τ) (h : IsFiniteLength (MonoidAlgebra R G) ρ.asModule) :
    Module.Finite (MonoidAlgebra R G) τ.asModule := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ e.toIntertwiningMap
  have hf : Function.Surjective f := e.toLinearEquiv.surjective
  have hτ := h.of_surjective hf
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hτ).1
  infer_instance

/-- Actual upper-parabolic smooth induction preserves finite type for
admissible finite-type complex GL block representations. -/
theorem inducedFiniteType : InducedFiniteTypeStatement.{uF, uV} := by
  intro F _ _ _ _
  intro n B
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  intro V _ _ π hAdm hFin
  let χ := (⟨⟩ : LocalFieldData F).blockInverseHalfCharacter B
  let e := (⟨⟩ : LocalFieldData F).normalizedProductInverseHalfAbsorptionEquiv B π
  have hTwistedAdm : ∀ i, IsAdmissible (twist (χ i).toMonoidHom (π i)) :=
    fun i => (isAdmissible_twist_iff (χ i).toMonoidHom (π i)
      (χ i).isOpen_ker).mpr (hAdm i)
  let A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F) :=
    fun i => SmoothRep.of (twist (χ i).toMonoidHom (π i)) (hTwistedAdm i).1
  have hBlock := glAdmissibleFiniteLength.{uF, uV} F (⟨⟩ : LocalFieldData F)
  have hFactors : ∀ i, (A i).IsAdmissible ∧
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (B.size i) F))
        (A i).representation.asModule := by
    intro i
    refine ⟨hTwistedAdm i, finiteLength_twist (χ i).toMonoidHom (π i) ?_⟩
    exact hBlock (B.size i) (B.positive i) (V i) (π i) (hAdm i) (hFin i)
  have hInduced := Langlands.AllField.Classification.admissibleFiniteLengthProductPreservation.{uF, uV}
    F (⟨⟩ : LocalFieldData F) (n + 1) (Nat.succ_pos n) B A hFactors
  exact finite_of_finiteLength_equiv e hInduced

end Langlands.AllField

import Langlands.Representation.Whittaker.InducedStatement
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.Representation.Twist.SubquotientDefinitions
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.LocalField.CanonicalProof

noncomputable section

namespace Langlands

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
  intro p hp F
  let := F.canonicalTopologicalData.topology
  intro n B
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  intro V _ _ π hAdm hFin
  let χ := F.canonicalTopologicalData.blockInverseHalfCharacter B
  let e := F.canonicalTopologicalData.normalizedProductInverseHalfAbsorptionEquiv B π
  have hTwistedAdm : ∀ i, IsAdmissible (twist (χ i).toMonoidHom (π i)) :=
    fun i => (isAdmissible_twist_iff (χ i).toMonoidHom (π i)
      (χ i).isOpen_ker).mpr (hAdm i)
  let A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun i => SmoothRep.of (twist (χ i).toMonoidHom (π i)) (hTwistedAdm i).1
  have hBlock := glAdmissibleFiniteLength.{uF, uV} p F
  rw [← F.canonicalTopologicalData_topology] at hBlock
  have hFactors : ∀ i, (A i).IsAdmissible ∧
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier))
        (A i).representation.asModule := by
    intro i
    refine ⟨hTwistedAdm i, finiteLength_twist (χ i).toMonoidHom (π i) ?_⟩
    exact hBlock (B.size i) (B.positive i) (V i) (π i) (hAdm i) (hFin i)
  have hInduced := Classification.admissibleFiniteLengthProductPreservation.{uF, uV}
    F F.canonicalTopologicalData (n + 1) (Nat.succ_pos n) B A hFactors
  exact finite_of_finiteLength_equiv e hInduced

end Langlands

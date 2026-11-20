import Langlands.LocalField.PadicBridge
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.SegmentSpecialEssentialSquareIntegrabilityProof
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Induction.CharacterVanishing
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.Tensor.FiniteProperties

/-! # Generic elliptic characters and essential square integrability -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.JacquetLanglands

open Classification GeneralLinear HarmonicAnalysis

private theorem padic_isEssentiallySquareIntegrable_comp_reindex
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {a b : ℕ} (h : a = b) {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear a F.Carrier) W)
    (hρ : T.IsEssentiallySquareIntegrable ρ) :
    T.IsEssentiallySquareIntegrable (ρ.comp (GeneralLinear.reindex (R := F.Carrier)
      (finCongr h)).symm.toMonoidHom) := by
  subst b
  rw [RankinSelberg.SupercuspidalLFactorCharacterization.comp_reindex_finCongr_rfl F]
  exact hρ

/-- A generic p-adic action that fails essential square integrability has
zero character at every regular elliptic element. -/
def PadicGenericEllipticCharacterVanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    let := T.topology
    let := T.valuativeRel
    have := T.localField
    ∀ (r : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
      (hπ : Whittaker.IsGeneric ψ r π),
      ¬ T.IsEssentiallySquareIntegrable π →
      have := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
      have := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
      have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
      ∀ (g : GeneralLinear (r + 1) F.Carrier), IsRegularElliptic g →
        HasCharacterValue π hπ.2.1 g 0

set_option maxHeartbeats 800000 in
/-- An action in the generic segment classification with one inducing block
is essentially square-integrable. Every remaining datum is proper induction. -/
theorem padicGenericEllipticCharacterVanishing :
    PadicGenericEllipticCharacterVanishingStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  dsimp only
  intro r ψ V _ _ π hπ hSQ g hg
  have := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
  let A := SmoothRep.of π hπ.2.1.1
  let U := SmoothRep.universeLift.{uF} A
  let e₀ := SmoothRep.universeLiftEquiv.{uF} A
  have hU : Whittaker.IsGeneric ψ r U.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r e₀).mp hπ
  obtain ⟨d, hHeads, _, ⟨f⟩⟩ := (genericSegmentProductExhaustion T ψ r U).mp hU
  let e : π.Equiv d.induced.representation := e₀.trans (SmoothRep.equivOfIso f)
  have hproper : 1 < d.shape.length := by
    by_contra h
    have hpos : 0 < d.shape.length :=
      UnlinkedSegmentSocleProductIrreducibleProof.length_pos_of_degree F T d (Nat.succ_pos r)
    have hsingle : d.shape.length = 1 := by omega
    let i : Fin d.shape.length := ⟨0, hpos⟩
    let e₁ := T.singleBlockNormalizedProductEquiv d.shape hsingle
      (fun i => (d.blocks i).representation) (fun i => (d.blocks i).isSmooth) i
    have hi := segmentSpecialEssentialSquareIntegrability F T
      (d.segments i) (d.blocks i) (hHeads i).isSegmentQuotient
    exact hSQ ((T.isEssentiallySquareIntegrable_iff_of_equiv (e.trans e₁)).mpr
      (padic_isEssentiallySquareIntegrable_comp_reindex T _ _ hi))
  let τ := d.shape.blockTensor (fun i => (d.blocks i).representation)
  have hτ : IsAdmissible τ := FiniteTensor.isAdmissible_external _ (fun i =>
    (CuspidalSupport.cuspidalEmbedding F T _ (d.blocks i) (hHeads i).choose_spec.2.1).1)
  have hAdm : IsAdmissible d.induced.representation := (isAdmissible_iff_of_equiv e).mp hπ.2.1
  have hvan : HasCharacterValue d.induced.representation hAdm g 0 :=
    properParabolicCharacterVanishing F.Carrier (r + 1) d.shape hproper _ τ hτ hAdm g hg
  exact (hasCharacterValue_iff_of_equivariant _ hπ.2.1 _ hAdm e.toLinearEquiv
    (fun x w => DFunLike.congr_fun (e.isIntertwining' x) w) g 0).mpr hvan

end Langlands.JacquetLanglands

import Langlands.Correspondence.AssemblyRelation
import Langlands.Correspondence.SupercuspidalRelations
import Langlands.Representation.Classification.MultisegmentConstituentCompatibilityStatement
import Langlands.Weil.Local.ContinuityProof
import Langlands.Weil.Representation.TwistClasses
import Langlands.Weil.Representation.InertiaOperations
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Group.GL.CompactOpen
import Langlands.WeilDeligne.BlockTwistProof

/-!
# Twist compatibility of the assembly

The twist part of `AssemblyOperationStatement`. Twisting by the character pulled back along the published Weil-to-field-units map
sends a block sum
`⊕_i σ_i ⊗ Sp(m_i + 1)` to the block sum of the twisted classes `χ σ_i`, with the same
carrier (`isBlockSum_twist`). Under supercuspidal twist compatibility, the multisegment of
the twisted classes is the twisted multisegment (`multisegmentOf_twist`), so the
published character-twist compatibility of Langlands heads gives a head class of the
twisted data (`isMultisegmentHeadClass_twist`). Well-definedness of the assembly then
identifies it with the assembled class (`twistCompatibility_of_assembly`).
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

namespace AssemblyTwist

open scoped TensorProduct

section WeilDeligne

variable {K : Type*} [Field K] {G : Type*} [Group G] {ν : G →* Kˣ}

/-- Twisting a finite direct sum twists each summand; the carrier is unchanged. -/
def twistDirectSumEquiv {ι : Type*} [Fintype ι] (χ : G →* Kˣ)
    (A : ι → WeilDeligneRepresentation K G ν) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.twist χ (WeilDeligneRepresentation.directSum A))
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.twist χ (A i)) where
  representationEquiv :=
    Representation.Equiv.mk (LinearEquiv.refl K (DirectSum ι fun i => A i)) (fun g => by
      apply LinearMap.ext
      intro x
      apply DirectSum.ext
      intro i
      rfl)
  comm_monodromy := rfl

end WeilDeligne

section Main

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyTwistFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyTwistGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- A quasi-character of `Fˣ` has open kernel. -/
theorem isOpen_ker_quasiCharacter (χ : QuasiCharacter F) :
    IsOpen (χ.toMonoidHom.ker : Set F.Carrierˣ) := by
  let _ := F.canonicalGeneralLinearNonarchimedean 1
  have hdet : Continuous (determinantQuasiCharacter F 1 χ) := by
    have := χ.continuous.comp (F.canonicalTopologicalData.generalLinearDeterminant 1).continuous
    exact this
  have h1 := @isOpen_ker_of_continuous_complex_character _ _ _
    (F.canonicalGeneralLinearNonarchimedean 1) _ hdet
  have h2 := h1.preimage (F.canonicalTopologicalData.generalLinearScalar 1).continuous
  convert h2 using 1
  ext a
  change χ a = 1 ↔ χ (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin 1) a)) = 1
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]

/-- The pulled-back character has open kernel on inertia. -/
theorem isOpen_ker_weilCharacter_inertia (e : ReciprocityCandidate F) (χ : QuasiCharacter F) :
    IsOpen (((weilCharacter F e χ).comp (Weil.Local.localInertia F).subtype).ker :
      Set (Weil.Local.localInertia F)) :=
  (Weil.Local.localCharacterInertia F (LocalFactor.RankOne.weilCharacter F e χ)).1

/-- Every parameter class has a twist by a character with open kernel on inertia. -/
theorem exists_isTwistOf (χ : Weil.Local.localWeilGroup F →* ℂˣ)
    (hχ : IsOpen ((χ.comp (Weil.Local.localInertia F).subtype).ker :
      Set (Weil.Local.localInertia F)))
    {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) :
    ∃ E : WeilDeligneClass.{uF, uP} F n,
      WeilDeligneRepresentation.ParameterRelations.IsTwistOf χ D E := by
  obtain ⟨c, hc⟩ := D
  induction c using Quotient.inductionOn with
  | h A =>
    refine ⟨⟨Quotient.mk _ ⟨WeilDeligneRepresentation.twist χ A.1, ?_, ?_⟩, hc⟩, rfl⟩
    · exact FiniteRepresentation.hasOpenInertiaKernel_twist _ χ hχ A.2.1
    · intro g hg
      exact Module.End.IsSemisimple_smul _ (A.2.2 g hg)

/-- Twisting a block sum decomposition of `D` by `χ` gives one of its twist `E`,
with the twisted irreducible Weil classes and the same lengths. -/
theorem isBlockSum_twist (e : ReciprocityCandidate F) (χ : QuasiCharacter F) {r : ℕ}
    {d : Fin r → ℕ} (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat)
    (m : Fin r → ℕ) {n : ℕ+} {D E : WeilDeligneClass.{uF, uP} F n}
    (hD : IsBlockSum F σ m D)
    (hE : WeilDeligneRepresentation.ParameterRelations.IsTwistOf (weilCharacter F e χ) D E) :
    IsBlockSum F (fun i => FiniteRepresentation.continuousIrreducibleTwistEquiv
      (LocalFactor.RankOne.weilCharacter F e χ) _ (σ i)) m E := by
  obtain ⟨B, A, hB, hA, ⟨φ⟩⟩ := hD
  refine ⟨fun i => FiniteRepresentation.twist (weilCharacter F e χ) (B i),
    WeilDeligneRepresentation.twist (weilCharacter F e χ) A, fun i => ?_, ?_, ⟨?_⟩⟩
  · rw [weilClassForget, FiniteRepresentation.forget_continuousIrreducibleTwistEquiv,
      ← FiniteRepresentation.twistClass_classOf, hB i]
    rfl
  · rw [parameterForget, hE]
    show _ = WeilDeligneRepresentation.twistClass _ (parameterForget F D)
    rw [← hA]
    rfl
  · exact (WeilDeligneRepresentation.directSumEquiv fun i =>
      (WeilDeligneRepresentation.Blocks.blockTwistEquiv _ (weilCharacter F e χ) (B i)
        (m i + 1)).symm).trans
      ((twistDirectSumEquiv _ _).symm.trans (WeilDeligneRepresentation.twistEquiv _ φ))

/-- Under supercuspidal twist compatibility, twisting the multisegment of `σ` by `χ`
gives the multisegment of the twisted Weil classes. -/
theorem multisegmentOf_twist (c0 : SupercuspidalMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (htwist : SupercuspidalTwistCompatibility F e c0)
    (χ : QuasiCharacter F) {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ) :
    (multisegmentOf F c0 σ m).map (fun Δ : Segment.{uA, uF} F.canonicalTopologicalData =>
      { base :=
          { rank := Δ.rank
            rank_pos := Δ.rank_pos
            cls := GeneralLinear.SupercuspidalClass.twist
              (χ.toMonoidHom.comp
                (GeneralLinear.determinant : GeneralLinear Δ.rank F.Carrier →* F.Carrierˣ))
              ((isOpen_ker_quasiCharacter F χ).preimage
                (F.canonicalTopologicalData.generalLinearDeterminant Δ.rank).continuous)
              (GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom) Δ.base.cls }
        length := Δ.length
        length_pos := Δ.length_pos }) =
      multisegmentOf F c0 (fun i => FiniteRepresentation.continuousIrreducibleTwistEquiv
        (LocalFactor.RankOne.weilCharacter F e χ) _ (σ i)) m := by
  simp only [multisegmentOf, Multiset.map_coe, List.map_ofFn]
  refine congrArg _ (congrArg List.ofFn (funext fun i => ?_))
  simp only [Function.comp, segmentOf, cuspidalDatumOf]
  congr 2
  exact ((isSupercuspidalCharacterTwist_iff_eq_twist F χ _ _ _).mp (htwist _ (σ i) χ)).symm

/-- Under the multisegment character-twist compatibility, the twist of a Langlands-head
class of `σ` by `χ` is a Langlands-head class of the twisted Weil classes. -/
theorem isMultisegmentHeadClass_twist
    (htw : Classification.MultisegmentConstituentCharacterTwistCompatibility.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (e : ReciprocityCandidate F)
    (htwist : SupercuspidalTwistCompatibility F e c0) (χ : QuasiCharacter F) {r : ℕ}
    {d : Fin r → ℕ} (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat)
    (m : Fin r → ℕ) {n : ℕ+} {π : AutomorphicClass.{uF, uA} F n}
    (hπ : IsMultisegmentHeadClass F c0 σ m π) :
    ∃ π' : AutomorphicClass.{uF, uA} F n, IsCharacterTwist F χ π π' ∧
      IsMultisegmentHeadClass F c0 (fun i => FiniteRepresentation.continuousIrreducibleTwistEquiv
        (LocalFactor.RankOne.weilCharacter F e χ) _ (σ i)) m π' := by
  obtain ⟨A0, J, hA0, hJ, ⟨ψ⟩⟩ := hπ
  have hχ := isOpen_ker_quasiCharacter F χ
  have hχn : IsOpen ((determinantQuasiCharacter F n χ).ker :
      Set (GeneralLinear (n : ℕ) F.Carrier)) :=
    hχ.preimage (F.canonicalTopologicalData.generalLinearDeterminant n).continuous
  refine ⟨automorphicClassOf F (IrreducibleAdmissibleRep.twist _ hχn A0),
    ⟨A0, _, hA0, rfl, ⟨equivOfRepresentationEq rfl⟩⟩,
    IrreducibleAdmissibleRep.twist _ hχn A0, J.twist _ hχn, rfl, ?_,
    ⟨Langlands.twistEquiv _ ψ⟩⟩
  have h := (htw χ.toMonoidHom hχ (n : ℕ) n.pos (multisegmentOf F c0 σ m) J).2.1 hJ
  rw [multisegmentOf_twist F c0 e htwist χ σ m] at h
  exact h

/-- **Twist compatibility of the assembly.** Given well-definedness of the assembly and
the character-twist compatibility of multisegment Langlands heads, the assembly of a
supercuspidal map compatible with twists is compatible with twists. -/
theorem twistCompatibility_of_assembly
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (htw : Classification.MultisegmentConstituentCharacterTwistCompatibility.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hc : IsAssemblyOf F c0 c)
    (htwist : SupercuspidalTwistCompatibility F e c0) : TwistCompatibility F e c := by
  intro n D χ
  obtain ⟨E, hE⟩ := exists_isTwistOf F (weilCharacter F e χ)
    (isOpen_ker_weilCharacter_inertia F e χ) D
  refine ⟨E, hE, ?_⟩
  obtain ⟨r, d, m, σ, hB, hH⟩ := hc n D
  obtain ⟨π', hπ', hH'⟩ := isMultisegmentHeadClass_twist F htw c0 e htwist χ σ m hH
  have hE' : IsAssembledFrom F c0 E π' := ⟨r, d, m, _, isBlockSum_twist F e χ σ m hB hE, hH'⟩
  rwa [(hwell c0 n E).unique (hc n E) hE']

end Main

end AssemblyTwist

end Langlands.Correspondence

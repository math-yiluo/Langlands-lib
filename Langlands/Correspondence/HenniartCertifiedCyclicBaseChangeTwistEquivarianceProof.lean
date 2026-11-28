import Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement
import Langlands.BaseChange.SigmaLiftNormTwist
import Langlands.BaseChange.PadicUnramifiedNormFactors
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.Representation.Classification.SupercuspidalSupportCharacterTwist
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Twist.SubquotientProof

/-!
# Certified cyclic base change commutes with unramified twists

For a cyclic extension `M / L` of p-adic fields of prime degree, a map `Ch` on supercuspidal
classes certified by σ-lifts for some `σ ≠ 1` commutes with unramified twists, given the
uniqueness of σ-lifts (Henniart–Lemaire 2011, II.2.9, Remarques (2) and (4)): the twist of a
class of `GL_{k+1}(L)` by the unramified character with value `z` at a uniformizer goes to the
twists of the classes of `Ch` by the unramified character of `M^×` with value `z ^ f(M|L)`.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uV

open Langlands.Correspondence Langlands.BaseChange GeneralLinear Numerical

variable {p : ℕ} [Fact p.Prime]

/-- Reading a supercuspidal class of rank `k + 1` as a cuspidal datum is injective. -/
private theorem supercuspidalSupportDatum_injective (K : PadicField.{uK} p) :
    Function.Injective (supercuspidalSupportDatum.{uK, uV} K) := by
  rintro ⟨k, a⟩ ⟨k', a'⟩ h
  exact Sigma.ext (Nat.succ.inj (congrArg (fun d => d.rank) h))
    (congr_arg_heq (fun d => d.cls) h)

/-- Given uniqueness of σ-lifts, a cyclic base-change map certified by σ-lifts on
supercuspidal classes for one `σ ≠ 1` commutes with unramified twists. -/
theorem certifiedCyclicBaseChangeTwistEquivariance :
    CertifiedCyclicBaseChangeTwistEquivarianceStatement.{uK, uV} := by
  intro hU p _ S Ch σ hσ1 hcert k z π
  let := S.algebra
  let TL := S.base.canonicalTopologicalData
  let TM := S.top.canonicalTopologicalData
  let := TL.topology
  let := TM.topology
  let := TL.valuativeRel
  let := TM.valuativeRel
  let := TL.localField
  let := TM.localField
  have : IsScalarTower (Padic p) S.base.Carrier S.top.Carrier :=
    Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  have : FiniteDimensional S.base.Carrier S.top.Carrier :=
    Weil.Local.extensionAlgebra_finiteDimensional S.base S.top S.embedding
  have : IsGalois S.base.Carrier S.top.Carrier := S.isGalois
  have : IsModuleTopology S.base.Carrier S.top.Carrier :=
    isModuleTopology_padic_extension S.base S.top
  have : CharZero S.base.Carrier := Algebra.charZero_of_charZero (Padic p) S.base.Carrier
  -- `M / L` is cyclic of group `⟨σ⟩`.
  have : Fact (Nat.card (S.top.Carrier ≃ₐ[S.base.Carrier] S.top.Carrier)).Prime :=
    ⟨S.card_prime⟩
  have hgen : ∀ τ : S.top.Carrier ≃ₐ[S.base.Carrier] S.top.Carrier,
      τ ∈ Subgroup.zpowers σ := by
    intro τ
    rw [zpowers_eq_top_of_prime_card rfl hσ1]
    exact Subgroup.mem_top τ
  have hord : orderOf σ = Module.finrank S.base.Carrier S.top.Carrier :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank _ _)
  have hcyc : IsCyclicAlgebra σ (orderOf σ) := by
    refine ⟨inferInstance, hord.symm, inferInstance, rfl, ?_⟩
    intro x hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := S.base.Carrier)
      (E := S.top.Carrier) x).mpr
    intro τ
    have hσ : σ ∈ MulAction.stabilizer (S.top.Carrier ≃ₐ[S.base.Carrier] S.top.Carrier) x := hx
    exact (Subgroup.zpowers_le.mpr hσ) (hgen τ)
  -- The two certified σ-lifts.
  induction π using Quotient.inductionOn with
  | h A => ?_
  obtain ⟨τ, hτ, I, c, hlift, hsupp⟩ := hcert k _ A rfl
  let A' : GeneralLinear.SupercuspidalRep.{uK, uV} (F := S.base.Carrier) (n := k + 1) :=
    GeneralLinear.SupercuspidalRep.twist (TL.determinantUnramifiedCharacter (k + 1) z)
      (TL.isOpen_ker_determinantUnramifiedCharacter (k + 1) z)
      (TL.ker_determinant_le_ker_determinantUnramifiedCharacter (k + 1) z) A
  obtain ⟨τ', hτ', I', c', hlift', hsupp'⟩ :=
    hcert k (supercuspidalUnramifiedTwist S.base k z (Quotient.mk _ A)) A' rfl
  -- Irreducibility of both lifts, read from their supercuspidal supports.
  have hirr : τ.IsIrreducible := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hsupp
    exact h
  have hirr' : τ'.IsIrreducible := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hsupp'
    exact h
  -- Twisting the σ-lift `τ` of `A` gives a σ-lift of `A'`.
  let ω := TL.unramifiedCharacterContinuous z
  let χE : GeneralLinear (k + 1) S.top.Carrier →* ℂˣ :=
    (ω.toMonoidHom.comp
      (Units.map (Algebra.norm S.base.Carrier : S.top.Carrier →* S.base.Carrier))).comp
      determinant
  obtain ⟨_hπω, hτω, Iω, _hIω, hliftω⟩ :=
    sigmaLiftFieldTwist S.base.Carrier S.top.Carrier σ (orderOf σ) (k + 1) hcyc _ _
      A.obj.representation A.property.2.1 τ.representation hτ I c hlift ω
  -- Uniqueness of σ-lifts identifies `τ'` with the twist of `τ`.
  obtain ⟨e⟩ := hU S.base.Carrier S.top.Carrier σ (orderOf σ) (k + 1) hcyc
    A'.obj.representation A'.property.2.1 A'.property.1
    τ'.representation hτ' hirr'
    (Langlands.twist χE τ.representation) hτω
    ((isIrreducible_twist_iff χE τ.representation).mpr hirr)
    I' Iω c' c hlift' hliftω
  -- The pullback of the unramified character along the norm.
  have hf : IsResidueDegree S.base.Carrier S.top.Carrier S.residueDegree := by
    change TM.residueCardinality = TL.residueCardinality ^ S.residueDegree
    exact Weil.Local.extensionResidueCardinality S.base S.top S.embedding
  have hnorm : ω.toMonoidHom.comp
      (Units.map (Algebra.norm S.base.Carrier : S.top.Carrier →* S.base.Carrier)) =
        TM.unramifiedCharacter (z ^ S.residueDegree) := by
    refine MonoidHom.ext fun x => ?_
    have h := ord_localNorm_eq_residueDegree_mul TL TM hf x
    change TL.ord ((Units.map (Algebra.norm S.base.Carrier :
      S.top.Carrier →* S.base.Carrier) x : S.base.Carrierˣ) : S.base.Carrier) = _ at h
    change z ^ TL.ord ((Units.map (Algebra.norm S.base.Carrier :
      S.top.Carrier →* S.base.Carrier) x : S.base.Carrier)) =
        (z ^ S.residueDegree) ^ TM.ord (x : S.top.Carrier)
    rw [h, zpow_mul, zpow_natCast]
  let χM : Induction.SmoothCharacter ℂ S.top.Carrierˣ :=
    ⟨TM.unramifiedCharacter (z ^ S.residueDegree), TM.isOpen_ker_unramifiedCharacter _⟩
  -- Transport the supercuspidal support of `τ` to `τ'`.
  have hrep : (τ.twist (χM.toMonoidHom.comp determinant)
      (χM.isOpen_ker.preimage (TM.generalLinearDeterminant (k + 1)).continuous)).representation =
        Langlands.twist χE τ.representation := by
    change Langlands.twist (χM.toMonoidHom.comp determinant) τ.representation = _
    simp only [χE, hnorm]
    rfl
  have hs2 := (hsupp.characterTwist χM).of_iso
    (SmoothRep.mkIso ((equivOfRepresentationEq hrep).trans e.symm))
  have hsupp_eq := glSupercuspidalSupportUniqueness.{uV, uK} p S.top TM (k + 1)
    (Nat.succ_pos k) τ' hirr' _ _ hsupp' hs2
  apply Multiset.map_injective (supercuspidalSupportDatum_injective.{uK, uV} S.top)
  rw [hsupp_eq, Multiset.map_map, Multiset.map_map]
  rfl

end Langlands.Henniart

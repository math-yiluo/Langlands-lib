import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Parabolic.RegroupingFactorEquivalences

/-! The whole-block case of the actual weak segment Jacquet factorization. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

/-- For one block, the actual Jacquet quotient map is an equivalence for the
original action restricted to the actual Levi embedding. -/
def singleBlockNormalizedJacquetEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation.Equiv (ρ.comp (B.leviEmbedding F.Carrier))
      (T.normalizedJacquet B ρ) := by
  let f : Representation.IntertwiningMap (ρ.comp (B.leviEmbedding F.Carrier))
      (T.normalizedJacquet B ρ) :=
    { toLinearMap := B.jacquetMk ρ
      isIntertwining' := by
        intro m
        ext v
        change B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) =
          T.normalizedJacquet B ρ m (B.jacquetMk ρ v)
        rw [T.normalizedJacquet_mk_eq_inv_halfModulus,
          T.singleBlock_leviHalfModulus B hB, inv_one, one_smul] }
  exact f.ofBijective
    ⟨B.jacquetMk_injective_of_length_le_one F.Carrier hB.le ρ,
      B.jacquetMk_surjective ρ⟩

/-- The singleton external tensor of the transported ambient object is its
original action restricted to the same actual Levi. -/
def singleBlockTransportedTensorEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier),
      (B.blockTensor (fun j =>
        ((B.singleBlock_size hB j).symm ▸ A :
          SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size j) F.Carrier)).representation)).Equiv
        (A.representation.comp (B.leviEmbedding F.Carrier)) := by
  letI := T.topology
  intro A
  let i := B.singleBlockIndex hB
  let h := B.singleBlock_size hB i
  let e := GeneralLinear.reindex (R := F.Carrier) (finCongr h)
  let δ := B.singleBlockTensorEquiv hB (fun j =>
    ((B.singleBlock_size hB j).symm ▸ A :
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size j) F.Carrier)).representation) i
  let ε := (FiniteTensor.rankCastRepresentationEquiv F T h A).symm.precomp
    (Pi.evalMonoidHom (fun j => GeneralLinear (B.size j) F.Carrier) i)
  let E := δ.trans ε
  refine Representation.Equiv.mk E.toLinearEquiv ?_
  intro m
  have hm : e (m i) = B.leviEmbedding F.Carrier m := by
    have hc := B.singleBlockLeviEquiv_symm_coordinate hB
      (B.leviEmbedding F.Carrier m) i
    change (B.singleBlockLeviEquiv hB F.Carrier).symm
      ((B.singleBlockLeviEquiv hB F.Carrier) m) i = _ at hc
    rw [MulEquiv.symm_apply_apply] at hc
    rw [hc]
    exact e.apply_symm_apply _
  have hE := E.isIntertwining' m
  change E.toLinearMap ∘ₗ _ =
    A.representation (e (m i)) ∘ₗ E.toLinearMap at hE
  rw [hm] at hE
  exact hE

/-- The one-block normalized Jacquet module is the tensor of the canonically
rank-transported original smooth object. -/
def singleBlockNormalizedJacquetTensorEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier),
      (T.normalizedJacquet B A.representation).Equiv
        (B.blockTensor (fun j =>
          ((B.singleBlock_size hB j).symm ▸ A :
            SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size j) F.Carrier)).representation)) := by
  letI := T.topology
  intro A
  exact (T.singleBlockNormalizedJacquetEquiv B hB A.representation).symm.trans
    (T.singleBlockTransportedTensorEquiv B hB A).symm

end Langlands.PadicField.TopologicalData

namespace Langlands.Classification

open GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The nonzero factor branch of the all-shape assertion holds for every
one-block shape, retaining precisely the supplied weak quotient. -/
theorem segmentQuotientJacquetFactors_singleBlock :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV, uF})
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentQuotient Δ π →
      ∀ (B : BlockShape Δ.degree), B.length = 1 →
        ∃ (k : Fin B.length → ℕ)
          (Γ : Fin B.length → T.Segment.{max uF uV, uF})
          (hdeg : ∀ i, (Γ i).degree = B.size i)
          (σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
            (GeneralLinear (B.size i) F.Carrier)),
          (∀ i, 0 < k i) ∧
          (∀ i, B.size i = Δ.rank * k i) ∧
          (∑ i, k i) = Δ.length ∧
          (∀ i, (Γ i).length = k i) ∧
          (∀ i, (Γ i).base =
            Δ.member (Δ.length - (∑ j : Fin B.length with j < i, k j) - k i)) ∧
          (∀ i, T.IsSegmentQuotient (Γ i) ((hdeg i).symm ▸ σ i)) ∧
          Nonempty ((T.normalizedJacquet B π.representation).Equiv
            (B.blockTensor (fun i => (σ i).representation))) := by
  let := T.topology
  intro Δ π hπ B hB
  classical
  let hdeg : ∀ i : Fin B.length, Δ.degree = B.size i :=
    fun i => (B.singleBlock_size hB i).symm
  let σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun i => (B.singleBlock_size hB i).symm ▸ π
  refine ⟨fun _ => Δ.length, fun _ => Δ, hdeg, σ, fun _ => Δ.length_pos, ?_,
    ?_, fun _ => rfl, ?_, ?_, ?_⟩
  · intro i
    rw [B.singleBlock_size hB i]
    exact Nat.mul_comm _ _
  · simp [hB]
  · intro i
    have hi : ∀ j : Fin B.length, ¬j < i := by
      intro j
      have he : j = i := (B.eq_singleBlockIndex hB j).trans
        (B.eq_singleBlockIndex hB i).symm
      simp only [he, lt_self_iff_false, not_false_eq_true]
    simp [hi]
  · intro i
    have hc : ∀ {r s : ℕ} (h : r = s)
        (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear s F.Carrier)),
        h ▸ (h.symm ▸ A :
          SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)) = A := by
      intro r s h A
      cases h
      rfl
    change T.IsSegmentQuotient Δ ((B.singleBlock_size hB i) ▸
      ((B.singleBlock_size hB i).symm ▸ π :
        SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)))
    rw [hc]
    exact hπ
  · exact ⟨T.singleBlockNormalizedJacquetTensorEquiv B hB π⟩

end Langlands.Classification

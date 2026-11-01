import Langlands.Representation.Aubert.ActualFixedFactorVector
import Langlands.Representation.Classification.SegmentJacquetSubobject
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.VirtualRepresentation.PositiveSupport

/-! Actual Jacquet detection and effectivity reflection on segment support. -/

noncomputable section

namespace Langlands.SmoothRep.IrreducibleOperator

open IrreducibleGrothendieckProof VirtualRepresentation
open CentralEigenspaceSplitting

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A nonzero actual finite-length object has a nonzero factor vector. -/
theorem compositionFactors_ne_zero_of_nontrivial
    (A : FiniteLengthObject.{uK, uG, uV} k G) (hA : Nontrivial A.val) :
    compositionFactors A ≠ 0 := by
  classical
  obtain ⟨n, s, hs⟩ := MultiplicityAdditivityProof.exists_series A.property
  have hn : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    have hzero : repLength A.val.representation = 0 := by
      rw [repLength_eq_of_hasSimpleFactors s hs, hn, Nat.cast_zero]
    have hss := repLength_eq_zero_iff.mp hzero
    exact @not_subsingleton A.val hA hss
  let i : Fin n := ⟨0, hn⟩
  let τ := gradedSmooth s i
  have hτ : τ.IsIrreducible := hs i
  have hpos : 0 < s.factorMultiplicity τ.obj := by
    unfold ObjectRepFiltration.factorMultiplicity
    exact Nat.card_pos_iff.mpr
      ⟨⟨⟨i, ⟨Representation.Equiv.refl _⟩⟩⟩, inferInstance⟩
  intro hzero
  have h := congrArg (fun v => v (irreducibleIsoClass τ hτ)) hzero
  rw [compositionFactors_eq_series A s hs, seriesClass_apply s hs τ hτ] at h
  simp only [Finsupp.zero_apply] at h
  exact (ne_of_gt hpos) (Int.natCast_eq_zero.mp h)

/-- Distinct scalar actions on simple graded factors give coefficient bound one. -/
theorem compositionFactors_le_one_of_scalarSeparatedSeries
    (A : FiniteLengthObject.{uK, uG, uV} k G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors)
    (z : G) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v) :
    ∀ d, compositionFactors A d ≤ 1 := by
  have hfree : ∀ i j : Fin n,
      Nonempty ((s.gradedRepresentation i).ρ.Equiv (s.gradedRepresentation j).ρ) →
        i = j := by
    intro i j ⟨E⟩
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (hs i)
    have he := apply_eq_smul_of_equiv E z (c j) (hgr j) v
    have hzero : (c i - c j) • v = 0 := by
      rw [sub_smul, ← hgr i v, ← he, sub_self]
    exact hc (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv))
  intro d
  obtain ⟨τ, hτ, rfl⟩ := IrreducibleIsoClass.exists_eq d
  rw [compositionFactors_eq_series A s hs, seriesClass_apply]
  exact_mod_cast MultiplicityFreeSubmoduleLatticeProof.factorMultiplicity_le_one s hfree τ.obj

end Langlands.SmoothRep.IrreducibleOperator

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport Classification SegmentFullJacquet
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator
open VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The existing actual Jacquet map transported to source and target factor vectors. -/
def jacquetOnIrreducibles {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    SmoothRep.IrreducibleLattice.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) →ₗ[ℤ]
      SmoothRep.IrreducibleLattice.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  factorMap.comp ((normalizedJacquetK0.{uF, uV} F T B).comp
    (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)))

theorem jacquetOnIrreducibles_factorMap {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      jacquetOnIrreducibles.{uF, uV} F T B (factorMap x) =
        factorMap (normalizedJacquetK0.{uF, uV} F T B x) := by
  let := T.topology
  intro x
  change factorMap (normalizedJacquetK0 F T B
    (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (factorMap x))) = _
  rw [show SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)
    (factorMap x) = x from LinearMap.congr_fun realize_comp_factorMap x]

theorem jacquetOnIrreducibles_generator {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.IsIrreducible),
      jacquetOnIrreducibles.{uF, uV} F T B (generator (SmoothRep.irreducibleIsoClass A hA)) =
        compositionFactors ⟨(T.normalizedJacquetFunctor B).obj A,
          normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA)⟩ := by
  let := T.topology
  intro A hA
  change factorMap (normalizedJacquetK0 F T B
    (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)
      (generator (SmoothRep.irreducibleIsoClass A hA)))) = _
  rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass A hA
    (SmoothRep.hasFiniteLength_of_isIrreducible hA)]
  change factorMap (normalizedJacquetK0 F T B
    (GeneralLinear.finiteLengthClass n F.Carrier A
      (SmoothRep.hasFiniteLength_of_isIrreducible hA))) = _
  rw [normalizedJacquetK0_finiteLengthClass F T B A
    (SmoothRep.hasFiniteLength_of_isIrreducible hA) _,
    BlockShape.finiteLengthClass, factorMap_ofRepresentation]

theorem jacquetOnIrreducibles_effective {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ c, jacquetOnIrreducibles.{uF, uV} F T B (generator c) ∈ effective := by
  let := T.topology
  intro c
  obtain ⟨A, hA, rfl⟩ := SmoothRep.IrreducibleIsoClass.exists_eq c
  rw [jacquetOnIrreducibles_generator F T B A hA]
  exact compositionFactors_effective _

/-- A uniform block shape is the only ordered shape in its association class. -/
theorem eq_uniform_of_levisAssociated {m r : ℕ} (hr : 0 < r)
    {C : BlockShape (m * r)}
    (h : LevisAssociated (F := F.Carrier) (BlockShape.uniform m r hr) C) :
    C = BlockShape.uniform m r hr := by
  obtain ⟨⟨w, hw⟩⟩ := h
  have hl := TotalConjugatingCount.length_eq hw
  refine TotalConjugatingCount.shape_ext hl.symm (fun j => ?_)
  obtain ⟨i, rfl⟩ := TotalConjugatingCount.blockMap_surjective hw j
  rw [TotalConjugatingCount.size_blockMap hw]
  rfl

/-- Every nonzero subquotient of uniform quasicuspidal induction has nonzero
Jacquet module for that same uniform shape. -/
theorem uniformInductionJacquet_nontrivial {m r : ℕ} (hr : 0 < r) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, max uF uV} ℂ ((BlockShape.uniform m r hr).Levi F.Carrier)),
      IsLeviQuasicuspidal (BlockShape.uniform m r hr) σ.representation →
      ∀ (Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier)),
        SmoothRep.IsSubquotient Q
          ((T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj σ) →
        Nontrivial Q →
        Nontrivial ((T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj Q) := by
  let := T.topology
  intro σ hσ Q hsub hQ
  obtain ⟨C, hJ, hqc⟩ := minimalNonzeroJacquet.{uF, max uF uV} p F T (m * r) Q hQ
  by_cases hC : LevisAssociated (F := F.Carrier) (BlockShape.uniform m r hr) C
  · obtain rfl := eq_uniform_of_levisAssociated F hr hC
    exact hJ
  · have hsubJ := normalizedJacquetSubquotient.{uF, max uF uV} p F T (m * r) C _ _ hsub
    have hzero := nonassociatedJacquetSubquotients.{uF, max uF uV} F T (m * r)
      (BlockShape.uniform m r hr) C σ hσ hC _ hsubJ hqc
    exact False.elim (@not_subsingleton _ hJ hzero)

/-- Associated Jacquet filtration and hereditary quasicuspidality apply to
every actual subquotient of quasicuspidal induction. -/
theorem inductionJacquet_subquotient_isLeviQuasicuspidal {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
      ∀ (Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        SmoothRep.IsSubquotient Q ((T.normalizedParabolicInductionFunctor B).obj σ) →
        IsLeviQuasicuspidal B ((T.normalizedJacquetFunctor B).obj Q).representation := by
  let := T.topology
  intro σ hσ Q hsub
  have htotal := (associatedJacquetFiltration.{uF, max uF uV} F T n B B σ hσ
    (LevisAssociated.refl B)).1
  apply leviQuasicuspidalSubquotient.{uF, max uF uV} F T B _ _ htotal
  exact normalizedJacquetSubquotient.{uF, max uF uV} p F T n B _ _ hsub

/-- The full segment Jacquet map reflects effectivity on the entire
constituent support of the increasing segment induction. -/
def SegmentJacquetDetectionStatement : Prop :=
  letI := T.topology
  ∀ (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := r)),
    let I := T.segmentInduced A.obj m hr
    let hI := normalizedInductionK0_hasFiniteLength.{uF, uV} F T
      (BlockShape.uniform m r hr)
      (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr))
      (SmoothRep.hasFiniteLength_of_isIrreducible
        (segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A).1)
    let v := compositionFactors ⟨I, hI⟩
    ∀ w : SmoothRep.IrreducibleLattice.{0, uF, max uF uV} ℂ
        (GeneralLinear (m * r) F.Carrier), w.support ⊆ v.support →
      jacquetOnIrreducibles.{uF, uV} F T (BlockShape.uniform m r hr) w ∈ effective →
      w ∈ effective

set_option maxHeartbeats 3200000 in
theorem segmentJacquetDetection :
    SegmentJacquetDetectionStatement.{uF, uV} F T := by
  let := T.topology
  intro m r hm hr A
  dsimp only
  let B := BlockShape.uniform m r hr
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
  let I := T.segmentInduced A.obj m hr
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A
  let hI := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B σ
    (SmoothRep.hasFiniteLength_of_isIrreducible hσ.1)
  let v := compositionFactors ⟨I, hI⟩
  let J := jacquetOnIrreducibles.{uF, uV} F T B
  have hpositive : ∀ c ∈ v.support, J (generator c) ∈ effective :=
    fun c _ => jacquetOnIrreducibles_effective F T B c
  have hnonzero : ∀ c ∈ v.support, J (generator c) ≠ 0 := by
    intro c hc
    obtain ⟨Q, hQ, rfl⟩ := SmoothRep.IrreducibleIsoClass.exists_eq c
    have hsub := (mem_support_compositionFactors_iff_isSubquotient ⟨I, hI⟩ Q hQ).mp hc
    have hnQ : Nontrivial Q := by
      obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hQ
      exact ⟨⟨v, 0, hv⟩⟩
    have hnJ := uniformInductionJacquet_nontrivial.{uF, uV} F T hr σ hσ.2.2 Q hsub hnQ
    change jacquetOnIrreducibles F T B (generator (SmoothRep.irreducibleIsoClass Q hQ)) ≠ 0
    rw [jacquetOnIrreducibles_generator F T B Q hQ]
    exact compositionFactors_ne_zero_of_nontrivial _ hnJ
  have hfree : ∀ d, J v d ≤ 1 := by
    have hJclass : J v = compositionFactors ⟨(T.normalizedJacquetFunctor B).obj I,
        normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B I hI⟩ := by
      change jacquetOnIrreducibles F T B (compositionFactors ⟨I, hI⟩) = _
      rw [← factorMap_ofRepresentation I hI, jacquetOnIrreducibles_factorMap]
      change factorMap (normalizedJacquetK0 F T B
        (GeneralLinear.finiteLengthClass (m * r) F.Carrier I hI)) = _
      rw [normalizedJacquetK0_finiteLengthClass F T B I hI _,
        BlockShape.finiteLengthClass, factorMap_ofRepresentation]
    rw [hJclass]
    let := T.generalLinearTopologicalGroup r
    obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
      admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
    let ω := χ.comp scalarToCenter
    have hω : HasScalarCharacter A.obj.representation GeneralLinear.scalar ω :=
      fun z v => hχ (scalarToCenter z) v
    obtain ⟨N, e, s, hs, hgr, _⟩ := exists_segmentJacquetFiltration F T
      (associatedJacquetFiltration F T (m * r)) hm hr A ω hω
    let c : Fin N → ℂ := fun i => segmentScalar T ω r m (blockPerm F (e i))
    have hc : Function.Injective c := fun i j h =>
      e.injective (blockPerm_injective F (segmentScalar_injective T ω hr m h))
    exact compositionFactors_le_one_of_scalarSeparatedSeries _ s hs
      (separatingScalar F T m r hr) c hc hgr
  intro w hw hJw
  exact effective_of_effective_image_on_support J v
    (compositionFactors_effective ⟨I, hI⟩) hpositive hnonzero hfree w hw hJw

end Langlands.Aubert

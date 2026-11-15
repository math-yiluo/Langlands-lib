import Langlands.Representation.Classification.MoeglinWaldspurgerCastCalculus
import Langlands.Representation.Classification.UnlinkedSocleProductIrreducibilityProof
import Langlands.Representation.CuspidalSupport.LiteralTwoBlockSwap
import Langlands.Representation.Classification.SegmentProductOrderedAssembly

/-!
# Swapping unlinked segment socles in a binary product

A segment socle is the Zelevinsky socle of the one-segment multisegment; the binary product
of the socles of two unlinked segments is irreducible, hence isomorphic, up to rank
transport, to the product in the other order.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment socle is the Zelevinsky socle of the one-segment multisegment. -/
theorem isZelevinskySocle_singleton {Δ : T.Segment.{max uF uV, uF}}
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hZ : T.IsSegmentSocle Δ Z) :
    Multisegment.IsZelevinskySocle ({Δ} : T.Multisegment.{max uF uV, uF}) Z := by
  let := T.topology
  let d : T.SegmentProductDatum.{max uF uV, uF} Δ.degree := ⟨1, fun _ => Δ, by simp, fun _ => Z⟩
  have hZi : Z.IsIrreducible := Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T hZ
  have e := SmoothRep.equivOfIso (SegmentProductOrderedAssembly.singletonIso d rfl ⟨0, Nat.zero_lt_one⟩)
  refine ⟨d, ?_, ?_, fun _ => hZ, ?_⟩
  · show ((List.ofFn fun _ : Fin 1 => Δ : List _) : Multiset _) = {Δ}
    simp
  · intro i j hij
    exfalso
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    have : i.val < j.val := hij
    omega
  · have hd : (d.induced).IsIrreducible :=
      (Weil.IsomorphismInvariance.irreducible_iff e).mpr hZi
    exact IsIrreducibleSubrepresentation.isIrreducibleSocle_of_irreducible
      ⟨hZi, e.symm.toIntertwiningMap, e.symm.injective⟩ hd

/-- The two-block product of the socles of two unlinked segments is irreducible. -/
theorem twoBlocks_isIrreducible_of_unlinked {Δ Γ : T.Segment.{max uF uV, uF}}
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    (hZ : T.IsSegmentSocle Δ Z) (hA : T.IsSegmentSocle Γ A) (hun : ¬ Δ.IsLinked Γ) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor
      (Shahidi.twoBlocks Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos)).obj
        (twoBlockFactors Δ.degree_pos Γ.degree_pos Z A)).IsIrreducible := by
  let := T.topology
  have h := unlinkedSocleProductIrreducibility.{uF, uV} F T (Δ.degree + Γ.degree)
    (Shahidi.twoBlocks Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos)
    ![({Δ} : T.Multisegment.{max uF uV, uF}), {Γ}]
    (twoBlockFactors Δ.degree_pos Γ.degree_pos Z A) ?_ ?_
  · obtain ⟨d, -, -, -, hirr, -⟩ := h
    exact hirr
  · intro i
    fin_cases i
    · exact isZelevinskySocle_singleton hZ
    · exact isZelevinskySocle_singleton hA
  · intro i j hij Δ₁ h₁ Δ₂ h₂
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Multiset.mem_singleton,
        Fin.mk_one, Matrix.cons_val_one] at h₁ h₂
      subst h₁ h₂
      exact hun
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Multiset.mem_singleton,
        Fin.mk_one, Matrix.cons_val_one] at h₁ h₂
      subst h₁ h₂
      exact fun h => hun h.symm
    · exact absurd rfl hij

/-- Swap at the level of standard two-block products. -/
theorem castIso_twoBlocks_swap_of_unlinked {Δ Γ : T.Segment.{max uF uV, uF}}
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    (hZ : T.IsSegmentSocle Δ Z) (hA : T.IsSegmentSocle Γ A) (hun : ¬ Δ.IsLinked Γ) :
    letI := T.topology
    CastIso T
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos)).obj
          (twoBlockFactors Δ.degree_pos Γ.degree_pos Z A))
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks Γ.degree Δ.degree Γ.degree_pos Δ.degree_pos)).obj
          (twoBlockFactors Γ.degree_pos Δ.degree_pos A Z)) := by
  let := T.topology
  have hZi : Z.IsIrreducible := Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T hZ
  have hAi : A.IsIrreducible := Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T hA
  have hP := twoBlocks_isIrreducible_of_unlinked hZ hA hun
  have esw := CuspidalSupport.irreducibleLiteralTwoBlockSwapEquiv F T Δ.degree_pos Γ.degree_pos
    Z A hZi hAi hP
  have hR : ((((T.normalizedProductInductionFunctor
      (Shahidi.twoBlocks Γ.degree Δ.degree Γ.degree_pos Δ.degree_pos)).obj
        (twoBlockFactors Γ.degree_pos Δ.degree_pos A Z)).representation.comp
          (reindex (R := F.Carrier) (finCongr (Nat.add_comm Δ.degree Γ.degree))).toMonoidHom).comp
          (reindex (R := F.Carrier) (finCongr (Nat.add_comm Δ.degree Γ.degree))).symm.toMonoidHom) =
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks Γ.degree Δ.degree Γ.degree_pos Δ.degree_pos)).obj
          (twoBlockFactors Γ.degree_pos Δ.degree_pos A Z)).representation := by
    ext g : 1
    simp
  have e2 := Parabolic.equivTrans
      (Parabolic.equivPrecomp esw
        (reindex (R := F.Carrier) (finCongr (Nat.add_comm Δ.degree Γ.degree))).symm.toMonoidHom)
      (equivOfRepresentationEq hR)
  have e1 := T.castRankEquiv (Nat.add_comm Δ.degree Γ.degree)
    ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos)).obj
          (twoBlockFactors Δ.degree_pos Γ.degree_pos Z A))
  have e := Parabolic.equivTrans (Parabolic.equivSymm e1) e2
  exact ⟨Nat.add_comm Δ.degree Γ.degree, ⟨SmoothRep.mkIso e⟩⟩

/-- **Swap.** The binary products of the socles of two unlinked segments in the two orders
are isomorphic up to rank transport. -/
theorem castIso_swap_of_unlinked {Δ Γ : T.Segment.{max uF uV, uF}}
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    (hZ : T.IsSegmentSocle Δ Z) (hA : T.IsSegmentSocle Γ A) (hun : ¬ Δ.IsLinked Γ) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (Z, A))
      ((T.binaryNormalizedProductFunctor Γ.degree Δ.degree).obj (A, Z)) := by
  let := T.topology
  have h1 : CastIso T ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (Z, A))
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos)).obj
          (twoBlockFactors Δ.degree_pos Γ.degree_pos Z A)) :=
    castIso_of_iso (eqToIso (BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
      F T Δ.degree_pos Γ.degree_pos Z A))
  have h2 := castIso_twoBlocks_swap_of_unlinked hZ hA hun
  have h3 : CastIso T
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks Γ.degree Δ.degree Γ.degree_pos Δ.degree_pos)).obj
          (twoBlockFactors Γ.degree_pos Δ.degree_pos A Z))
      ((T.binaryNormalizedProductFunctor Γ.degree Δ.degree).obj (A, Z)) :=
    castIso_of_iso (eqToIso (BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
      F T Γ.degree_pos Δ.degree_pos A Z).symm)
  exact h1.trans (h2.trans h3)

end Langlands.MoeglinWaldspurger.Derivation

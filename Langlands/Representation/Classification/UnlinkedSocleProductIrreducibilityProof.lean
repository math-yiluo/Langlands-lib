import Langlands.Representation.Classification.TadicBlockReductionStatement
import Langlands.Representation.Classification.UnlinkedSocleProductEmbedding
import Langlands.Representation.Classification.MultisegmentConstituentContragredientProof
import Langlands.Representation.Classification.TadicSocleIndependence
import Langlands.Representation.Classification.OrderedMultisegmentSocleExistenceProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Classification.SegmentSocleInversionReduction
import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.RegularLanglandsHeadReduction
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Category.FiniteLengthHelpers
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity
import Langlands.Representation.Aubert.IrreducibleImageAssembly
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-! # Zelevinsky 1980, Proposition 8.5 -/

noncomputable section

namespace Langlands.Classification.UnlinkedSocleProduct

open CategoryTheory

universe uG uV

section Multiplicity

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An irreducible smooth representation equivalent to `τ` occurs once, with
respect to `τ`, in its own composition series. -/
theorem hasJordanHolderMultiplicity_one {P τ : SmoothRep.{0, uG, uV} ℂ G}
    (hP : P.IsIrreducible) (e : P.representation.Equiv τ.representation) :
    HasJordanHolderMultiplicity P.obj τ.obj 1 := by
  have h := SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity_witness
    ⟨P, SmoothRep.hasFiniteLength_of_isIrreducible hP⟩ P
  rw [SmoothRep.IrreducibleOperator.compositionMultiplicity_self P hP] at h
  exact (equivJordanHolderMultiplicityTransport ℂ G P.obj P.obj P.obj τ.obj
    (Representation.Equiv.refl _) e 1).mp h

/-- A nonzero finite-length smooth representation in which `τ` occurs at most
once, and whose irreducible subrepresentations and irreducible quotients are all
equivalent to `τ`, is irreducible. -/
theorem isIrreducible_of_multiplicity_le_one
    (A τ : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) [Nontrivial A]
    (m : ℕ) (hm : HasJordanHolderMultiplicity A.obj τ.obj m) (hm1 : m ≤ 1)
    (hsub : ∀ (P : SmoothRep.{0, uG, uV} ℂ G) (j : P ⟶ A), P.IsIrreducible →
      Function.Injective (SmoothRep.hom j) →
        Nonempty (P.representation.Equiv τ.representation))
    (hquot : ∀ (Q : SmoothRep.{0, uG, uV} ℂ G) (q : A ⟶ Q), Q.IsIrreducible →
      Function.Surjective (SmoothRep.hom q) →
        Nonempty (Q.representation.Equiv τ.representation)) :
    A.IsIrreducible := by
  obtain ⟨P, hP, j, hj⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hA
  by_cases hsurj : Function.Surjective (SmoothRep.hom j)
  · exact (Weil.IsomorphismInvariance.irreducible_iff
      ((SmoothRep.hom j).ofBijective ⟨hj, hsurj⟩)).mp hP
  exfalso
  let S : Subrepresentation A.representation := (SmoothRep.hom j).range
  let C := SmoothRep.quotient A S
  have hC : C.HasFiniteLength := hA.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.hom (SmoothRep.mkQ A S))) (SmoothRep.mkQ_surjective A S)
  have hCnt : Nontrivial C := by
    obtain ⟨v, hv⟩ : ∃ v : A, v ∉ S.toSubmodule := by
      by_contra h
      push Not at h
      exact hsurj fun v => h v
    refine ⟨⟨SmoothRep.hom (SmoothRep.mkQ A S) v, 0, ?_⟩⟩
    intro h0
    exact hv ((Submodule.Quotient.mk_eq_zero _).mp h0)
  obtain ⟨Q, hQ, r, hr⟩ := SegmentHeadSupport.exists_irreducible_quotient hC
  obtain ⟨eP⟩ := hsub P j hP hj
  obtain ⟨eQ⟩ := hquot Q (SmoothRep.mkQ A S ≫ r) hQ
    (hr.comp (SmoothRep.mkQ_surjective A S))
  have hex : LinearMap.range (SmoothRep.hom j).toLinearMap =
      LinearMap.ker (SmoothRep.hom (SmoothRep.mkQ A S)).toLinearMap :=
    (Submodule.ker_mkQ _).symm
  obtain ⟨mP, mC, hmP, hmC, hsum⟩ :=
    jordanHolderShortExactDecomposition ℂ G P.obj A.obj C.obj τ.obj
      (SmoothRep.hom j) (SmoothRep.hom (SmoothRep.mkQ A S)) hj
      (SmoothRep.mkQ_surjective A S) hex m hm
  have hP1 := HasJordanHolderMultiplicity.unique hmP (hasJordanHolderMultiplicity_one hP eP)
  have hQC := jordanHolderSurjectiveMonotonicity ℂ G C.obj Q.obj τ.obj (SmoothRep.hom r) hr
    mC 1 hmC (hasJordanHolderMultiplicity_one hQ eQ)
  omega

end Multiplicity

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

open PadicField.TopologicalData GeneralLinear

section Label

open Aubert.SegmentPolynomialSurjectivity in
/-- Zelevinsky 1980, Theorem 7.1 (multiplicity one): an irreducible subrepresentation of a
precedence-ordered product of segment socles occurs at most once in that product. -/
theorem compositionMultiplicity_le_one {n : ℕ} (D : T.SegmentProductDatum.{max uF uV, uF} n)
    (hs : D.HasSegmentSocles)
    (S : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hS : D.IsZelevinskySubrepresentation S) :
    letI := T.topology
    SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity
      ⟨D.induced, Aubert.SegmentProductClass.hasFiniteLength_induced F T D hs⟩ S ≤ 1 := by
  let := T.topology
  have hx := Aubert.binaryProductExactness F T
  have hl := Aubert.gradedInductionRingLaws F T hx
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hirr : S.IsIrreducible := hS.2.2.1
  have hlab : IsLabel F T D.multisegment n (irreducibleIsoClass n F.Carrier S hirr) :=
    ⟨S, hirr, rfl, D, rfl, hS⟩
  have h1 := coeff_mul_le_weightedCount F T (labelWeight_nonneg F T D.multisegment)
    (isEffective_zeta F T hx hl D.multisegment) n (irreducibleIsoClass n F.Carrier S hirr)
  have h2 := labelCount_zeta_le_one F T hx hl ψ (highestDerivativeLabelStep F T ψ)
    D.multisegment
  rw [labelWeight_of_isLabel F T hlab, mul_one, zeta_multisegment F T hx hl D hs,
    coeff_gradedInclusion_ofRepresentation F T n D.induced _ S hirr] at h1
  rw [zeta_multisegment F T hx hl D hs] at h2
  exact_mod_cast h1.trans h2

end Label

section Quotient

/-- Segments whose duals are linked are linked. -/
theorem isLinked_of_dual {Δ Γ : T.Segment.{max uF uV, uF}} (h : Δ.dual.IsLinked Γ.dual) :
    Δ.IsLinked Γ := by
  rcases h.precedes_or_precedes with h | h
  · exact ((Segment.precedes_dual_iff _ _).mp h).isLinked.symm
  · exact ((Segment.precedes_dual_iff _ _).mp h).isLinked

/-- Every irreducible quotient of a product of Zelevinsky socles with mutually unlinked
multisegments `a i` is a Zelevinsky socle of `∑ i, a i` (Zelevinsky 1980, proof of
Proposition 8.5, via smooth contragredients). -/
theorem isZelevinskySocle_of_quotient {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (a : Fin B.length → T.Multisegment.{max uF uV, uF})
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hπ : ∀ i, (a i).IsZelevinskySocle (π i))
    (hu : ∀ i j, i ≠ j → ∀ Δ ∈ a i, ∀ Δ' ∈ a j, ¬ Δ.IsLinked Δ')
    (Q : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology; Q.IsIrreducible)
    (q : letI := T.topology; (T.normalizedProductInductionFunctor B).obj π ⟶ Q)
    (hq : letI := T.topology; Function.Surjective (SmoothRep.hom q)) :
    (∑ i, a i).IsZelevinskySocle Q := by
  classical
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  have hG := GeneralLinear.compactOpen_cofinal F T n
  have hπirr (i : Fin B.length) : (π i).IsIrreducible :=
    (hπ i).choose_spec.2.2.2.1
  have hadm (i : Fin B.length) : IsAdmissible (π i).representation :=
    TwoFactorCommutativity.isAdmissible_of_isIrreducible F T _ (π i).isSmooth (hπirr i)
  have hQadm : Q.IsAdmissible :=
    TwoFactorCommutativity.isAdmissible_of_isIrreducible F T _ Q.isSmooth hQ
  have hQ' : Q.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hG Q hQadm).mpr hQ
  -- the dual data
  have hπ' (i : Fin B.length) :
      Multisegment.IsZelevinskySocle ((a i).map Segment.dual) (π i).contragredient :=
    (hπ i).contragredient (B.positive i)
  choose d' hd'm hd'z using hπ'
  let D' := SegmentProductDatum.concatenate B d'
  have hD'o : D'.IsPrecedenceOrdered := by
    refine SegmentProductDatum.concatenate_isPrecedenceOrdered B d' (fun i => (hd'z i).1) ?_
    intro i j hij Δ hΔ Δ' hΔ' hl
    rw [hd'm] at hΔ hΔ'
    obtain ⟨Δ₀, hΔ₀, rfl⟩ := Multiset.mem_map.mp hΔ
    obtain ⟨Δ₁, hΔ₁, rfl⟩ := Multiset.mem_map.mp hΔ'
    exact hu i j hij Δ₀ hΔ₀ Δ₁ hΔ₁ (isLinked_of_dual F T hl)
  have hD's : D'.HasSegmentSocles :=
    SegmentProductDatum.concatenate_hasSegmentSocles B d' (fun i => (hd'z i).2.1)
  obtain ⟨S', hS'⟩ := orderedMultisegmentSocleExistence F T n D' hD'o hD's
  obtain ⟨e, he⟩ := SegmentProductDatum.socleProductEmbedding B d'
    (fun i => (π i).contragredient) hd'z
  obtain ⟨E⟩ := TwoFactorCommutativity.productSmoothDual F T B
    (fun i => (π i).representation) hadm
  let j' := e.comp (E.symm.toIntertwiningMap.comp (SmoothRep.hom (SmoothRep.contragredientHom q)))
  have hj' : Function.Injective j' :=
    he.comp (E.symm.injective.comp (contragredientMap_injective_of_surjective _ hq))
  have hsoc : IsIrreducibleSocle D'.induced.representation Q.contragredient.representation :=
    hS'.2.2.of_subrepresentation ⟨hQ', j', hj'⟩
  have hdual :
      Multisegment.IsZelevinskySocle ((∑ i, a i).map Segment.dual) Q.contragredient := by
    refine ⟨D', ?_, hD'o, hD's, hsoc⟩
    rw [SegmentProductDatum.concatenate_multisegment,
      show Multiset.map Segment.dual (∑ i, a i) = ∑ i, Multiset.map Segment.dual (a i) from
        map_sum (Multiset.mapAddMonoidHom Segment.dual) a Finset.univ]
    exact Finset.sum_congr rfl fun i _ => hd'm i
  have hbidual := hdual.contragredient hn
  rw [Multiset.map_map] at hbidual
  have hid : (Segment.dual ∘ Segment.dual : T.Segment.{max uF uV, uF} → _) = id :=
    funext fun Δ => Segment.dual_dual Δ
  rw [hid, Multiset.map_id] at hbidual
  exact Multisegment.IsZelevinskySocle.of_iso hbidual (SmoothRep.bidualIso hG Q hQadm).symm

end Quotient

end Langlands.Classification.UnlinkedSocleProduct

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

/-- Zelevinsky 1980, Proposition 8.5: a normalized product of Zelevinsky socles whose
multisegments are mutually unlinked is a Zelevinsky socle of the sum of the multisegments. -/
theorem unlinkedSocleProductIrreducibility {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : UnlinkedSocleProductIrreducibility.{uF, uV} F T := by
  let := T.topology
  intro n B a π hπ hu
  choose d hda hdz using hπ
  let D := SegmentProductDatum.concatenate B d
  have hDm : D.multisegment = ∑ i, a i := by
    rw [SegmentProductDatum.concatenate_multisegment]
    exact Finset.sum_congr rfl fun i _ => hda i
  have hDo : D.IsPrecedenceOrdered :=
    SegmentProductDatum.concatenate_isPrecedenceOrdered B d (fun i => (hdz i).1)
      (fun i j hij => by rw [hda i, hda j]; exact hu i j hij)
  have hDs : D.HasSegmentSocles :=
    SegmentProductDatum.concatenate_hasSegmentSocles B d (fun i => (hdz i).2.1)
  obtain ⟨S, hS⟩ := orderedMultisegmentSocleExistence F T n D hDo hDs
  obtain ⟨j, hj⟩ := SegmentProductDatum.socleProductEmbedding B d π hdz
  let X := (T.normalizedProductInductionFunctor B).obj π
  suffices hirr : X.IsIrreducible from
    ⟨D, hDm, hDo, hDs, hS.2.2.of_subrepresentation ⟨hirr, j, hj⟩⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact rankZeroNormalizedProduct_isIrreducible F T B (fun i => (π i).representation)
  have : Nontrivial X := RegularHeadExistence.nontrivial_normalizedProductInduction T B π
    (fun i => SegmentHeadSupport.nontrivial_of_isIrreducible (hdz i).2.2.1)
  have hDfl := Aubert.SegmentProductClass.hasFiniteLength_induced F T D hDs
  have hfl : X.HasFiniteLength :=
    Aubert.ZelevinskyHighestDerivative.hasFiniteLength_of_injective (SmoothRep.ofHom j) hj hDfl
  refine UnlinkedSocleProduct.isIrreducible_of_multiplicity_le_one X S hfl
    (SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity ⟨X, hfl⟩ S)
    (SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity_witness ⟨X, hfl⟩ S) ?_ ?_ ?_
  · exact (jordanHolderInjectiveMonotonicity ℂ _ X.obj D.induced.obj S.obj j hj _ _
      (SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity_witness ⟨X, hfl⟩ S)
      (SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity_witness
        ⟨D.induced, hDfl⟩ S)).trans
      (UnlinkedSocleProduct.compositionMultiplicity_le_one F T D hDs S
        hS.isZelevinskySubrepresentation)
  · intro P j' hP hj'
    exact hS.2.2.nonempty_equiv_of_subrepresentation hP (j.comp (SmoothRep.hom j'))
      (hj.comp hj')
  · intro Q q hQ hq
    have hQz := UnlinkedSocleProduct.isZelevinskySocle_of_quotient F T hn B a π
      (fun i => ⟨d i, hda i, hdz i⟩) hu Q hQ q hq
    obtain ⟨e⟩ := nonempty_iso_of_isZelevinskySocle hQz ⟨D, hDm, hS⟩
    exact ⟨SmoothRep.equivOfIso e⟩

end Langlands.Classification

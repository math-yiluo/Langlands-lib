import Langlands.Representation.CuspidalSupport.RepeatedSubrepresentationProducts
import Langlands.Representation.CuspidalSupport.TripleInjectionTransport
import Langlands.Representation.CuspidalSupport.LiteralTwoBlockSwap
import Langlands.Representation.CuspidalSupport.UniformTripleRepresentativeTransport

/-! Actual exact-sequence construction of the two repeated-factor triple moves. -/

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Classification Parabolic Shahidi

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The literal smooth two-factor family has the displayed algebraic pair action. -/
def twoBlockPairEquiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier)),
      ((T.normalizedProductInductionFunctor (twoBlocks a b ha hb)).obj
        (twoBlockFactors ha hb A B)).representation.Equiv
      (T.normalizedProductInduced (twoBlocks a b ha hb)
        (pairFamily A.representation B.representation)) := by
  let := T.topology
  intro A B
  exact T.normalizedProductInducedEquiv (twoBlocks a b ha hb)
    (Fin.cases (Representation.Equiv.refl A.representation)
      (Fin.cases (Representation.Equiv.refl B.representation) finZeroElim))

/-- Identify the left grouping with the literal two-factor family constructors. -/
def uniformLeftProductEquiv {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (C A B : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d F.Carrier)),
      ((T.normalizedProductInductionFunctor (threeBlocks d d d hd hd hd)).obj
        (threeBlockSmoothFamily C A B)).representation.Equiv
      (T.normalizedProductInduced (Shahidi.twoBlocks d (d+d) hd (by omega))
        (pairFamily C.representation
          (T.normalizedProductInduced (Shahidi.twoBlocks d d hd hd)
            (fun i => (twoBlockFactors hd hd A B i).representation)))) := by
  let := T.topology
  intro C A B
  let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
    (twoBlockFactors hd hd A B)
  let eP : P.representation.Equiv
      (T.normalizedProductInduced (Shahidi.twoBlocks d d hd hd)
        (pairFamily A.representation B.representation)) :=
    T.normalizedProductInducedEquiv (Shahidi.twoBlocks d d hd hd)
      (Fin.cases (Representation.Equiv.refl A.representation)
        (Fin.cases (Representation.Equiv.refl B.representation) finZeroElim))
  let eOuter :
      (T.normalizedProductInduced (Shahidi.twoBlocks d (d+d) hd (by omega))
        (pairFamily C.representation
          (T.normalizedProductInduced (Shahidi.twoBlocks d d hd hd)
            (pairFamily A.representation B.representation)))).Equiv
      (T.normalizedProductInduced (Shahidi.twoBlocks d (d+d) hd (by omega))
        (pairFamily C.representation P.representation)) :=
    T.normalizedProductInducedEquiv (Shahidi.twoBlocks d (d+d) hd (by omega))
      (σ := pairFamily C.representation
        (T.normalizedProductInduced (Shahidi.twoBlocks d d hd hd)
          (pairFamily A.representation B.representation)))
      (τ := pairFamily C.representation P.representation)
      (Fin.cases (Representation.Equiv.refl C.representation)
        (Fin.cases eP.symm finZeroElim))
  exact (leftRegroupingEquiv.{uF,uV} T (orderedProductRegrouping F T)
    d d d hd hd hd C A B).trans eOuter

/-- An actual simple cuspidal Jacquet module of an irreducible admissible
object gives its injection into the displayed two-factor induction. -/
theorem injection_into_reversed_pair_of_adjacent_quotient {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (A B : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd A.obj B.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        ∃ f : (SmoothRep.quotient P S).representation.IntertwiningMap
          (T.normalizedParabolicInduced (Shahidi.twoBlocks d d hd hd)
            (FiniteTensor.externalSmoothObject (twoBlockFactors hd hd B.obj A.obj)).representation),
          Function.Injective f := by
  let := T.topology
  intro A B hAB P S hS₀ hS₁
  have hPred : ¬ P.IsIrreducible := by
    intro h
    rcases h.eq_bot_or_eq_top S with h | h
    · exact hS₀ h
    · exact hS₁ h
  have hstr := TwoSupercuspidalAdjacent.adjacentStructure F T hd
    (nonassociatedJacquetSubquotients F T (d+d))
    (associatedJacquetFiltration F T (d+d)) A B (Or.inr hAB)
  have hQi := ((hstr.1 hPred).2.2 S hS₀ hS₁).2
  let Q := SmoothRep.quotient P S
  let D := FiniteTensor.externalSmoothObject (twoBlockFactors hd hd B.obj A.obj)
  obtain ⟨eQ⟩ := (hstr.2 S hS₀ hS₁).2
  have hDD : SmoothRep.IsQuotient D D := ⟨𝟙 D, fun v => ⟨v,rfl⟩⟩
  have hOcc : SmoothRep.IsSubquotient D
      ((T.normalizedJacquetFunctor (Shahidi.twoBlocks d d hd hd)).obj Q) :=
    hDD.isSubquotient.of_iso_right (SmoothRep.mkIso eQ.symm)
  have hD := TwoSupercuspidalAdjacent.tensor_irreducible_cuspidal F T hd B A
  exact exists_inductionInjection_of_cuspidalOccurrence F T
    (Shahidi.twoBlocks d d hd hd) Q D hQi
    (cuspidalEmbedding F T (d+d) Q hQi).1 hD.1 hD.2 hOcc

/-- Exactness and the two repeated product irreducibility statements turn
an actual right-bracketed ABC injection into a BAC or CAB injection. -/
theorem rightRepeatedInjectionAlternative {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (E : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((d+d)+d) F.Carrier))
      (A B C : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      E.IsIrreducible →
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      (C = A ∨ C = B) →
      SmoothRep.IsSubrepresentation E
        ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
          (threeBlockSmoothFamily A.obj B.obj C.obj)) →
      SmoothRep.IsSubrepresentation E
        ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
          (threeBlockSmoothFamily B.obj A.obj C.obj)) ∨
      SmoothRep.IsSubrepresentation E
        ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
          (threeBlockSmoothFamily C.obj A.obj B.obj)) := by
  let := T.topology
  intro E A B C hEi hAB hC hIn
  have hdd : 0 < d+d := by omega
  let P := (T.normalizedProductInductionFunctor (twoBlocks d d hd hd)).obj
    (twoBlockFactors hd hd A.obj B.obj)
  let R := (T.normalizedProductInductionFunctor (twoBlocks d d hd hd)).obj
    (twoBlockFactors hd hd B.obj A.obj)
  let PC := (T.normalizedProductInductionFunctor (twoBlocks (d+d) d hdd hd)).obj
    (twoBlockFactors hdd hd P C.obj)
  let RC := (T.normalizedProductInductionFunctor (twoBlocks (d+d) d hdd hd)).obj
    (twoBlockFactors hdd hd R C.obj)
  obtain ⟨f,hf⟩ := hIn
  let ep := threeRightProductEquiv.{uF,uV} F T hd hd hd A.obj B.obj C.obj
  let fp : E.representation.IntertwiningMap PC.representation :=
    ep.toIntertwiningMap.comp (SmoothRep.hom f)
  have hfp : Function.Injective fp := ep.injective.comp hf
  have toBAC (g : E.representation.IntertwiningMap RC.representation)
      (hg : Function.Injective g) :
      SmoothRep.IsSubrepresentation E
        ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
          (threeBlockSmoothFamily B.obj A.obj C.obj)) := by
    let er := threeRightProductEquiv.{uF,uV} F T hd hd hd B.obj A.obj C.obj
    exact ⟨SmoothRep.ofHom (A := E) (er.symm.toIntertwiningMap.comp g),
      er.symm.injective.comp hg⟩
  by_cases hPi : P.IsIrreducible
  · obtain ⟨es⟩ := irreducibleTwoFactorProductSwap F T d hd
      A.obj B.obj A.property.1 B.property.1 hPi
    let fs := (SmoothRep.equivOfIso es).toIntertwiningMap
    let gs := rightProductMap F T hdd hd (A := P) (A' := R) fs C.obj
    have hgs : Function.Injective gs :=
      rightProductMap_injective F T hdd hd (P := P) (Q := R) fs C.obj
        (SmoothRep.equivOfIso es).injective
    exact Or.inl (toBAC (gs.comp fp) (hgs.comp hfp))
  · have hstr := TwoSupercuspidalAdjacent.adjacentStructure F T hd
      (nonassociatedJacquetSubquotients F T (d+d))
      (associatedJacquetFiltration F T (d+d)) A B (Or.inr hAB)
    obtain ⟨S,hS,_⟩ := (hstr.1 hPi).2.1
    let L := SmoothRep.subrepresentation P S
    let Q := SmoothRep.quotient P S
    let LC := (T.normalizedProductInductionFunctor (twoBlocks (d+d) d hdd hd)).obj
      (twoBlockFactors hdd hd L C.obj)
    let QC := (T.normalizedProductInductionFunctor (twoBlocks (d+d) d hdd hd)).obj
      (twoBlockFactors hdd hd Q C.obj)
    let i := SmoothRep.hom (SmoothRep.subtype P S)
    let q := SmoothRep.hom (SmoothRep.mkQ P S)
    have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
      change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ]
    let iC : LC.representation.IntertwiningMap PC.representation :=
      rightProductMap F T hdd hd (A := L) (A' := P) i C.obj
    let qC : PC.representation.IntertwiningMap QC.representation :=
      rightProductMap F T hdd hd (A := P) (A' := Q) q C.obj
    have hseq := rightProductMap_shortExact F T hdd hd i q C.obj
      (SmoothRep.subtype_injective P S) (SmoothRep.mkQ_surjective P S) hex
    have hLi : L.IsIrreducible := ((hstr.1 hPi).2.2 S hS.1 hS.2).1
    have hRepeated := decreasingAdjacentSubrepresentationRepeatedProducts.{uF,uV}
      F T d hd B A hAB S hS.1 hS.2
    have hLC : LC.IsIrreducible := by
      rcases hC with hC | hC
      · simpa only [LC,hC] using hRepeated.1
      · simpa only [LC,hC] using hRepeated.2
    have hfp₀ : fp ≠ 0 := by
      intro hz
      let := hEi
      let : Nontrivial E :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear ((d+d)+d) F.Carrier))
          E.representation.asModule
      obtain ⟨v,hv⟩ := exists_ne (0 : E)
      apply hv
      apply hfp
      simp [hz]
    rcases RepresentationExactComparison.equiv_left_or_injective_right
        hEi hLC iC qC fp hseq.1 hseq.2.1 hfp₀ with he | hqfp
    · obtain ⟨e⟩ := he
      let CL := (T.normalizedProductInductionFunctor (twoBlocks d (d+d) hd hdd)).obj
        (twoBlockFactors hd hdd C.obj L)
      let CP := (T.normalizedProductInductionFunctor (twoBlocks d (d+d) hd hdd)).obj
        (twoBlockFactors hd hdd C.obj P)
      let s := irreducibleLiteralTwoBlockSwapEquiv.{uF,max uF uV}
        F T hdd hd L C.obj hLi C.property.1 hLC
      let il : CL.representation.IntertwiningMap CP.representation :=
        leftProductMap F T hd hdd C.obj (B := L) (B' := P) i
      have hil : Function.Injective il :=
        leftProductMap_injective F T hd hdd C.obj (B := L) (B' := P)
          i (SmoothRep.subtype_injective P S)
      let ip := rankPullbackMap F T (Nat.add_assoc d d d) (E := CL) (Z := CP) il
      have hip : Function.Injective ip := by
        change Function.Injective (fun v : CL => il v)
        exact hil
      let ee := equivTrans
        (equivTrans (equivPrecomp (twoBlockPairEquiv.{uF,uV} F T hd hdd C.obj P)
            (reindex (R := F.Carrier) (finCongr (Nat.add_assoc d d d))).toMonoidHom)
          (equivPrecomp (equivSymm (uniformLeftProductEquiv.{uF,uV} F T hd C.obj A.obj B.obj))
            (reindex (R := F.Carrier) (finCongr (Nat.add_assoc d d d))).toMonoidHom))
        (uniformRightInductionEquiv.{uF,uV} F T hd C.obj A.obj B.obj)
      let g₁ : E.representation.IntertwiningMap
          (rankPullback F T (Nat.add_assoc d d d) CL).representation :=
        s.toIntertwiningMap.comp e.toIntertwiningMap
      let g := ee.toIntertwiningMap.comp (ip.comp g₁)
      exact Or.inr ⟨SmoothRep.ofHom (A := E) g,
        ee.injective.comp (hip.comp (s.injective.comp e.injective))⟩
    · obtain ⟨fq,hfq⟩ :=
        injection_into_reversed_pair_of_adjacent_quotient.{uF,uV}
          F T hd A B hAB S hS.1 hS.2
      let iq := rightProductMap F T hdd hd (A := Q) (A' := R) fq C.obj
      have hiq : Function.Injective iq :=
        rightProductMap_injective F T hdd hd (P := Q) (Q := R) fq C.obj hfq
      exact Or.inl (toBAC (iq.comp (qC.comp fp)) (hiq.comp hqfp))

/-- The actual uniform Jacquet occurrence gives the actual injection in the
right-bracketed rank used by the exact-sequence argument. -/
theorem rightInductionInjection_of_uniformOccurrence {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (E : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (d+(d+d)) F.Carrier))
      (A B C : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      E.IsIrreducible → E.IsAdmissible →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj C.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
      SmoothRep.IsSubrepresentation (rankPullback F T (Nat.add_assoc d d d) E)
        ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
          (threeBlockSmoothFamily A.obj B.obj C.obj)) := by
  let := T.topology
  intro E A B C hEi hEa hOcc
  obtain ⟨f,hf⟩ := exists_uniformTripleInductionInjection F T hd E A B C hEi hEa hOcc
  let Z := (T.normalizedProductInductionFunctor (threeBlocks d d d hd hd hd)).obj
    (threeBlockSmoothFamily A.obj B.obj C.obj)
  let f₀ : E.representation.IntertwiningMap Z.representation := f
  let g := rankPullbackMap F T (Nat.add_assoc d d d) (E := E) (Z := Z) f₀
  have hg : Function.Injective g := by
    change Function.Injective (fun v : E => f₀ v)
    exact hf
  let er := uniformRightInductionEquiv.{uF,uV} F T hd A.obj B.obj C.obj
  exact ⟨SmoothRep.ofHom (A := rankPullback F T (Nat.add_assoc d d d) E)
      (er.toIntertwiningMap.comp g), er.injective.comp hg⟩

/-- Both literal repeated-factor seed moves follow from the actual
right-bracketed injection alternative. -/
theorem repeatedTripleSeedTransfer :
    RepeatedTripleSeedTransfer.{uF,max uF uV} F T := by
  let := T.topology
  intro d hd E A B hEi hEa _hEf hAB
  have hEr := rankPullback_irreducible F T (Nat.add_assoc d d d) E hEi
  constructor
  · intro hOcc
    have hIn := rightInductionInjection_of_uniformOccurrence.{uF,uV}
      F T hd E A B B hEi hEa hOcc
    have hAlt := rightRepeatedInjectionAlternative.{uF,uV} F T hd
      (rankPullback F T (Nat.add_assoc d d d) E) A B B hEr hAB (Or.inr rfl) hIn
    rcases hAlt with h | h
    all_goals
      obtain ⟨g,hg⟩ := h
      exact uniformTripleOccurrence_of_rightInductionInjection.{uF,uV}
        F T hd E B A B hEi (SmoothRep.hom g) hg
  · intro hOcc
    have hIn := rightInductionInjection_of_uniformOccurrence.{uF,uV}
      F T hd E A B A hEi hEa hOcc
    have hAlt := rightRepeatedInjectionAlternative.{uF,uV} F T hd
      (rankPullback F T (Nat.add_assoc d d d) E) A B A hEr hAB (Or.inl rfl) hIn
    rcases hAlt with h | h
    · obtain ⟨g,hg⟩ := h
      exact Or.inr (uniformTripleOccurrence_of_rightInductionInjection.{uF,uV}
        F T hd E B A A hEi (SmoothRep.hom g) hg)
    · obtain ⟨g,hg⟩ := h
      exact Or.inl (uniformTripleOccurrence_of_rightInductionInjection.{uF,uV}
        F T hd E A A B hEi (SmoothRep.hom g) hg)

/-- The proved literal seeds and actual representative transport give the
full uniform local conjunction. -/
theorem uniformRepeatedCuspidalTripleJacquetTransfer :
    UniformRepeatedCuspidalTripleJacquetTransfer.{uF,max uF uV} F T :=
  uniformRepeatedTripleTransfer_of_seed F T (repeatedTripleSeedTransfer F T)

end Langlands.CuspidalSupport

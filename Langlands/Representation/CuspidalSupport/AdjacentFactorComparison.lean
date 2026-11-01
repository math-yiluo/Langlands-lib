import Langlands.Representation.CuspidalSupport.TripleInductionMaps
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentJacquetProof
import Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof

/-! Actual comparison of the two adjacent length-two factors. -/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Classification

universe uF uV uG

/-- The actual image of an injective intertwiner is equivalent to its source. -/
def injectionRangeEquiv
    {G : Type uG} [Group G] [TopologicalSpace G]
    (P Q : SmoothRep.{0,uG,uV} ℂ G)
    (f : Q.representation.IntertwiningMap P.representation)
    (hf : Function.Injective f) :
    Q.representation.Equiv (SmoothRep.subrepresentation P f.range).representation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hf)
    (fun g => by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ f g v))

/-- A simple object injected into a reducible representation with a unique
nonzero proper subrepresentation is that actual subrepresentation. -/
theorem nonempty_equiv_uniqueProper_of_injective
    {G : Type uG} [Group G] [TopologicalSpace G]
    (P Q : SmoothRep.{0,uG,uV} ℂ G)
    (hQ : Q.IsIrreducible) (hP : ¬ P.IsIrreducible)
    (S : Subrepresentation P.representation)
    (hu : ∀ R : Subrepresentation P.representation, R ≠ ⊥ → R ≠ ⊤ → R = S)
    (f : Q.representation.IntertwiningMap P.representation)
    (hf : Function.Injective f) :
    Nonempty (Q.representation.Equiv (SmoothRep.subrepresentation P S).representation) := by
  let := hQ
  let : Nontrivial Q :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) Q.representation.asModule
  have hR₀ : f.range ≠ ⊥ := by
    intro hr
    obtain ⟨v, hv⟩ := exists_ne (0 : Q)
    apply hv
    apply hf
    have hm : f v ∈ f.range := ⟨v, rfl⟩
    rw [hr] at hm
    exact (show f v = 0 from hm).trans (map_zero f).symm
  have hR₁ : f.range ≠ ⊤ := by
    intro hr
    have hs : Function.Surjective f := by
      intro y
      have hy : y ∈ f.range := by rw [hr]; trivial
      exact hy
    exact hP (JacquetLength.isIrreducible_of_equiv (f.ofBijective ⟨hf,hs⟩) hQ)
  have hRS : f.range = S := hu _ hR₀ hR₁
  let e := injectionRangeEquiv P Q f hf
  rw [← hRS]
  exact ⟨e⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Reversing an equal-rank product of simple factors preserves reducibility. -/
theorem twoBlock_reducible_swap {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear d F.Carrier)),
      A.IsIrreducible → B.IsIrreducible →
      ¬ ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd A B)).IsIrreducible →
      ¬ ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B A)).IsIrreducible := by
  let := T.topology
  intro A B hA hB hAB hBA
  obtain ⟨e⟩ := irreducibleTwoFactorProductSwap F T d hd B A hB hA hBA
  exact hAB (JacquetLength.isIrreducible_of_equiv (SmoothRep.equivOfIso e) hBA)

/-- A proper subrepresentation of the decreasing adjacent product is
equivalent to the quotient by any proper subrepresentation of the
increasing product. All factors and quotient carriers are actual. -/
theorem decreasingSubrepresentation_equiv_increasingQuotient {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd A.obj B.obj)
      let R := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ (S : Subrepresentation P.representation) (U : Subrepresentation R.representation),
        S ≠ ⊥ → S ≠ ⊤ → U ≠ ⊥ → U ≠ ⊤ →
        Nonempty ((SmoothRep.subrepresentation P S).representation.Equiv
          (SmoothRep.quotient R U).representation) := by
  let := T.topology
  intro B A hAB P R S U hS₀ hS₁ hU₀ hU₁
  have hPred : ¬ P.IsIrreducible := by
    intro h
    rcases h.eq_bot_or_eq_top S with h₀ | h₁
    · exact hS₀ h₀
    · exact hS₁ h₁
  have hRred : ¬ R.IsIrreducible :=
    twoBlock_reducible_swap F T hd A.obj B.obj A.property.1 B.property.1 hPred
  have hDec := TwoSupercuspidalAdjacent.adjacentStructure F T hd
    (nonassociatedJacquetSubquotients F T (d+d))
    (associatedJacquetFiltration F T (d+d)) A B (Or.inr hAB)
  have hInc := TwoSupercuspidalAdjacent.adjacentStructure F T hd
    (nonassociatedJacquetSubquotients F T (d+d))
    (associatedJacquetFiltration F T (d+d)) B A (Or.inl hAB)
  have hQi := ((hInc.1 hRred).2.2 U hU₀ hU₁).2
  let Q := SmoothRep.quotient R U
  let D := FiniteTensor.externalSmoothObject (twoBlockFactors hd hd A.obj B.obj)
  obtain ⟨eQ⟩ := (hInc.2 U hU₀ hU₁).2
  have hDD : SmoothRep.IsQuotient D D := ⟨𝟙 D, fun v => ⟨v,rfl⟩⟩
  have hOcc : SmoothRep.IsSubquotient D
      ((T.normalizedJacquetFunctor (Shahidi.twoBlocks d d hd hd)).obj Q) :=
    hDD.isSubquotient.of_iso_right (SmoothRep.mkIso eQ.symm)
  have hD := TwoSupercuspidalAdjacent.tensor_irreducible_cuspidal F T hd A B
  obtain ⟨f, hf⟩ := exists_inductionInjection_of_cuspidalOccurrence F T
    (Shahidi.twoBlocks d d hd hd) Q D hQi
    (cuspidalEmbedding F T (d+d) Q hQi).1 hD.1 hD.2 hOcc
  obtain ⟨S₀, _, hunique⟩ := (hDec.1 hPred).2.1
  have hu : ∀ X : Subrepresentation P.representation, X ≠ ⊥ → X ≠ ⊤ → X = S := by
    intro X hX₀ hX₁
    exact (hunique X ⟨hX₀,hX₁⟩).trans (hunique S ⟨hS₀,hS₁⟩).symm
  obtain ⟨e⟩ := nonempty_equiv_uniqueProper_of_injective P Q hQi hPred S hu f hf
  exact ⟨e.symm⟩

/-- A proper subrepresentation on the decreasing side ensures a proper
subrepresentation on the increasing side. -/
theorem decreasingProper_exists_increasingProper {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd A.obj B.obj)
      let R := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
        (twoBlockFactors hd hd B.obj A.obj)
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        ∃ U : Subrepresentation R.representation, U ≠ ⊥ ∧ U ≠ ⊤ := by
  let := T.topology
  intro B A hAB P R S hS₀ hS₁
  have hPred : ¬ P.IsIrreducible := by
    intro h
    rcases h.eq_bot_or_eq_top S with h | h
    · exact hS₀ h
    · exact hS₁ h
  have hRred := twoBlock_reducible_swap F T hd
    A.obj B.obj A.property.1 B.property.1 hPred
  obtain ⟨U, hU, _⟩ :=
    ((TwoSupercuspidalAdjacent.adjacentStructure F T hd
      (nonassociatedJacquetSubquotients F T (d+d))
      (associatedJacquetFiltration F T (d+d)) B A (Or.inl hAB)).1 hRred).2.1
  exact ⟨U, hU⟩

end Langlands.CuspidalSupport

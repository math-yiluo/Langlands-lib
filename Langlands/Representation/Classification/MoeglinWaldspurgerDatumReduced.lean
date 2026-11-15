import Langlands.Representation.Classification.MoeglinWaldspurgerPointBlocks
import Langlands.Representation.Classification.SegmentProductOrderedAssembly

/-!
# Left reducedness of segment products

Assuming the left cuspidal derivative lemma, a normalized product of finite-length left
`A`-reduced blocks is left `A`-reduced and has finite length.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification
open Langlands.Classification.LeftCuspidalDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem leftReduced_rankCast {d : ℕ}
    {A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)}
    {a b : ℕ} (h : a = b)
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hY : LeftReduced F T A Y) :
    LeftReduced F T A (letI := T.topology; (Derivative.generalLinearRankCast T h).obj Y) := by
  subst h
  exact hY

theorem hasFiniteLength_rankCast {a b : ℕ} (h : a = b)
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hY : letI := T.topology; Y.HasFiniteLength) :
    letI := T.topology; ((Derivative.generalLinearRankCast T h).obj Y).HasFiniteLength := by
  subst h
  exact hY

/-- **Products of reduced blocks.** A segment-product datum whose blocks have finite length
and are left `A`-reduced has a finite-length left `A`-reduced product. -/
theorem datum_leftReduced (hL : LeftCuspidalDerivativeLemma.{uF, uV}) {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    ∀ (k : ℕ) {n : ℕ} (D : T.SegmentProductDatum.{max uF uV, uF} n), D.length = k →
      (∀ i, LeftReduced F T A (D.blocks i)) →
      (letI := T.topology; ∀ i, (D.blocks i).HasFiniteLength) →
      LeftReduced F T A D.induced ∧ (letI := T.topology; D.induced.HasFiniteLength) := by
  let := T.topology
  obtain ⟨-, hprod, -, -, -⟩ := hL p F T d A
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n D hk hred hfin
  rcases k with _ | _ | k
  · -- no blocks: rank zero
    have hn : n = 0 := by
      have := D.degree_sum
      rcases D with ⟨r, segments, hsum, blocks⟩
      simp only at hk
      subst hk
      simpa using hsum.symm
    subst hn
    refine ⟨?_, ?_⟩
    · intro Z hZ hZY k' hk' σ
      omega
    · exact Derivative.ProductDerivativesFiniteLength.hasFiniteLength_of_iso
        (SegmentProductOrderedAssembly.zeroDatumUnitIso D).symm
        (Aubert.binaryProductUnit_hasFiniteLength F T)
  · -- one block
    have e := SegmentProductOrderedAssembly.singletonIso D hk ⟨0, by omega⟩
    exact ⟨leftReduced_of_iso e.symm (leftReduced_rankCast _ (hred _)),
      Derivative.ProductDerivativesFiniteLength.hasFiniteLength_of_iso e.symm
        (hasFiniteLength_rankCast _ (hfin _))⟩
  · -- split off the first block
    obtain ⟨e⟩ := SegmentProductSplit.nonempty_iso_binary D hk
    obtain ⟨htr, htf⟩ := ih (k + 1) (by omega) (SegmentProductSplit.tail D hk) rfl
      (fun j => hred _) (fun j => hfin _)
    have hhead := hred (D.shape.headIndex hk)
    have hheadf := hfin (D.shape.headIndex hk)
    refine ⟨leftReduced_of_iso e.symm (leftReduced_rankCast _ ?_),
      Derivative.ProductDerivativesFiniteLength.hasFiniteLength_of_iso e.symm
        (hasFiniteLength_rankCast _ ?_)⟩
    · exact hprod _ _ _ _ hheadf htf hhead htr
    · exact Aubert.binaryProduct_preservesFiniteLength F T _ _ _ _ hheadf htf

end Langlands.MoeglinWaldspurger.Derivation

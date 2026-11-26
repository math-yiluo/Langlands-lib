import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Langlands.VirtualRepresentation.DescentProof

/-! Aubert's support-sign adjustment over any nonarchimedean local field. -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear SmoothRep VirtualRepresentation
open AllFieldBZ.LocalFieldPackage.TopologicalData
open SmoothRep.IrreducibleGrothendieckProof

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

private theorem exists_support_of_pos {n : ℕ} (hn : 0 < n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier)),
      A.IsIrreducible →
      ∃ s : Multiset (CuspidalDatum.{max uF uV, uF} T), IsSupercuspidalSupport A s := by
  let := T.topology
  intro A hA
  obtain ⟨k, ρ, hρ⟩ := AllFieldBZ.glSupercuspidalEmbedding.{max uF uV, uF} K T n hn A hA
  exact ⟨_, k, ρ, rfl, hρ.isCuspidalConstituent⟩

private def countOfRep (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier)),
      A.IsIrreducible → ℕ :=
  letI := T.topology
  fun A hA => if hn : 0 < n then (Classical.choose (exists_support_of_pos T hn A hA)).card else 0

private theorem countOfRep_eq_support {n : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier))
      (hA : A.IsIrreducible) (s : Multiset (CuspidalDatum.{max uF uV, uF} T)),
      IsSupercuspidalSupport A s → countOfRep T n A hA = s.card := by
  let := T.topology
  intro A hA s hs
  by_cases hn : 0 < n
  · unfold countOfRep
    rw [dite_eq_left hn]
    exact congrArg Multiset.card
      (AllFieldBZ.glSupercuspidalSupportUniqueness.{max uF uV, uF} K T n hn A hA _ s
        (Classical.choose_spec (exists_support_of_pos T hn A hA)) hs)
  · simp only [countOfRep, dite_eq_right hn]
    obtain ⟨k, ρ, rfl, hsum, -⟩ := hs
    suffices hk : k = 0 by simp [hk]
    by_contra hne
    have hpos : 0 < ∑ i, (ρ i).rank :=
      Finset.sum_pos (fun i _ => (ρ i).rank_pos)
        ⟨⟨0, Nat.pos_of_ne_zero hne⟩, Finset.mem_univ _⟩
    exact hn (hsum ▸ hpos)

private theorem support_of_iso {n : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier)}
      (_e : A ≅ B) (_hB : B.IsIrreducible) {s : Multiset (CuspidalDatum.{max uF uV, uF} T)},
      IsSupercuspidalSupport A s → IsSupercuspidalSupport B s := by
  let := T.topology
  intro A B e hB s hs
  obtain ⟨k, ρ, hρ, hsum, V, hV, _, hSub⟩ := hs
  exact ⟨k, ρ, hρ, hsum, V, hV, hB, IsSubquotient.of_iso_left e hSub⟩

/-- The cardinality, with multiplicity, of the actual supercuspidal support
of an irreducible class, with the empty support in rank zero. -/
def supportCount (n : ℕ) :
    letI := T.topology
    GeneralLinear.IrreducibleIsoClass.{uV, uF} n K.Carrier → ℕ :=
  letI := T.topology
  Quotient.lift (fun A => countOfRep T n A.val A.property) fun A B h => by
    by_cases hn : 0 < n
    · obtain ⟨e⟩ := h
      obtain ⟨s, hs⟩ := exists_support_of_pos.{uF, uV} T hn A.val A.property
      rw [countOfRep_eq_support T A.val A.property s hs,
        countOfRep_eq_support T B.val B.property s (support_of_iso T e B.property hs)]
    · simp only [countOfRep, dite_eq_right hn]

/-- Aubert's sign `(-1)^(n-k)` when the support contains `k` cuspidal factors. -/
def supportSign (n : ℕ) :
    letI := T.topology
    GeneralLinear.IrreducibleIsoClass.{uV, uF} n K.Carrier → ℤ :=
  letI := T.topology
  fun c => (-1 : ℤ) ^ (n - supportCount T n c)

theorem supportSign_of_support {n : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier))
      (hA : A.IsIrreducible) (s : Multiset (CuspidalDatum.{max uF uV, uF} T)),
      IsSupercuspidalSupport A s →
        supportSign T n (SmoothRep.irreducibleIsoClass A hA) = (-1 : ℤ) ^ (n - s.card) := by
  let := T.topology
  intro A hA s hs
  change (-1 : ℤ) ^ (n - countOfRep T n A hA) = (-1 : ℤ) ^ (n - s.card)
  rw [countOfRep_eq_support T A hA s hs]

@[simp]
theorem supportSign_rankZero :
    letI := T.topology
    ∀ c : GeneralLinear.IrreducibleIsoClass.{uV, uF} 0 K.Carrier, supportSign T 0 c = 1 := by
  let := T.topology
  intro c
  simp [supportSign]

/-- Extend the support-sign adjustment of a homogeneous endomorphism
additively using the exact Jordan–Hölder comparison. -/
def adjustOperator (n : ℕ) :
    letI := T.topology
    (GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier) →
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier :=
  letI := T.topology
  fun D => (extend fun c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n K.Carrier =>
    supportSign T n c • D (realizeIrreducibles ℂ (GeneralLinear n K.Carrier) (generator c))).comp
      factorMap

/-- The adjusted operator satisfies Aubert's formula on actual irreducible classes. -/
theorem adjustOperator_irreducible (n : ℕ) :
    letI := T.topology
    ∀ (D : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier)
      (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier))
      (hA : A.IsIrreducible) (hL : A.HasFiniteLength),
      adjustOperator T n D (finiteLengthClass n K.Carrier A hL) =
        supportSign T n (SmoothRep.irreducibleIsoClass A hA) •
          D (finiteLengthClass n K.Carrier A hL) := by
  let := T.topology
  intro D A hA hL
  change extend _ (factorMap (FiniteLengthGrothendieckGroup.ofRepresentation A hL)) = _
  rw [factorMap_ofRepresentation, compositionFactors_irreducible A hA, extend_generator,
    realizeIrreducibles_generator_irreducibleIsoClass A hA hL]
  rfl

end Langlands.Aubert.LocalFieldGraded

import Langlands.Representation.Classification.SegmentSocleDerivativesProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Classification.SegmentProductCuspidalEmbedding

/-! Support witnesses for actual constituents of derivatives of segment products. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentSocleDerivativeConstituentSupport

open GeneralLinear PadicField.TopologicalData Derivative
open SegmentProductOrderedAssembly SegmentProductCuspidalEmbedding

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An irreducible subquotient of a representation embedded in a supplied
cuspidal product has that product's multiset as a support. -/
theorem support_of_embedding {n : ℕ}
    {A D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hA : EmbedsCuspidal T A s)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology; SmoothRep.IsSubquotient D A) :
    T.IsSupercuspidalSupport D s := by
  let := T.topology
  obtain ⟨r, ρ, hρ, R, hR, hρs, f, hf⟩ := hA
  refine ⟨r, ρ, hρs, hρ, R, hR, hD, ?_⟩
  exact smoothSubquotientTransitivity ℂ _ _ _ _ hDA
    (SmoothRep.IsSubrepresentation.isSubquotient ⟨f, hf⟩)

/-- Every irreducible constituent of a supplied segment-socle product has
exactly the multiset of all segment members as a support. -/
theorem support_of_product {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (hd : d.HasSegmentSocles)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology; SmoothRep.IsSubquotient D d.induced) :
    T.IsSupercuspidalSupport D d.multisegment.cuspidalContent :=
  support_of_embedding T (embedsCuspidal_induced d hd) hD hDA

/-- A supplied segment socle embeds in the product of its ordered members. -/
theorem segment_embedding (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hA : T.IsSegmentSocle Δ A) : EmbedsCuspidal T A Δ.cuspidalContent := by
  let := T.topology
  let d := cons Δ A (empty : SegmentProductDatum.{uV, uF} T 0)
  have hd : d.HasSegmentSocles := cons_hasSegmentSocles Δ A empty hA empty_hasSegmentSocles
  have hE := embedsCuspidal_induced d hd
  have hcontent : d.multisegment.cuspidalContent = Δ.cuspidalContent := by
    simp [d, SegmentProductDatum.multisegment, cons_segments]
  rw [hcontent] at hE
  have e : d.induced ≅ (generalLinearRankCast T (Nat.add_zero Δ.degree).symm).obj A := by
    exact singletonIso d rfl (0 : Fin 1)
  have he := hE.of_iso e.symm
  have ht : EmbedsCuspidal T
      ((generalLinearRankCast T (Nat.add_zero Δ.degree)).obj
        ((generalLinearRankCast T (Nat.add_zero Δ.degree).symm).obj A)) Δ.cuspidalContent :=
    he.rankCast (Nat.add_zero Δ.degree)
  exact ht

/-- At rank zero, every irreducible representation is a constituent of the
empty cuspidal product, so its support is the empty multiset. -/
theorem support_zero
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible) :
    T.IsSupercuspidalSupport D (0 : Multiset (CuspidalDatum.{uV, uF} T)) := by
  let := T.topology
  let ρ : Fin 0 → CuspidalDatum.{uV, uF} T := Fin.elim0
  have hρ : ∑ i, (ρ i).rank = 0 := by simp
  let R : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank) :=
    fun i => i.elim0
  let P := T.cuspidalProductInduced ρ hρ R
  let eP : P ≅ T.binaryProductUnit.{uF, max uF uV} :=
    T.emptyProductUnitIso (T.cuspidalShape ρ hρ) (fun i => (R i).obj)
  have hP : Module.finrank ℂ P = 1 :=
    (SmoothRep.equivOfIso eP).toLinearEquiv.finrank_eq.trans T.finrank_binaryProductUnit
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hP
  obtain ⟨_, q, hq⟩ := isIrreducibleQuotient_of_subsingleton_linearEquiv
    P.representation D.representation hD e.symm
  exact ⟨0, ρ, by simp [ρ], hρ, R, (fun i => i.elim0), hD,
    SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩⟩

/-- An irreducible constituent forces its source to be nonzero. -/
theorem nontrivial_of_constituent {n : ℕ}
    {A D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology; SmoothRep.IsSubquotient D A) : Nontrivial A := by
  let := T.topology
  apply not_subsingleton_iff_nontrivial.mp
  intro hA
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  have hDz : Subsingleton D := ⟨fun d e => by
    obtain ⟨x, rfl⟩ := hq d
    obtain ⟨y, rfl⟩ := hq e
    exact congrArg (SmoothRep.hom q) (hi (hA.elim _ _))⟩
  let : D.representation.IsIrreducible := hD
  exact (not_nontrivial_iff_subsingleton.mpr hDz)
    (IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      D.representation.asModule)

/-- Equality transport of ranks preserves a supplied support witness. -/
theorem support_rankCast_iff {a b : ℕ} (h : a = b)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    T.IsSupercuspidalSupport ((generalLinearRankCast T h).obj D) s ↔
      T.IsSupercuspidalSupport D s := by
  subst h
  rfl

/-- Equality transport of ranks preserves irreducibility. -/
theorem irreducible_rankCast {a b : ℕ} (h : a = b)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible) :
    letI := T.topology; ((generalLinearRankCast T h).obj D).IsIrreducible := by
  subst h
  exact hD

/-- Equality transport of ranks preserves actual subquotient occurrences. -/
theorem subquotient_rankCast {a b : ℕ} (h : a = b)
    {D A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hDA : letI := T.topology; SmoothRep.IsSubquotient D A) :
    letI := T.topology
    SmoothRep.IsSubquotient ((generalLinearRankCast T h).obj D)
      ((generalLinearRankCast T h).obj A) := by
  subst h
  exact hDA

theorem castRank_eq {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    T.castRank h A = (generalLinearRankCast T h).obj A := by
  subst h
  rfl

/-- The content remaining after choosing the zero or rank derivative of a
segment. A shortened singleton has empty content. -/
def residualContent (Δ : Segment.{uV, uF} T) (shorten : Bool) :
    Multiset (CuspidalDatum.{uV, uF} T) :=
  if shorten then
    if h : 2 ≤ Δ.length then
      (⟨Δ.base, Δ.length - 1, by omega⟩ : Segment.{uV, uF} T).cuspidalContent
    else 0
  else Δ.cuspidalContent

/-- A simple constituent of a segment derivative chooses either the unchanged
segment or its end truncation, with the corresponding derivative order. -/
theorem segment_support
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hA : T.IsSegmentSocle Δ A) (i : ℕ) (hi : i ≤ Δ.degree)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - i) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ Δ.degree i hi).obj A)) :
    ∃ b : Bool, i = (if b then Δ.rank else 0) ∧
      T.IsSupercuspidalSupport D (residualContent T Δ b) := by
  let := T.topology
  by_cases hi0 : i = 0
  · subst i
    exact ⟨false, rfl, support_of_embedding T (segment_embedding T Δ A hA) hD hDA⟩
  have hseg := segmentSocleDerivatives F T ψ Δ A hA
  have hir : i = Δ.rank := by
    by_contra hne
    exact (not_nontrivial_iff_subsingleton.mpr (hseg.1 i hi (by omega) hne))
      (nontrivial_of_constituent T hD hDA)
  subst i
  refine ⟨true, rfl, ?_⟩
  by_cases h₂ : 2 ≤ Δ.length
  · let Δ' : Segment.{uV, uF} T := ⟨Δ.base, Δ.length - 1, by omega⟩
    have hdeg : Δ.degree - Δ.rank = Δ'.degree := by
      simpa only [Segment.degree, Δ', Nat.one_mul] using
        (Nat.sub_mul Δ.length 1 Δ.rank).symm
    let A' := (generalLinearRankCast T hdeg).obj
      ((generalLinearDerivative T ψ Δ.degree Δ.rank hi).obj A)
    have hA' : T.IsSegmentSocle Δ' A' := by
      have h := hseg.2.2 hi h₂ hdeg
      rw [castRank_eq T] at h
      exact h
    have hD' := irreducible_rankCast T hdeg D hD
    have hDA' := subquotient_rankCast T hdeg hDA
    have hs := support_of_embedding T (segment_embedding T Δ' A' hA') hD' hDA'
    have hs' := (support_rankCast_iff T hdeg D Δ'.cuspidalContent).mp hs
    simpa only [residualContent, Bool.true_eq, ↓reduceIte, dite_eq_left h₂] using hs'
  · have h₁ : Δ.length = 1 := by have := Δ.length_pos; omega
    have hdeg : Δ.degree - Δ.rank = 0 := by
      simp only [Segment.degree, h₁, Nat.one_mul, Nat.sub_self]
    have hs := support_zero T ((generalLinearRankCast T hdeg).obj D)
      (irreducible_rankCast T hdeg D hD)
    have hs' := (support_rankCast_iff T hdeg D 0).mp hs
    simpa only [residualContent, Bool.true_eq, ↓reduceIte, dite_eq_right h₂] using hs'

end Langlands.Classification.SegmentSocleDerivativeConstituentSupport

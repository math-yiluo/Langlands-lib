import Langlands.Representation.Classification.LeftCuspidalDerivative.Frobenius
import Langlands.Representation.Classification.SegmentSocleJacquetProof
import Langlands.Representation.Classification.SegmentHeadJacquetProof
import Langlands.Representation.Classification.SegmentHeadContragredient
import Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Tensor.SmoothSubquotients

/-!
# Segment heads and socles are left reduced

Clause (segments) of the highest left cuspidal derivative lemma: a segment socle of `Δ` is
left `A`-reduced unless the beginning of `Δ` is the class of `A`, and a segment head of `Δ`
is left `A`-reduced unless the end of `Δ` is the class of `A`. The proof combines first
adjointness for `A × σ` with the two-block Jacquet formulas of Zelevinsky (1980,
Propositions 3.4 and 9.5).
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section Supercuspidal

/-- The upper parabolic of a two-block shape is proper. -/
theorem ofPair_parabolic_ne_top {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = n) :
    (BlockShape.ofPair a b ha hb h).parabolic F.Carrier ≠ ⊤ := by
  intro htop
  have hs := CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top _ htop
  have h01 : (⟨0, by simp⟩ : Fin (BlockShape.ofPair a b ha hb h).length) =
      ⟨1, by simp⟩ := Subsingleton.elim _ _
  exact absurd (congrArg Fin.val h01) (by simp)

/-- A supercuspidal representation has trivial Jacquet module along a two-block shape. -/
theorem subsingleton_jacquet_of_isSupercuspidal {n a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = n) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      IsSupercuspidal π.representation →
        Subsingleton ((T.normalizedJacquetFunctor (BlockShape.ofPair a b ha hb h)).obj π) := by
  let _ := T.topology
  intro π hsc
  change Subsingleton ((BlockShape.ofPair a b ha hb h).JacquetModule π.representation)
  exact ((CuspidalSupport.standardJacquetSupercuspidalityClause T n
    π.obj π.representation).mp hsc).2 _ (ofPair_parabolic_ne_top F ha hb h)

/-- An object isomorphic to a nontrivial one is not subsingleton. -/
theorem not_subsingleton_of_iso {G : Type uF} [Group G] [TopologicalSpace G]
    {X Y : SmoothRep.{0, uF, uV} ℂ G} (e : X ≅ Y) [Nontrivial Y] : ¬ Subsingleton X := by
  intro hX
  obtain ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
  obtain ⟨x₁, rfl⟩ := Derivative.LevelCalculus.iso_hom_surjective e y₁
  obtain ⟨x₂, rfl⟩ := Derivative.LevelCalculus.iso_hom_surjective e y₂
  exact hy (congrArg _ (Subsingleton.elim x₁ x₂))

end Supercuspidal

section LengthOne

/-- A segment socle that is supercuspidal comes from a one-term segment. -/
theorem length_eq_one_of_isSegmentSocle_of_isSupercuspidal :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → IsSupercuspidal π.representation → Δ.length = 1 := by
  let _ := T.topology
  intro Δ π hπ hsc
  by_contra hne
  have h1 : 1 < Δ.length := by have := Δ.length_pos; omega
  obtain ⟨π₁, π₂, h₁, h₂, ⟨e⟩⟩ :=
    ((segmentSocleJacquetFormula.{uF, uV} F T) Δ π hπ).2 1 Nat.one_pos h1
  have hnt : Nontrivial (FiniteTensor.externalFunctor.obj
      (Δ.socleSplitFactors 1 Nat.one_pos h1 π₁ π₂)) := by
    have hn₁ : Nontrivial π₁ := SegmentSocleDerivativesProof.nontrivial_of_isIrreducible
      (SegmentSocleDerivativesProof.isIrreducible_of_isSegmentSocle T h₁)
    have hn₂ : Nontrivial π₂ := SegmentSocleDerivativesProof.nontrivial_of_isIrreducible
      (SegmentSocleDerivativesProof.isIrreducible_of_isSegmentSocle T h₂)
    apply SegmentSocleDerivativesProof.nontrivial_piTensorProduct
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => absurd j.2 (Nat.not_lt_zero _)) j) i
    · exact hn₁
    · exact hn₂
  exact not_subsingleton_of_iso e
    (subsingleton_jacquet_of_isSupercuspidal F T _ _ _ π hsc)

/-- A segment head that is supercuspidal comes from a one-term segment. -/
theorem length_eq_one_of_isSegmentHead_of_isSupercuspidal :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π → IsSupercuspidal π.representation → Δ.length = 1 := by
  let _ := T.topology
  intro Δ π hπ hsc
  by_contra hne
  have h1 : 1 < Δ.length := by have := Δ.length_pos; omega
  obtain ⟨π₁, π₂, h₁, h₂, ⟨e⟩⟩ :=
    ((segmentHeadJacquetFormula.{uF, uV} F T) Δ π hπ).2 1 Nat.one_pos h1
  have hnt : Nontrivial (FiniteTensor.externalFunctor.obj
      (Δ.splitFactors 1 Nat.one_pos h1 π₁ π₂)) := by
    have hn₁ : Nontrivial π₁ := by
      obtain ⟨_, _, hh⟩ := h₁
      exact SegmentSocleDerivativesProof.nontrivial_of_isIrreducible hh.1
    have hn₂ : Nontrivial π₂ := by
      obtain ⟨_, _, hh⟩ := h₂
      exact SegmentSocleDerivativesProof.nontrivial_of_isIrreducible hh.1
    apply SegmentSocleDerivativesProof.nontrivial_piTensorProduct
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => absurd j.2 (Nat.not_lt_zero _)) j) i
    · exact hn₁
    · exact hn₂
  exact not_subsingleton_of_iso e
    (subsingleton_jacquet_of_isSupercuspidal F T _ _ _ π hsc)

/-- A head of a one-term segment is equivalent to the rank transport of a supercuspidal
representative of the segment's base. -/
theorem exists_equiv_castRank_of_isSegmentHead_length_one :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π → Δ.length = 1 →
        ∃ A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
          Δ.base.IsRepresentedBy A ∧ ∀ h : Δ.rank = Δ.degree,
            Nonempty (π.representation.Equiv (T.castRank h A.obj).representation) := by
  let _ := T.topology
  intro Δ
  obtain ⟨ρ, m, hm⟩ := Δ
  intro π hπ h1
  change m = 1 at h1
  subst h1
  obtain ⟨A, hA, hirr, q, hq, -⟩ := hπ
  refine ⟨A, hA, fun h => ?_⟩
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (Nat.one_mul ρ.rank).symm A.obj A.property.1
  let g := q.comp e.symm.toIntertwiningMap
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨e x, by simp [g]⟩
  have hnt := SegmentSocleDerivativesProof.nontrivial_of_isIrreducible hirr
  have := hB
  rcases Representation.IsIrreducible.injective_or_eq_zero g with hinj | h0
  · exact ⟨(Representation.IntertwiningMap.ofBijective g ⟨hinj, hg⟩).symm⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_ne (0 : π)
    obtain ⟨x, rfl⟩ := hg y
    apply hy
    rw [h0]
    rfl

/-- A one-term segment ends at its beginning. -/
theorem last_eq_base_of_length_eq_one (Δ : T.Segment.{uV, uF}) (h : Δ.length = 1) :
    Δ.last = Δ.base := by
  simp [Segment.last, h]

end LengthOne

section Target

/-- A nonzero intertwiner from a segment socle to an irreducible supercuspidal
representation forces a one-term segment whose base is represented by the target. -/
theorem isSegmentSocle_supercuspidal_target :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π A' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → A'.IsIrreducible → IsSupercuspidal A'.representation →
      ∀ g : π.representation.IntertwiningMap A'.representation, g ≠ 0 →
        Δ.length = 1 ∧ ∃ A₀ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
          Δ.base.IsRepresentedBy A₀ ∧ ∀ h : Δ.rank = Δ.degree,
            Nonempty ((T.castRank h A₀.obj).representation.Equiv A'.representation) := by
  let _ := T.topology
  intro Δ π A' hπ hA'irr hA'sc g hg
  have hirr := SegmentSocleDerivativesProof.isIrreducible_of_isSegmentSocle T hπ
  have := hirr
  have := hA'irr
  obtain ⟨E⟩ := nonempty_equiv_of_ne_zero g hg
  have hsc : IsSupercuspidal π.representation :=
    GeneralLinear.isSupercuspidal_of_equiv E.symm hA'sc
  have h1 := length_eq_one_of_isSegmentSocle_of_isSupercuspidal F T Δ π hπ hsc
  obtain ⟨A₀, hA₀, hE⟩ :=
    SegmentSocleDerivativesProof.exists_equiv_castRank_of_length_one T Δ π hπ h1
  refine ⟨h1, A₀, hA₀, fun h => ?_⟩
  obtain ⟨E₀⟩ := hE h
  exact ⟨E₀.symm.trans E⟩

/-- A nonzero intertwiner from a segment head to an irreducible supercuspidal
representation forces a one-term segment whose base is represented by the target. -/
theorem isSegmentHead_supercuspidal_target :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π A' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π → A'.IsIrreducible → IsSupercuspidal A'.representation →
      ∀ g : π.representation.IntertwiningMap A'.representation, g ≠ 0 →
        Δ.length = 1 ∧ ∃ A₀ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
          Δ.base.IsRepresentedBy A₀ ∧ ∀ h : Δ.rank = Δ.degree,
            Nonempty ((T.castRank h A₀.obj).representation.Equiv A'.representation) := by
  let _ := T.topology
  intro Δ π A' hπ hA'irr hA'sc g hg
  have hirr : π.IsIrreducible := by
    obtain ⟨_, _, hh⟩ := hπ
    exact hh.1
  have := hirr
  have := hA'irr
  obtain ⟨E⟩ := nonempty_equiv_of_ne_zero g hg
  have hsc : IsSupercuspidal π.representation :=
    GeneralLinear.isSupercuspidal_of_equiv E.symm hA'sc
  have h1 := length_eq_one_of_isSegmentHead_of_isSupercuspidal F T Δ π hπ hsc
  obtain ⟨A₀, hA₀, hE⟩ := exists_equiv_castRank_of_isSegmentHead_length_one F T Δ π hπ h1
  refine ⟨h1, A₀, hA₀, fun h => ?_⟩
  obtain ⟨E₀⟩ := hE h
  exact ⟨E₀.symm.trans E⟩

/-- Two cuspidal data whose supercuspidal representatives become equivalent after rank
transport to a common rank are equal. -/
theorem cuspidalDatum_eq_of_castRank_equiv {ρ₁ ρ₂ : T.CuspidalDatum.{uV, uF}} {s t : ℕ}
    (A₁ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ₁.rank))
    (A₂ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := s))
    (h₁ : ρ₁.IsRepresentedBy A₁) (hs : ρ₂.rank = s) (h₂ : ρ₂.IsRepresentedBy (hs ▸ A₂))
    (ht₁ : ρ₁.rank = t) (ht₂ : s = t)
    (E : letI := T.topology
      Nonempty ((T.castRank ht₁ A₁.obj).representation.Equiv
        (T.castRank ht₂ A₂.obj).representation)) :
    ρ₁ = ρ₂ := by
  let _ := T.topology
  subst ht₂
  subst hs
  obtain ⟨E⟩ := E
  exact CuspidalSupport.cuspidalDatum_eq_of_equiv A₁ A₂ h₁ h₂ (finCongr ht₁)
    (GeneralLinear.reindex (R := F.Carrier) (finCongr ht₁)).symm.toMonoidHom
    (fun _ _ _ => rfl) ((T.castRankEquiv ht₁ A₁.obj).trans E)

end Target

section Main

/-- An irreducible subquotient of an irreducible representation is equivalent to it. -/
theorem nonempty_equiv_of_isSubquotient_irreducible {n : ℕ} :
    letI := T.topology
    ∀ (π Z : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible → Z.IsIrreducible → SmoothRep.IsSubquotient Z π →
        Nonempty (π.representation.Equiv Z.representation) := by
  let _ := T.topology
  intro π Z hπ hZ h
  exact CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient hπ hZ
    (SmoothRep.isSubquotient_iff_representation.mp h)

/-- **Segment socles.** For a cuspidal datum `κ` represented by `A`, a segment socle of `Δ`
is left `A`-reduced unless `Δ.base = κ`. -/
theorem leftReduced_of_isSegmentSocle {d : ℕ}
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (κ : T.CuspidalDatum.{max uF uV, uF}) (hκ : κ.rank = d) (hA : κ.IsRepresentedBy (hκ ▸ A))
    (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentSocle Δ π) (hne : Δ.base ≠ κ) : LeftReduced F T A π := by
  let _ := T.topology
  intro Z hZ hZπ k h σ hsub
  obtain ⟨E⟩ := nonempty_equiv_of_isSubquotient_irreducible F T π Z
    (SegmentSocleDerivativesProof.isIrreducible_of_isSegmentSocle T hπ) hZ hZπ
  have hZs : T.IsSegmentSocle Δ Z := SegmentSocleDerivativesProof.isSegmentSocle_of_equiv T E hπ
  have hZnt : Nontrivial Z := SegmentSocleDerivativesProof.nontrivial_of_isIrreducible hZ
  have hd : 0 < d := hκ ▸ κ.rank_pos
  apply hne
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨g, hg⟩ := exists_ne_zero_of_isSubrepresentation_rankZero F T h Z A.obj σ hZnt hsub
    obtain ⟨h1, A₀, hA₀, hE⟩ := isSegmentSocle_supercuspidal_target F T Δ Z (T.castRank h A.obj)
      hZs (T.isIrreducible_castRank h A.obj A.property.1)
      (SegmentSocleDerivativesProof.isSupercuspidal_castRank T h A.obj A.property.2) g hg
    have hr : Δ.rank = Δ.degree := by
      change Δ.rank = Δ.length * Δ.rank
      rw [h1, Nat.one_mul]
    exact cuspidalDatum_eq_of_castRank_equiv F T A₀ A hA₀ hκ hA hr h (hE hr)
  · obtain ⟨g, hg⟩ := exists_jacquet_ne_zero_of_isSubrepresentation F T hd hk h Z A.obj σ hZnt hsub
    by_cases hdvd : Δ.rank ∣ d
    · obtain ⟨q, hq⟩ := hdvd
      rw [Nat.mul_comm] at hq
      subst hq
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
      have h' : q * Δ.rank + k = Δ.length * Δ.rank := h
      have hqm : q < Δ.length := by
        apply Nat.lt_of_mul_lt_mul_right (a := Δ.rank)
        omega
      obtain rfl : k = (Δ.length - q) * Δ.rank := by
        rw [Nat.sub_mul]
        omega
      obtain ⟨π₁, π₂, h₁, -, ⟨e⟩⟩ :=
        ((segmentSocleJacquetFormula.{uF, max uF uV} F T) Δ Z hZs).2 q hq0 hqm
      let f : (FiniteTensor.external (H := fun i : Fin 2 =>
            GeneralLinear ((Δ.socleSplitShape q hq0 hqm).size i) F.Carrier)
            (fun i => (Δ.socleSplitFactors q hq0 hqm π₁ π₂ i).representation)).IntertwiningMap
          (FiniteTensor.external (H := fun i : Fin 2 =>
            GeneralLinear ((Δ.socleSplitShape q hq0 hqm).size i) F.Carrier)
            (fun i => (twoBlockFactors hd hk A.obj σ i).representation)) :=
        g.comp (SmoothRep.hom e.inv)
      have hf : f ≠ 0 := by
        intro h0
        apply hg
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        have := congrArg (fun φ => φ (SmoothRep.hom e.hom x)) h0
        simp only [f] at this
        change g (SmoothRep.hom e.inv (SmoothRep.hom e.hom x)) = 0 at this
        have hx := Derivative.LevelCalculus.hom_inv_apply e x
        change g x = 0
        calc g x = g (SmoothRep.hom e.inv (SmoothRep.hom e.hom x)) := congrArg g hx.symm
          _ = 0 := this
      obtain ⟨g', hg'⟩ := exists_firstFactor_ne_zero _ _ f hf
      obtain ⟨h1, A₀, hA₀, hE⟩ := isSegmentSocle_supercuspidal_target F T (Δ.initial q hq0) π₁
        A.obj h₁ A.property.1 A.property.2 g' hg'
      have hr : (Δ.initial q hq0).rank = (Δ.initial q hq0).degree := by
        change (Δ.initial q hq0).rank = (Δ.initial q hq0).length * (Δ.initial q hq0).rank
        rw [h1, Nat.one_mul]
      exact cuspidalDatum_eq_of_castRank_equiv F T A₀ A hA₀ hκ hA hr rfl (hE hr)
    · exfalso
      have hln : d < Δ.degree := by omega
      obtain rfl : k = Δ.degree - d := by omega
      have hsub0 := ((segmentSocleJacquetFormula.{uF, max uF uV} F T) Δ Z hZs).1 d hd hln hdvd
      apply hg
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      have hx : x = 0 := @Subsingleton.elim _ hsub0 x 0
      rw [hx, map_zero, map_zero]

/-- **Segment heads.** For a cuspidal datum `κ` represented by `A`, a segment head of `Δ`
is left `A`-reduced unless `Δ.last = κ`. -/
theorem leftReduced_of_isSegmentHead {d : ℕ}
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (κ : T.CuspidalDatum.{max uF uV, uF}) (hκ : κ.rank = d) (hA : κ.IsRepresentedBy (hκ ▸ A))
    (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (hne : Δ.last ≠ κ) : LeftReduced F T A π := by
  let _ := T.topology
  intro Z hZ hZπ k h σ hsub
  have hπirr : π.IsIrreducible := by
    obtain ⟨_, _, hh⟩ := hπ
    exact hh.1
  obtain ⟨E⟩ := nonempty_equiv_of_isSubquotient_irreducible F T π Z hπirr hZ hZπ
  have hZs : T.IsSegmentHead Δ Z := hπ.of_equiv E
  have hZnt : Nontrivial Z := SegmentSocleDerivativesProof.nontrivial_of_isIrreducible hZ
  have hd : 0 < d := hκ ▸ κ.rank_pos
  apply hne
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨g, hg⟩ := exists_ne_zero_of_isSubrepresentation_rankZero F T h Z A.obj σ hZnt hsub
    obtain ⟨h1, A₀, hA₀, hE⟩ := isSegmentHead_supercuspidal_target F T Δ Z (T.castRank h A.obj)
      hZs (T.isIrreducible_castRank h A.obj A.property.1)
      (SegmentSocleDerivativesProof.isSupercuspidal_castRank T h A.obj A.property.2) g hg
    have hr : Δ.rank = Δ.degree := by
      change Δ.rank = Δ.length * Δ.rank
      rw [h1, Nat.one_mul]
    rw [last_eq_base_of_length_eq_one F T Δ h1]
    exact cuspidalDatum_eq_of_castRank_equiv F T A₀ A hA₀ hκ hA hr h (hE hr)
  · obtain ⟨g, hg⟩ := exists_jacquet_ne_zero_of_isSubrepresentation F T hd hk h Z A.obj σ hZnt hsub
    by_cases hdvd : Δ.rank ∣ k
    · obtain ⟨q, hq⟩ := hdvd
      rw [Nat.mul_comm] at hq
      subst hq
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
      have h' : d + q * Δ.rank = Δ.length * Δ.rank := h
      have hqm : q < Δ.length := by
        apply Nat.lt_of_mul_lt_mul_right (a := Δ.rank)
        omega
      obtain rfl : d = (Δ.length - q) * Δ.rank := by
        rw [Nat.sub_mul]
        omega
      obtain ⟨π₁, π₂, h₁, -, ⟨e⟩⟩ :=
        ((segmentHeadJacquetFormula.{uF, max uF uV} F T) Δ Z hZs).2 q hq0 hqm
      let f : (FiniteTensor.external (H := fun i : Fin 2 =>
            GeneralLinear ((Δ.splitShape q hq0 hqm).size i) F.Carrier)
            (fun i => (Δ.splitFactors q hq0 hqm π₁ π₂ i).representation)).IntertwiningMap
          (FiniteTensor.external (H := fun i : Fin 2 =>
            GeneralLinear ((Δ.splitShape q hq0 hqm).size i) F.Carrier)
            (fun i => (twoBlockFactors hd hk A.obj σ i).representation)) :=
        g.comp (SmoothRep.hom e.inv)
      have hf : f ≠ 0 := by
        intro h0
        apply hg
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        have := congrArg (fun φ => φ (SmoothRep.hom e.hom x)) h0
        simp only [f] at this
        change g (SmoothRep.hom e.inv (SmoothRep.hom e.hom x)) = 0 at this
        have hx := Derivative.LevelCalculus.hom_inv_apply e x
        change g x = 0
        calc g x = g (SmoothRep.hom e.inv (SmoothRep.hom e.hom x)) := congrArg g hx.symm
          _ = 0 := this
      obtain ⟨g', hg'⟩ := exists_firstFactor_ne_zero _ _ f hf
      obtain ⟨h1, A₀, hA₀, hE⟩ := isSegmentHead_supercuspidal_target F T (Δ.terminal q hqm) π₁
        A.obj h₁ A.property.1 A.property.2 g' hg'
      have hr : (Δ.terminal q hqm).rank = (Δ.terminal q hqm).degree := by
        change (Δ.terminal q hqm).rank = (Δ.terminal q hqm).length * (Δ.terminal q hqm).rank
        rw [h1, Nat.one_mul]
      rw [← Δ.terminal_last q hqm, last_eq_base_of_length_eq_one F T _ h1]
      exact cuspidalDatum_eq_of_castRank_equiv F T A₀ A hA₀ hκ hA hr rfl (hE hr)
    · exfalso
      have hln : k < Δ.degree := by omega
      obtain rfl : d = Δ.degree - k := by omega
      have hsub0 := ((segmentHeadJacquetFormula.{uF, max uF uV} F T) Δ Z hZs).1 k hk hln hdvd
      apply hg
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      have hx : x = 0 := @Subsingleton.elim _ hsub0 x 0
      rw [hx, map_zero, map_zero]

end Main

end Langlands.Classification.LeftCuspidalDerivative

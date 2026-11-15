import Langlands.Representation.Classification.MoeglinWaldspurgerProductMoves
import Langlands.Representation.Classification.MoeglinWaldspurgerSocleCut
import Langlands.Representation.Classification.MoeglinWaldspurgerZelevinskyTop
import Langlands.Representation.Classification.SegmentSocleDecreasingHead

/-!
# Adding a segment with the greatest ending to a Zelevinsky label

The field `zsocle` of `DerivativeFacts` for `LDrel`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative Aubert.SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment of a datum with segment socles has a segment socle. -/
theorem exists_segmentSocle_of_mem {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hd : d.HasSegmentSocles) {Δ : T.Segment.{max uF uV, uF}} (hΔ : Δ ∈ d.multisegment) :
    ∃ Z : (letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)), T.IsSegmentSocle Δ Z := by
  have h : Δ ∈ List.ofFn d.segments := Multiset.mem_coe.mp hΔ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact ⟨d.blocks i, hd i⟩

/-- Transport a segment socle along an equality of segments. -/
theorem exists_segmentSocle_of_eq {Δ₁ Δ₂ : T.Segment.{max uF uV, uF}} (h : Δ₁ = Δ₂)
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ₁.degree F.Carrier)}
    (hZ : T.IsSegmentSocle Δ₁ Z) :
    ∃ Z₂ : (letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ₂.degree F.Carrier)),
      T.IsSegmentSocle Δ₂ Z₂ ∧ CastIso T Z Z₂ := by
  subst h
  exact ⟨Z, hZ, CastIso.refl Z⟩

variable (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-- **Labels from a prepended segment.** Let `d₀` be a precedence-ordered datum of segment
socles for `realize ρ x b` and let `J` end at least where every occurrence of `b` ends.
Every irreducible subrepresentation of `Z × d₀.induced`, for a socle `Z` of the realization of
`J`, is a label of `J ::ₘ b`. -/
theorem labelClass_cons {b : Multisegment} {J : Interval} (hJ : ∀ K ∈ b, K.ending ≤ J.ending)
    {n₀ : ℕ} (d₀ : T.SegmentProductDatum.{max uF uV, uF} n₀)
    (hd₀ms : d₀.multisegment = realize ρ x b) (hd₀ord : d₀.IsPrecedenceOrdered)
    (hd₀soc : d₀.HasSegmentSocles)
    {Z : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (J.realize ρ x).degree F.Carrier)}
    (hZ : T.IsSegmentSocle (J.realize ρ x) Z)
    (W : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((J.realize ρ x).degree + n₀) F.Carrier))
    (hW : letI := T.topology; W.IsIrreducible)
    (hWsub : letI := T.topology; SmoothRep.IsSubrepresentation W
      ((T.binaryNormalizedProductFunctor (J.realize ρ x).degree n₀).obj (Z, d₀.induced))) :
    LabelClass F T ρ x (J ::ₘ b) _ (letI := T.topology;
      GeneralLinear.irreducibleIsoClass _ F.Carrier W hW) := by
  let := T.topology
  let d := SegmentProductOrderedAssembly.cons (J.realize ρ x) Z d₀
  obtain ⟨e⟩ := SegmentProductOrderedAssembly.nonempty_cons_iso_binary (J.realize ρ x) Z d₀
  have hWd : SmoothRep.IsSubrepresentation W d.induced := isSubrepresentation_of_iso hWsub e.symm
  refine ⟨W, hW, rfl, d, ?_, ?_, SegmentProductOrderedAssembly.cons_hasSegmentSocles _ _ _ hZ hd₀soc,
    hW, SmoothRep.hom hWd.choose, hWd.choose_spec⟩
  · rw [SegmentProductDatum.multisegment, SegmentProductOrderedAssembly.cons_segments,
      ← Multiset.cons_coe]
    change _ ::ₘ d₀.multisegment = _
    rw [hd₀ms]
    simp [realize]
  · rw [SegmentProductDatum.IsPrecedenceOrdered, isPrecedenceOrdered_iff_list,
      SegmentProductOrderedAssembly.cons_segments, IsPrecedenceOrderedList, List.pairwise_cons]
    refine ⟨?_, (isPrecedenceOrdered_iff_list T _).mp hd₀ord⟩
    intro Γ hΓ hprec
    have hΓ' : Γ ∈ d₀.multisegment := Multiset.mem_coe.mpr hΓ
    rw [hd₀ms] at hΓ'
    obtain ⟨K, hK, rfl⟩ := mem_realize ρ x hΓ'
    have h1 := (realize_precedes_iff F T ρ x J K).mp hprec
    have h2 := hJ K hK
    omega

/-- **Derivative data from an embedding.** If `π` embeds into `A^K × Y` up to rank transport,
where `Y` has finite length, is left reduced, has an irreducible subrepresentation, and all its
irreducible subrepresentations are labels of `β`, then `(K, label of β)` is the derivative
datum of `π`. -/
theorem LDrel_of_embeds (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (c : ℤ) (β : Multisegment)
    {K m' m n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier))
    (hYf : letI := T.topology; Y.HasFiniteLength)
    (hYred : LeftReduced F T (cuspRep F T ρ x c) Y)
    (hex : letI := T.topology; ∃ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)),
      D.IsIrreducible ∧ SmoothRep.IsSubrepresentation D Y)
    (hYlab : letI := T.topology;
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)) (hW : W.IsIrreducible),
        SmoothRep.IsSubrepresentation W Y →
          LabelClass F T ρ x β m' (GeneralLinear.irreducibleIsoClass m' F.Carrier W hW))
    (S : Label.{uF, uV} F T m) (hS : LabelClass F T ρ x β m S)
    (hemb : Embeds T π (iterProd T (cuspRep F T ρ x c).obj K Y)) :
    LDrel F T ρ x c (letI := T.topology; GeneralLinear.irreducibleIsoClass n F.Carrier π hπ) K S := by
  let := T.topology
  obtain ⟨D, hD, hDY⟩ := hex
  have hm' : m' = m := ((hYlab D hD hDY).degree).symm.trans hS.degree
  subst hm'
  have hrank : powerRank ρ.rank K m' = n := hemb.choose.symm
  refine LDrel_of_embedding ρ x hL c hrank π hπ Y hYf hYred S ?_ ⟨D, hD, hDY⟩ ?_
  · intro Z hZ hZY
    exact labelClass_unique F T ρ x (hYlab Z hZ hZY) hS
  · rw [powerProduct_eq_iterProd]
    exact hemb.isSubrepresentation_castRank hrank

theorem segment_eq_mk {Γ : T.Segment.{max uF uV, uF}} {B : T.CuspidalDatum.{max uF uV, uF}}
    {L : ℕ} (hL : 0 < L) (hB : Γ.base = B) (hl : Γ.length = L) : Γ = ⟨B, L, hL⟩ := by
  obtain ⟨b, l, h⟩ := Γ
  simp only at hB hl
  subst hB hl
  rfl

/-- **Adding a segment with the greatest ending** (the field `zsocle`). -/
theorem zsocle_LDrel (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (I : Interval)
    (ν ν' : Multisegment) (hν : ∀ J ∈ ν, J.ending ≤ I.ending)
    (hν' : ∀ J ∈ ν', J.ending ≤ I.ending)
    {n₁ m₁ n m : ℕ} (cls₁ : Label.{uF, uV} F T n₁) (S₁ : Label.{uF, uV} F T m₁)
    (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m) (K : ℕ)
    (h₁ : LabelClass F T ρ x ν n₁ cls₁) (hLD : LDrel F T ρ x I.beginning cls₁ K S₁)
    (hS₁ : LabelClass F T ρ x ν' m₁ S₁) (hcls : LabelClass F T ρ x (I ::ₘ ν) n cls)
    (hS : LabelClass F T ρ x (Interval.dropFirst I + ν') m S) :
    LDrel F T ρ x I.beginning cls (K + 1) S := by
  let := T.topology
  let A := cuspRep F T ρ x I.beginning
  have hr : 0 < ρ.rank := ρ.rank_pos
  obtain ⟨hK, π₁, hπ₁, D₁, hD₁, hπ₁c, hD₁c, hD₁red, hsub₁⟩ := hLD
  have hn₁ := h₁.degree
  have hn := hcls.degree
  subst hK
  have e₁ : Embeds T π₁ (iterProd T A.obj K D₁) := by
    have h := hsub₁
    rw [powerProduct_eq_iterProd] at h
    exact embeds_of_isSubrepresentation h
  obtain ⟨πν, hπν, hπνc, dν, hdνms, hdνord, hdνsoc, -, fν, hfν⟩ := h₁
  obtain ⟨πν', hπν', hπν'c, dν', hdν'ms, hdν'ord, hdν'soc, -, fν', hfν'⟩ := hS₁
  have eπ₁ : π₁ ≅ πν :=
    ((SmoothRep.irreducibleIsoClass_eq_iff hπ₁ hπν).mp (hπ₁c.trans hπνc.symm)).some
  have eD₁ : D₁ ≅ πν' :=
    ((SmoothRep.irreducibleIsoClass_eq_iff hD₁ hπν').mp (hD₁c.trans hπν'c.symm)).some
  have hπ₁dν : SmoothRep.IsSubrepresentation π₁ dν.induced :=
    isSubrepresentation_of_iso_left eπ₁.symm ⟨SmoothRep.ofHom fν, hfν⟩
  have hD₁dν' : SmoothRep.IsSubrepresentation D₁ dν'.induced :=
    isSubrepresentation_of_iso_left eD₁.symm ⟨SmoothRep.ofHom fν', hfν'⟩
  -- a socle of the realization of `I`
  have hclsc := hcls
  obtain ⟨-, -, -, dI, hdIms, -, hdIsoc, -⟩ := hclsc
  obtain ⟨Z, hZ⟩ := exists_segmentSocle_of_mem dI hdIsoc (Δ := I.realize ρ x) (by
    rw [hdIms]; exact Multiset.mem_map_of_mem _ (Multiset.mem_cons_self I ν))
  have hZi : Z.IsIrreducible := Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T hZ
  -- an irreducible subrepresentation of `Z × π₁` is a label of `I + ν`
  have : Nontrivial Z :=
    Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hZi
  have : Nontrivial π₁ :=
    Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hπ₁
  have : Nontrivial ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree
      (powerRank ρ.rank K m₁)).obj (Z, π₁)) := Derivative.ProductVanishing.nontrivial_binary T (Z, π₁)
  have hPf := Aubert.binaryProduct_preservesFiniteLength F T _ _ Z π₁
    (SmoothRep.hasFiniteLength_of_isIrreducible hZi) (SmoothRep.hasFiniteLength_of_isIrreducible hπ₁)
  obtain ⟨π, hπ, f, hf⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hPf
  have hπP : Embeds T π ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree
      (powerRank ρ.rank K m₁)).obj (Z, π₁)) := embeds_of_isSubrepresentation ⟨f, hf⟩
  have hπZdν : SmoothRep.IsSubrepresentation π
      ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree (powerRank ρ.rank K m₁)).obj
        (Z, dν.induced)) :=
    (hπP.trans ((CastIso.refl Z).embeds.binary
      (embeds_of_isSubrepresentation hπ₁dν))).isSubrepresentation_castRank rfl
  have hlab := labelClass_cons ρ x hν dν hdνms hdνord hdνsoc hZ π hπ hπZdν
  have hN : (I.realize ρ x).degree + powerRank ρ.rank K m₁ = n := by
    rw [← hn, ← hn₁, weight_cons, Nat.add_mul]
    rfl
  subst hN
  have hclsπ := labelClass_unique F T ρ x hlab hcls
  rw [← hclsπ]
  -- commuting the cuspidal factors past `Z`
  have hun : ¬ (I.realize ρ x).IsLinked (pointSegment ρ x I.beginning) := by
    rw [pointSegment_eq, realize_isLinked_iff F T]
    simp only [point]
    omega
  have sw := castIso_swap_of_unlinked hZ (pointBlock_isSegmentSocle ρ x I.beginning) hun
  have pb : CastIso T (pointBlock F ρ x I.beginning) A.obj :=
    (castIso_castRank (pointSegment_degree ρ x I.beginning).symm A.obj).symm
  have hswap : CastIso T
      ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree ρ.rank).obj (Z, A.obj))
      ((T.binaryNormalizedProductFunctor ρ.rank (I.realize ρ x).degree).obj (A.obj, Z)) :=
    ((CastIso.refl Z).binary pb.symm).trans (sw.trans (pb.binary (CastIso.refl Z)))
  have hD₁cond : 0 < m₁ ∨ (m₁ = 0 ∧ D₁.IsIrreducible) := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · exact Or.inr ⟨h, hD₁⟩
    · exact Or.inl h
  have E2 : Embeds T π (iterProd T A.obj K
      ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree m₁).obj (Z, D₁))) :=
    (hπP.trans ((CastIso.refl Z).embeds.binary e₁)).castIso_right
      (castIso_commute hr (Segment.degree_pos _) A.obj Z hswap K D₁ hD₁cond)
  by_cases hce : I.beginning < I.ending
  · -- the cut case: `Z ↪ A × Z₀` with `Z₀` a socle of `[c+1, e]`
    let J' : Interval := ⟨I.beginning + 1, I.ending, by omega⟩
    have hdrop : Interval.dropFirst I = {J'} := by
      simp only [Interval.dropFirst, hce, ↓reduceDIte]
      rfl
    rw [hdrop] at hS
    have hSc := hS
    obtain ⟨-, -, -, dS, hdSms, -, hdSsoc, -⟩ := hSc
    obtain ⟨Z₀, hZ₀⟩ := exists_segmentSocle_of_mem dS hdSsoc (Δ := J'.realize ρ x) (by
      rw [hdSms]
      exact Multiset.mem_map_of_mem _ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self J'))))
    have hIlen : ((I.ending - I.beginning).toNat : ℤ) = I.ending - I.beginning :=
      Int.toNat_of_nonneg (by omega)
    have hJlen : ((I.ending - (I.beginning + 1)).toNat : ℤ) = I.ending - (I.beginning + 1) :=
      Int.toNat_of_nonneg (by omega)
    obtain ⟨k, hk⟩ : ∃ k, (I.realize ρ x).length = k + 2 :=
      ⟨(I.realize ρ x).length - 2, by
        rw [Interval.realize_length]; unfold Interval.length; omega⟩
    have hseg : J'.realize ρ x =
        ⟨(I.realize ρ x).base.twist ((1 : ℕ) : ℝ), k + 1, Nat.succ_pos k⟩ := by
      apply segment_eq_mk
      · rw [Interval.realize_base, Interval.realize_base, CuspidalDatum.twist_twist]
        congr 1
        show x + ((I.beginning + 1 : ℤ) : ℝ) = _
        push_cast
        ring
      · rw [Interval.realize_length] at hk ⊢
        unfold Interval.length at hk ⊢
        show (I.ending - (I.beginning + 1)).toNat + 1 = k + 1
        omega
    obtain ⟨Z', hZ', hZ₀Z'⟩ := exists_segmentSocle_of_eq hseg hZ₀
    have hcut := socleCut_embeds hk A (cuspRep_represents F T ρ x I.beginning) hZ hZ'
    have hZ'pos : 0 < (k + 1) * ρ.rank := Nat.mul_pos (Nat.succ_pos k) hr
    have s1 := E2.trans (Embeds.iterProd A.obj K (hcut.binary (CastIso.refl D₁).embeds))
    have s2 := castIso_assoc' hr hZ'pos A.obj Z' D₁ hD₁cond
    have s3 := (CastIso.refl A.obj).binary (hZ₀Z'.symm.binary (CastIso.refl D₁))
    have s4 := castIso_iterProd_shift A.obj K
      ((T.binaryNormalizedProductFunctor (J'.realize ρ x).degree m₁).obj (Z₀, D₁))
    have E3 := s1.castIso_right ((CastIso.iterProd A.obj K (s2.trans s3)).trans s4)
    -- the second factor
    have hZ₀i : Z₀.IsIrreducible :=
      Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T hZ₀
    have hYf := Aubert.binaryProduct_preservesFiniteLength F T _ _ Z₀ D₁
      (SmoothRep.hasFiniteLength_of_isIrreducible hZ₀i) (SmoothRep.hasFiniteLength_of_isIrreducible hD₁)
    obtain ⟨-, hprod, -, -, -⟩ := hL p F T ρ.rank A
    have hZ₀red := socle_leftReduced ρ x hL I.beginning J' (by simp [J']) Z₀ hZ₀
    have hYred := hprod _ _ Z₀ D₁ (SmoothRep.hasFiniteLength_of_isIrreducible hZ₀i)
      (SmoothRep.hasFiniteLength_of_isIrreducible hD₁) hZ₀red hD₁red
    have : Nontrivial Z₀ :=
      Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hZ₀i
    have : Nontrivial D₁ :=
      Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hD₁
    have : Nontrivial ((T.binaryNormalizedProductFunctor (J'.realize ρ x).degree m₁).obj
      (Z₀, D₁)) := Derivative.ProductVanishing.nontrivial_binary T (Z₀, D₁)
    obtain ⟨W₀, hW₀, g₀, hg₀⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hYf
    have hYsub : Embeds T ((T.binaryNormalizedProductFunctor (J'.realize ρ x).degree m₁).obj
        (Z₀, D₁)) ((T.binaryNormalizedProductFunctor (J'.realize ρ x).degree m₁).obj
          (Z₀, dν'.induced)) :=
      (CastIso.refl Z₀).embeds.binary (embeds_of_isSubrepresentation hD₁dν')
    refine LDrel_of_embeds ρ x hL I.beginning ({J'} + ν') π hπ _ hYf hYred ⟨W₀, hW₀, g₀, hg₀⟩
      ?_ S hS E3
    intro W hW hWY
    have hWs := ((embeds_of_isSubrepresentation hWY).trans hYsub).isSubrepresentation_castRank rfl
    have hlab' := labelClass_cons ρ x (J := J') (b := ν') hν' dν' hdν'ms hdν'ord hdν'soc hZ₀ W hW hWs
    rw [Multiset.singleton_add]
    exact hlab'
  · -- the point case: `Z ≅ A`
    have hIe : I = point I.beginning :=
      Interval.ext rfl (by have := I.nonempty; simp only [point]; omega)
    have hdrop : Interval.dropFirst I = 0 := by
      simp only [Interval.dropFirst, hce, ↓reduceDIte]
    rw [hdrop, zero_add] at hS
    have hseg : I.realize ρ x = pointSegment ρ x I.beginning := by
      rw [pointSegment_eq]
      conv_lhs => rw [hIe]
    obtain ⟨Z₂, hZ₂, hZZ₂⟩ := exists_segmentSocle_of_eq hseg hZ
    obtain ⟨e⟩ := IsSegmentSocle.nonempty_equiv hZ₂ (pointBlock_isSegmentSocle ρ x I.beginning)
    have hZA : CastIso T Z A.obj := hZZ₂.trans ((castIso_of_iso (SmoothRep.mkIso e)).trans pb)
    have E3 := E2.castIso_right ((CastIso.iterProd A.obj K (hZA.binary (CastIso.refl D₁))).trans
      (castIso_iterProd_shift A.obj K D₁))
    refine LDrel_of_embeds ρ x hL I.beginning ν' π hπ D₁
      (SmoothRep.hasFiniteLength_of_isIrreducible hD₁) hD₁red
      ⟨D₁, hD₁, isSubrepresentation_refl D₁⟩ ?_ S hS E3
    intro W hW hWD
    obtain ⟨g, hg⟩ := isSubrepresentation_trans hWD hD₁dν'
    exact ⟨W, hW, rfl, dν', hdν'ms, hdν'ord, hdν'soc, hW, SmoothRep.hom g, hg⟩

end Langlands.MoeglinWaldspurger.Derivation

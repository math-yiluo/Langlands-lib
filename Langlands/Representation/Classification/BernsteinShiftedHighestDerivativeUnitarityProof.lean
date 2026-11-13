import Langlands.Representation.Classification.BernsteinShiftedHighestDerivativeUnitarizabilityProof
import Langlands.Representation.Aubert.ZelevinskyHighestDerivative
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleExistenceProof
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof

/-!
# Irreducibility and unitarizability of the shifted highest derivative

Bernstein 1984, §7.4 (Tadic 1986, Theorem 2.5(iii)). For an irreducible representation `π` of `GL_N` whose shifted highest derivative
`ν^(1/2) π^(h)` is unitarizable, the highest derivative `π^(h)` is irreducible. The
Zelevinsky realization `π ⊂ ⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` embeds `π^(h)` into a product with an
irreducible socle, and unitarizability with admissibility makes `π^(h)` semisimple.
Hence the unitarizability half of `BernsteinShiftedHighestDerivativeUnitarity`
(`bernsteinShiftedHighestDerivativeUnitarizability`) implies the whole statement.
See the paired Markdown.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.ShiftedHighestDerivative

open GeneralLinear HarmonicAnalysis Derivative PadicField.TopologicalData

universe uF uV uG uW

section Socle

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A nonzero finite-length representation with a complemented subrepresentation
lattice that embeds in a representation with an irreducible socle is irreducible. -/
theorem isIrreducible_of_complemented_of_isIrreducibleSocle
    {A Y : SmoothRep.{0, uG, uW} ℂ G} [Nontrivial A] (hA : A.HasFiniteLength)
    (hc : ComplementedLattice (Subrepresentation A.representation))
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {π₀ : Representation ℂ G W}
    (hY : IsIrreducibleSocle Y.representation π₀)
    (ι : A ⟶ Y) (hι : Function.Injective (SmoothRep.hom ι)) :
    A.representation.IsIrreducible := by
  have : IsArtinian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).2
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.representation)
  have : IsAtomic (Subrepresentation A.representation) := e.isAtomic_iff.mpr inferInstance
  have hbt : (⊥ : Subrepresentation A.representation) ≠ ⊤ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    intro hb
    apply hv
    have hmem : v ∈ (⊤ : Subrepresentation A.representation).toSubmodule := Submodule.mem_top
    rw [← hb] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨-, j, -, hj⟩ := hY
  -- Two atoms have the same image in `Y`, hence coincide.
  have key : ∀ U₁ U₂ : Subrepresentation A.representation, IsAtom U₁ → IsAtom U₂ →
      U₁ ≤ U₂ := by
    intro U₁ U₂ h₁ h₂ x hx
    have r₁ := hj _ _ (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom U₁ h₁)
      (SmoothRep.hom (SmoothRep.subtype A U₁ ≫ ι)) (hι.comp (SmoothRep.subtype_injective A U₁))
    have r₂ := hj _ _ (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom U₂ h₂)
      (SmoothRep.hom (SmoothRep.subtype A U₂ ≫ ι)) (hι.comp (SmoothRep.subtype_injective A U₂))
    have hmem₁ : SmoothRep.hom ι x ∈
        (SmoothRep.hom (SmoothRep.subtype A U₁ ≫ ι)).toLinearMap.range := ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, hy⟩ := (SetLike.ext_iff.mp (r₁.trans r₂.symm) (SmoothRep.hom ι x)).mp hmem₁
    change SmoothRep.hom ι y.1 = SmoothRep.hom ι x at hy
    rw [← hι hy]
    exact y.2
  have hsimple : ∀ S : Subrepresentation A.representation, S = ⊥ ∨ S = ⊤ := by
    intro S
    obtain ⟨C, hC⟩ := exists_isCompl S
    by_cases hS : S = ⊥
    · exact Or.inl hS
    by_cases hC0 : C = ⊥
    · right
      have := hC.sup_eq_top
      rwa [hC0, sup_bot_eq] at this
    obtain ⟨U₁, h₁, hU₁⟩ := (eq_bot_or_exists_atom_le S).resolve_left hS
    obtain ⟨U₂, h₂, hU₂⟩ := (eq_bot_or_exists_atom_le C).resolve_left hC0
    have hle : U₁ ≤ S ⊓ C := le_inf hU₁ ((key U₁ U₂ h₁ h₂).trans hU₂)
    rw [hC.inf_eq_bot] at hle
    exact absurd (le_bot_iff.mp hle) h₁.1
  exact { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := hsimple }

end Socle

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A finite-length representation of `GL_r` whose `ν^(1/2)`-twist is unitarizable has a
complemented subrepresentation lattice. -/
theorem complementedLattice_of_isUnitarizable_segmentFactor {r : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier), A.HasFiniteLength →
      IsUnitarizable (T.segmentFactor A (1 / 2)).representation →
      ComplementedLattice (Subrepresentation A.representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  intro A hA hu
  have hadm : A.IsAdmissible :=
    SmoothRep.isAdmissible_of_finiteLength_of_irreducible
      (fun B hB => (CuspidalSupport.cuspidalEmbedding.{uF, uW} F T r B hB).1) A hA
  have hadm' : IsAdmissible (T.segmentFactor A (1 / 2)).representation :=
    (isAdmissible_twist_iff (T.determinantPowerCharacter r (1 / 2)) A.representation
      (T.isOpen_ker_determinantPowerCharacter r (1 / 2))).mpr hadm
  have hcofinal : ∀ H : OpenSubgroup (GeneralLinear r F.Carrier),
      ∃ K : OpenSubgroup (GeneralLinear r F.Carrier),
        IsCompact (K : Set (GeneralLinear r F.Carrier)) ∧ K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ := T.generalLinearCompactOpen r
      (H : Set _) (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, hKH⟩
  have hsem : Representation.IsSemisimpleRepresentation
      (T.segmentFactor A (1 / 2)).representation :=
    admissibleUnitarySemisimplicity _ hcofinal _ _ hadm' hu
  exact (twistSubrepresentationOrderIso (T.determinantPowerCharacter r (1 / 2))
    A.representation).complementedLattice_iff.mpr hsem

/-- The highest derivative of an irreducible `π` of `GL_N` is irreducible when its
`ν^(1/2)`-twist is unitarizable. -/
theorem isIrreducible_highestDerivative {N : ℕ} (hN : 0 < N)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (hπ : letI := T.topology; Representation.IsIrreducible π.representation)
    (hd : letI := T.topology; GeneralLinearHighestDerivativeOrderData T ψ π)
    (hu : letI := T.topology
      IsUnitarizable (T.segmentFactor
        ((generalLinearDerivative T ψ N hd.order hd.le_rank).obj π) (1 / 2)).representation) :
    letI := T.topology
    Representation.IsIrreducible
      ((generalLinearDerivative T ψ N hd.order hd.le_rank).obj π).representation := by
  let := T.topology
  obtain ⟨-, -, d, -, ho, hs, hsoc⟩ := multisegmentSocleExhaustion.{uF, uV} F T N π hπ
  obtain ⟨-, j, hj, -⟩ := hsoc
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hk : ∑ i, (d.segments i).rank ≤ M + 1 :=
    Aubert.ZelevinskyHighestDerivative.sum_rank_le F T d
  have hkpos : 0 < ∑ i, (d.segments i).rank :=
    Aubert.ZelevinskyHighestDerivative.sum_rank_pos F T hN d
  have hk' : 0 < ∑ i, (d.segments i).rank ∧ ∑ i, (d.segments i).rank ≤ M + 1 :=
    ⟨hkpos, hk⟩
  -- The highest derivative of the product (Ze80 6.6 for the product itself).
  obtain ⟨hvan, ⟨d', hlist, hs', ⟨e⟩⟩, -⟩ :=
    segmentSocleProductHighestDerivative.{uF, max uF uV} F T ψ (M + 1) d hs _ hk rfl
  have hlist' : List.ofFn d'.segments = Segment.dropLastList (List.ofFn d.segments) :=
    hlist.trans (Segment.filterMap_eq_dropLastList _)
  -- Homogeneity of the restricted product (Ze80 Thm 6.2).
  have hsep := precedenceOrdered_endpointSeparated.{uF, max uF uV} F T
    (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T) d.segments ho
  have hhom : IsHomogeneous T ψ ((generalLinearRestriction T M).obj d.induced) :=
    (isGeneralLinearHomogeneous_iff T ψ d.induced).mp
      (segmentSocleProductHomogeneity.{uF, max uF uV} F T ψ M d hs hsep)
  have hlevX : level T ψ ((generalLinearRestriction T M).obj d.induced) =
      ∑ i, (d.segments i).rank := by
    rw [level_eq_iff T ψ hkpos]
    refine ⟨hk, ?_, ?_⟩
    · rw [Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ hk',
        LevelCalculus.nontrivial_iff_of_iso e]
      exact segmentSocleProduct_nontrivial F T d' hs'
    · intro m hkm hm hnz
      rw [Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ
        ⟨by omega, hm⟩] at hnz
      exact (not_nontrivial_iff_subsingleton.mpr (hvan m hm hkm)) hnz
  -- The level of `π` is `λ`.
  let jS : π ⟶ d.induced := SmoothRep.ofHom j
  have hjS : Function.Injective (SmoothRep.hom jS) := hj
  have hjR : Function.Injective (SmoothRep.hom ((generalLinearRestriction T M).map jS)) :=
    LevelCalculus.map_injective_of_exact (generalLinearRestriction_mapsShortExact F T M) jS hjS
  have hπnt : Nontrivial π := SegmentHeadSupport.nontrivial_of_isIrreducible hπ
  have hπR : Nontrivial ((generalLinearRestriction T M).obj π) := hπnt
  have hlev := LevelCalculus.level_eq_of_isHomogeneous T ψ hhom _ hjR hπR
  have hπk := ((level_eq_iff T ψ hkpos _).mp (hlev.trans hlevX)).2.1
  rw [Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ hk'] at hπk
  -- The order of `hd` is `λ`.
  have hord : hd.order = ∑ i, (d.segments i).rank := by
    rcases lt_trichotomy hd.order (∑ i, (d.segments i).rank) with hlt | heq | hgt
    · exact absurd (hd.higher_vanish _ hk hlt) (not_subsingleton_iff_nontrivial.mpr hπk)
    · exact heq
    · have hDm : Function.Injective (SmoothRep.hom
          ((generalLinearDerivative.{uF, max uF uV} T ψ (M + 1) hd.order hd.le_rank).map jS)) :=
        LevelCalculus.map_injective_of_exact
          (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (M + 1) _ hd.le_rank) jS hjS
      have := hvan hd.order hd.le_rank hgt
      exact absurd hDm.subsingleton (not_subsingleton_iff_nontrivial.mpr hd.nonzero)
  revert hu
  suffices H : ∀ (o : ℕ) (hoN : o ≤ M + 1), o = ∑ i, (d.segments i).rank →
      IsUnitarizable (T.segmentFactor
        ((generalLinearDerivative T ψ (M + 1) o hoN).obj π) (1 / 2)).representation →
      Representation.IsIrreducible
        ((generalLinearDerivative T ψ (M + 1) o hoN).obj π).representation from
    H hd.order hd.le_rank hord
  intro o hoN hoeq hu
  subst hoeq
  -- The order-`λ` derivative of `π` embeds into the product of the `⟨Δ_i⁻⟩`.
  let D := generalLinearDerivative.{uF, max uF uV} T ψ (M + 1) (∑ i, (d.segments i).rank) hk
  have hDj : Function.Injective (SmoothRep.hom (D.map jS)) :=
    LevelCalculus.map_injective_of_exact
      (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (M + 1) _ hk) jS hjS
  have hDe : Function.Injective (SmoothRep.hom (D.map jS ≫ e.hom)) :=
    (LevelCalculus.iso_hom_injective e).comp hDj
  have hFL : (D.obj π).HasFiniteLength :=
    Aubert.ZelevinskyHighestDerivative.hasFiniteLength_of_injective (D.map jS ≫ e.hom) hDe
      (Aubert.SegmentProductClass.hasFiniteLength_induced F T d' hs')
  have ho' : d'.IsPrecedenceOrdered := by
    have h₁ := (segmentInitialTruncationOrder.{uF, max uF uV} F T
      (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T)).2 _
      ((T.isPrecedenceOrdered_iff_list d.segments).mp ho)
    rw [← hlist'] at h₁
    exact (T.isPrecedenceOrdered_iff_list d'.segments).mpr h₁
  obtain ⟨π₀, -, -, hπ₀⟩ :=
    orderedMultisegmentSocleExistence.{uF, uV} F T _ d' ho' hs'
  have : Nontrivial (D.obj π) := hπk
  exact isIrreducible_of_complemented_of_isIrreducibleSocle hFL
    (complementedLattice_of_isUnitarizable_segmentFactor F T (D.obj π) hFL hu)
    hπ₀ (D.map jS ≫ e.hom) hDe

end Langlands.Classification.ShiftedHighestDerivative

namespace Langlands.Classification

universe uF uV

/-- The unitarizability half of Bernstein's shifted highest-derivative theorem implies
the whole theorem: unitarizability of `ν^(1/2) π^(h)` forces irreducibility of `π^(h)`. -/
theorem bernsteinShiftedHighestDerivativeUnitarity_of_unitarizability {p : ℕ}
    [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hunit : BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T) :
    BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T := by
  let := T.topology
  intro N hN ψ π hirrπ hπ hd
  have hu := hunit N hN ψ π hirrπ hπ hd
  exact ⟨(isIrreducible_twist_iff _ _).mpr
      (ShiftedHighestDerivative.isIrreducible_highestDerivative F T hN ψ π hirrπ hd hu),
    hu⟩

/-- Bernstein 1984, §7.4 (Tadic 1986, Theorem 2.5(iii)): for an irreducible unitarizable
`π` of `GL_N`, `N ≥ 1`, the shifted highest derivative `ν^(1/2) π^(h)` is irreducible and
unitarizable. -/
theorem bernsteinShiftedHighestDerivativeUnitarity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T :=
  bernsteinShiftedHighestDerivativeUnitarity_of_unitarizability F T
    (bernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T)

end Langlands.Classification

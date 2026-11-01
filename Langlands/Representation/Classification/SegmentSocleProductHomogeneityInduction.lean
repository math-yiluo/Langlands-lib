import Langlands.Representation.Derivative.RestrictedProductLevel
import Langlands.Representation.Derivative.RestrictionBridge
import Langlands.Representation.Classification.SegmentProductSplit
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityStatement
import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Classification.SegmentCuspidalContent

/-!
# The induction on the number of segments

Zelevinsky's proof of Theorem 6.2 (6.3) is an induction on the number of
segments. One segment: the restriction of `⟨Δ⟩` has a single nonzero
derivative order (Ze80 3.5), so it is homogeneous. Several segments: split
off the first segment, `π = ⟨Δ_1⟩ × π°`, and apply the restricted-product
step with the homogeneity of `π°|P` (induction) and of the left mixed product
(Ze80 5.3, the hypothesis `hH`). The second case of 6.3 is an explicit
hypothesis here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentSocleProductHomogeneityInduction

open GeneralLinear PadicField.TopologicalData Derivative HarmonicAnalysis
open LevelCalculus MirabolicProductRestriction SegmentProductSplit

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

section Bridges

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- If a representation of `GL_a` has nonzero positive-order derivatives only
in order `c`, the restriction of any isomorphic transport has nonzero
derivatives only in order `c`. -/
theorem single_order_of_iso {a N : ℕ} (c : ℕ) (h : a = N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier)),
      (X ≅ (generalLinearRankCast T h).obj A) →
      (∀ (k : ℕ) (hk : k ≤ a), 0 < k → k ≠ c →
        Subsingleton ((generalLinearDerivative T ψ a k hk).obj A)) →
      ∀ j, HasNonzeroDerivative T ψ ((generalLinearRestriction T N).obj X) j → j = c := by
  let _ := T.topology
  subst h
  rintro A X e hA j ⟨hj, hnt⟩
  have h1 : Nontrivial ((generalLinearDerivative T ψ (N + 1) j hj.2).obj X) :=
    (RestrictionBridge.nontrivial_generalLinearDerivative_iff T ψ rfl hj.2 hj.1 X).mpr ⟨hj, hnt⟩
  have h2 : Nontrivial ((generalLinearDerivative T ψ (N + 1) j hj.2).obj A) :=
    (nontrivial_iff_of_iso ((generalLinearDerivative T ψ (N + 1) j hj.2).mapIso e)).mp h1
  by_contra hjc
  exact not_subsingleton _ (hA j hj.2 hj.1 hjc)

/-- Homogeneity of the restricted binary product gives homogeneity of any
isomorphic `GL` representation. -/
theorem isGeneralLinearHomogeneous_of_restrictedProduct {a b M N m n : ℕ}
    (ha : a = m + 1) (hb : b = n + 1) (e : a + b = M) (hM : M = N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
      (X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)),
      (X ≅ (generalLinearRankCast T e).obj ((T.binaryNormalizedProductFunctor a b).obj (A, B))) →
      IsHomogeneous T ψ ((restrictedProduct T m n).obj
        ((generalLinearRankCast T ha).obj A, (generalLinearRankCast T hb).obj B)) →
      IsGeneralLinearHomogeneous T ψ ((generalLinearRankCast T hM).obj X) := by
  let _ := T.topology
  subst ha hb hM
  obtain rfl : N = m + n + 1 := by omega
  intro A B X i hH
  exact isHomogeneous_of_iso T ψ ((generalLinearRestriction T (m + n + 1)).mapIso i.symm) hH

end Bridges

section Data

variable {T : F.TopologicalData}

/-- A one-segment product is its block, after the rank transport. -/
theorem nonempty_iso_single {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = 1) (hdeg : (d.segments ⟨0, by omega⟩).degree = n) :
    letI := T.topology
    Nonempty (d.induced ≅ (generalLinearRankCast T hdeg).obj (d.blocks ⟨0, by omega⟩)) := by
  let _ := T.topology
  obtain ⟨l, s, hs, b⟩ := d
  change l = 1 at h
  subst h
  change (s 0).degree = n at hdeg
  subst hdeg
  let e : SegmentProductDatum.{uV, uF} T (s 0).degree := ⟨1, s, hs, b⟩
  let E := T.singleBlockNormalizedProductEquiv e.shape rfl
    (fun i => (e.blocks i).representation) (fun i => (e.blocks i).isSmooth)
    ⟨0, by change 0 < 1; omega⟩
  refine ⟨SmoothRep.mkIso (E.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ (b 0)) ?_))⟩
  intro g
  have hg : (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (e.shape.singleBlock_size rfl ⟨0, by change 0 < 1; omega⟩))).symm g = g := by
    apply Units.ext
    ext a b
    rfl
  change (b 0).representation ((GeneralLinear.reindex (R := F.Carrier)
    (finCongr (e.shape.singleBlock_size rfl ⟨0, by change 0 < 1; omega⟩))).symm g) = (b 0).representation g
  rw [hg]

/-- The endpoint condition passes to the tail. -/
theorem tail_endpoint {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (h : d.length = k + 2)
    (hsep : ∀ i j : Fin d.length, i < j →
      (d.segments j).base ≠ ((d.segments i).last).twist 1) :
    ∀ i j : Fin (tail d h).length, i < j →
      ((tail d h).segments j).base ≠ (((tail d h).segments i).last).twist 1 := by
  intro i j hij
  apply hsep
  change (i.succ : ℕ) < (j.succ : ℕ)
  simpa using hij

/-- The endpoint condition between the first segment and the tail. -/
theorem head_endpoint {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (h : d.length = k + 2)
    (hsep : ∀ i j : Fin d.length, i < j →
      (d.segments j).base ≠ ((d.segments i).last).twist 1) :
    ∀ Δ ∈ List.ofFn (tail d h).segments,
      Δ.base ≠ ((d.segments (d.shape.headIndex h)).last).twist 1 := by
  intro Δ hΔ
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hΔ
  apply hsep
  change 0 < (j.succ : ℕ)
  simp

/-- The segment list is the first segment followed by the tail. -/
theorem ofFn_segments_eq_cons {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = k + 2) :
    List.ofFn d.segments =
      d.segments (d.shape.headIndex h) :: List.ofFn (tail d h).segments := by
  rw [List.ofFn_congr h, List.ofFn_succ]
  rfl

theorem cuspidalContent_eq {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    d.multisegment.cuspidalContent =
      ((List.ofFn d.segments).map Segment.cuspidalContent).sum := by
  simp [SegmentProductDatum.multisegment, Multisegment.cuspidalContent]

end Data

section Induction

variable (T : F.TopologicalData)

/-- The second case of Ze80 6.3, for a datum split at its first segment:
no nonzero representation injects both into the restricted product and into
its quotient `⟨Δ_1⟩ × (π°|P)`. -/
def CaseTwoExclusion
    {M k : ℕ} (d : SegmentProductDatum.{uV, uF} T M) (h : d.length = k + 2) (m n : ℕ)
    (ha : d.shape.headRank h = m + 1) (hb : d.shape.tailRank h = n + 1) : Prop :=
  letI := T.topology
  ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
    (f : W ⟶ (restrictedProduct T m n).obj
      ((generalLinearRankCast T ha).obj (d.blocks (d.shape.headIndex h)),
        (generalLinearRankCast T hb).obj (tail d h).induced))
    (g : W ⟶ (restrictionQuotient T m n).obj
      ((generalLinearRankCast T ha).obj (d.blocks (d.shape.headIndex h)),
        (generalLinearRankCast T hb).obj (tail d h).induced)),
    Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
      Nontrivial W → False

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
  (hD : RightMixedProductPhiMinusDetection.{uF, max uF uV} F T)
  (hS : MirabolicProductMinus.RightPhiShortExact.{uF, max uF uV} F T)
  (hB : MirabolicProductMinus.RightPhiBoundary.{uF, max uF uV} F T)
  (hR : MirabolicProductRestrictionStatement.{uF, max uF uV} F T)
  (hLD : LeftMixedProductDerivative.{uF, max uF uV} F T)
  (hH : letI := T.topology
    ∀ (k r : ℕ) (ρ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic r F.Carrier)),
      IsHomogeneous T ψ τ → IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)))
  (h35 : SegmentSocleDerivatives.{uF, uV} F T)
include hE hD hS hB hR hLD hH h35

/-- Ze80 6.2 by induction on the number of segments, with the second case of
6.3 as a hypothesis on every split datum whose tail is homogeneous. -/
theorem homogeneous_of_caseTwo
    (hC2 : ∀ {M k : ℕ} (d : SegmentProductDatum.{uV, uF} T M) (h : d.length = k + 2)
      (m n : ℕ) (ha : d.shape.headRank h = m + 1) (hb : d.shape.tailRank h = n + 1),
      d.HasSegmentSocles →
      (∀ i j : Fin d.length, i < j →
        (d.segments j).base ≠ ((d.segments i).last).twist 1) →
      IsGeneralLinearHomogeneous T ψ ((generalLinearRankCast T hb).obj (tail d h).induced) →
      CaseTwoExclusion T d h m n ha hb) :
    ∀ (ℓ M : ℕ) (d : SegmentProductDatum.{uV, uF} T M) (N : ℕ) (hM : M = N + 1),
      d.length = ℓ + 1 → d.HasSegmentSocles →
      (∀ i j : Fin d.length, i < j →
        (d.segments j).base ≠ ((d.segments i).last).twist 1) →
      IsGeneralLinearHomogeneous T ψ ((generalLinearRankCast T hM).obj d.induced) := by
  let _ := T.topology
  intro ℓ
  induction ℓ with
  | zero =>
    intro M d N hM hl hd _
    have h0 : 0 < d.length := by omega
    have hdeg : (d.segments ⟨0, h0⟩).degree = M := by
      have := d.degree_sum
      rw [Fintype.sum_eq_single ⟨0, h0⟩ (fun i hi => absurd (Fin.ext (by omega)) hi)] at this
      exact this
    obtain ⟨e⟩ := nonempty_iso_single d hl hdeg
    subst hM
    apply RestrictionBridge.isHomogeneous_of_single_order T ψ hE
      (d.segments ⟨0, h0⟩).rank
    exact single_order_of_iso T ψ _ hdeg _ _ e
      (fun k hk hpos hne => (h35 ψ _ _ (hd ⟨0, h0⟩)).1 k hk hpos hne)
  | succ ℓ ih =>
    intro M d N hM hl hd hsep
    obtain ⟨m, ha⟩ : ∃ m, d.shape.headRank hl = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (d.shape.headRank_pos hl)).symm⟩
    obtain ⟨n, hb⟩ : ∃ n, d.shape.tailRank hl = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (d.shape.tailRank_pos hl)).symm⟩
    obtain ⟨e⟩ := nonempty_iso_binary d hl
    have hP : IsGeneralLinearHomogeneous T ψ
        ((generalLinearRankCast T hb).obj (tail d hl).induced) :=
      ih _ (tail d hl) n hb rfl (tail_hasSegmentSocles d hl hd) (tail_endpoint d hl hsep)
    let Δ := d.segments (d.shape.headIndex hl)
    have hrank : Δ.rank ≤ m + 1 := by
      rw [← ha]
      exact Nat.le_mul_of_pos_left _ Δ.length_pos
    have hm : m = (m + 1 - Δ.rank) + (Δ.rank - 1) := by
      have := Δ.rank_pos
      omega
    apply isGeneralLinearHomogeneous_of_restrictedProduct T ψ ha hb _ hM _ _ _ e
    refine RestrictedProductLevel.isHomogeneous_restrictedProduct T ψ hE hD hS hB hR hLD
      m n (m + 1 - Δ.rank) (Δ.rank - 1) hm _ _ ?_
      (hH _ _ _ _ hP) (hC2 d hl m n ha hb hd hsep hP)
    intro j hj
    have := single_order_of_iso T ψ Δ.rank ha _ _ (Iso.refl _)
      (fun k hk hpos hne => (h35 ψ _ _ (hd _)).1 k hk hpos hne) j hj
    have := Δ.rank_pos
    omega

end Induction

end Langlands.Classification.SegmentSocleProductHomogeneityInduction

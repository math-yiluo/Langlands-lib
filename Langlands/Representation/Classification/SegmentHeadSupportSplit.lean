import Langlands.Representation.Classification.SegmentHeadSupportCons

/-!
# Splitting a segment induction into its first factor and its tail

The increasing induction `ρ × νρ × ⋯ × ν^(m-1) ρ` is isomorphic, after a rank
cast, to the binary product of its first factor `ρ` with the increasing induction
of `νρ, …, ν^(m-1) ρ`, and the decreasing induction
`ν^(m-1) ρ × ⋯ × ρ` to the binary product of `ν^(m-1) ρ` with the decreasing
induction of length `m - 1`. The module also twists supercuspidal
representatives by real powers of the determinant norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentHeadSupport

open GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section RankCast

/-- Two successive rank casts are one rank cast. -/
theorem rankCast_rankCast_obj {a b c : ℕ} (h : a = b) (h' : b = c)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    (generalLinearRankCast T h').obj ((generalLinearRankCast T h).obj X) =
      (generalLinearRankCast T (h.trans h')).obj X := by
  subst h h'
  rfl

/-- A rank cast of the second factor of a binary product is a rank cast of the
product. -/
theorem binary_rankCast_right_obj {a b c : ℕ} (h : b = c)
    (L : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    (T.binaryNormalizedProductFunctor a c).obj (L, (generalLinearRankCast T h).obj Y) =
      (generalLinearRankCast T (congrArg (a + ·) h)).obj
        ((T.binaryNormalizedProductFunctor a b).obj (L, Y)) := by
  subst h
  rfl

/-- Equal factors give equal binary products. -/
theorem binary_obj_congr {a b : ℕ}
    {L L' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    {Y Y' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (hL : L = L') (hY : Y = Y') :
    (T.binaryNormalizedProductFunctor a b).obj (L, Y) =
      (T.binaryNormalizedProductFunctor a b).obj (L', Y') := by
  subst hL hY
  rfl

end RankCast

section Twist

/-- Twists by equal characters are isomorphic. -/
def twistIsoOfEq {G : Type*} [Group G] [TopologicalSpace G] {χ η : G →* ℂˣ} (h : χ = η)
    (hχ : IsOpen (χ.ker : Set G)) (hη : IsOpen (η.ker : Set G))
    (A : SmoothRep.{0, _, uV} ℂ G) : A.twist χ hχ ≅ A.twist η hη := by
  subst h
  exact Iso.refl _

/-- The twist `ν^s A` of an actual supercuspidal representative. -/
def twistRep {r : ℕ} (s : ℝ)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter r s)
    (T.isOpen_ker_determinantPowerCharacter r s)
    (T.ker_determinant_le_ker_determinantPowerCharacter r s) A

theorem twistRep_obj {r : ℕ} (s : ℝ)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    (twistRep T s A).obj = T.segmentFactor A.obj s :=
  rfl

/-- `ν^s A` represents `ν^s ρ` when `A` represents `ρ`. -/
theorem isRepresentedBy_twistRep {ρ : CuspidalDatum.{uV, uF} T} (s : ℝ)
    {A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) : (ρ.twist s).IsRepresentedBy (twistRep T s A) := by
  let := T.topology
  change (twistRep T s A).isoClass = T.supercuspidalClassRealPowerTwist ρ.rank s ρ.cls
  rw [← hA]
  rfl

/-- `ν^j (ν A) ≅ ν^(j+1) A`. -/
def segmentFactorTwistIso {r : ℕ} (j : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    T.segmentFactor (T.segmentFactor A ((1 : ℕ) : ℝ)) ((j : ℕ) : ℝ) ≅
      T.segmentFactor A ((j + 1 : ℕ) : ℝ) :=
  letI := T.topology
  SmoothRep.twistTwistIso _ _ _ _
      (by
        rw [← realPowerCharacter_add]
        exact T.isOpen_ker_determinantPowerCharacter r _) A ≪≫
    twistIsoOfEq (by rw [← realPowerCharacter_add]; push_cast; rfl) _ _ A

end Twist

section Split

variable {r : ℕ} (hr : 0 < r)

theorem uniform_tailRank {m k : ℕ} (hm : m = k + 2) :
    (k + 1) * r = (BlockShape.uniform m r hr).tailRank hm := by
  simp [BlockShape.tailRank, BlockShape.uniform]

theorem uniform_tailShape {m k : ℕ} (hm : m = k + 2) :
    (BlockShape.uniform m r hr).tailShape hm =
      (BlockShape.uniform (k + 1) r hr).rankCast (uniform_tailRank hr hm) :=
  rfl

theorem uniform_split_rank {m k : ℕ} (hm : m = k + 2) : r + (k + 1) * r = m * r := by
  subst hm
  ring

/-- The head/tail split of a normalized product on the uniform shape. -/
theorem headTail_uniform_obj {m k : ℕ} (hm : m = k + 2)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor ((BlockShape.uniform m r hr).headTailShape hm)).obj
        (T.headTailProductFactors (BlockShape.uniform m r hr) hm σ) =
      (generalLinearRankCast T (uniform_split_rank hm)).obj
        ((T.binaryNormalizedProductFunctor r ((k + 1) * r)).obj
          (SmoothRep.universeLift.{uF} (σ (Fin.cast hm.symm 0)),
            (T.normalizedProductInductionFunctor (BlockShape.uniform (k + 1) r hr)).obj
              (fun j => σ (Fin.cast hm.symm j.succ)))) := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  have hX : (T.normalizedProductInductionFunctor (B.headTailShape hm)).obj
      (T.headTailProductFactors B hm σ) =
      (generalLinearRankCast T (B.headRank_add_tailRank hm)).obj
        ((T.binaryNormalizedProductFunctor (B.headRank hm) (B.tailRank hm)).obj
          (SmoothRep.universeLift.{uF} (σ (B.headIndex hm)),
            (T.normalizedProductInductionFunctor (B.tailShape hm)).obj
              (fun j => σ (B.tailIndex hm j)))) := by
    rw [binaryNormalizedProductFunctor_obj_eq T (B.headRank_pos hm)
      (B.tailRank_pos hm) (SmoothRep.universeLift.{uF} (σ (B.headIndex hm)))
      ((T.normalizedProductInductionFunctor (B.tailShape hm)).obj
        (fun j => σ (B.tailIndex hm j)))
      (T.headTailProductFactors B hm σ) rfl rfl]
    exact normalizedProductInductionFunctor_rankCast_obj T _ _ _
  have htail : (T.normalizedProductInductionFunctor (B.tailShape hm)).obj
      (fun j => σ (B.tailIndex hm j)) =
      (generalLinearRankCast T (uniform_tailRank hr hm)).obj
        ((T.normalizedProductInductionFunctor (BlockShape.uniform (k + 1) r hr)).obj
          (fun j => σ (Fin.cast hm.symm j.succ))) :=
    normalizedProductInductionFunctor_rankCast_obj T (BlockShape.uniform (k + 1) r hr)
      (uniform_tailRank hr hm) _
  rw [hX, htail, binary_rankCast_right_obj, rankCast_rankCast_obj]
  rfl

/-- The decreasing induction of length `k + 2` is the rank cast of
`ν^(k+1) A × (ν^k A × ⋯ × A)`. -/
theorem nonempty_iso_segmentInducedDown_split {m k : ℕ} (hm : m = k + 2)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Nonempty (T.segmentInducedDown A m hr ≅
      (generalLinearRankCast T (uniform_split_rank hm)).obj
        ((T.binaryNormalizedProductFunctor r ((k + 1) * r)).obj
          (SmoothRep.universeLift.{uF} (T.segmentFactor A ((k + 1 : ℕ) : ℝ)),
            T.segmentInducedDown A (k + 1) hr))) := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  let e1 := T.headTailProductInductionIso B hm (T.segmentFactorsDown A m hr)
  have hhead : T.segmentFactorsDown A m hr (Fin.cast hm.symm 0) =
      T.segmentFactor A ((k + 1 : ℕ) : ℝ) := by
    change T.segmentFactor A ((m - 1 - 0 : ℕ) : ℝ) = _
    rw [show m - 1 - 0 = k + 1 by omega]
  have htail : (fun j : Fin (BlockShape.uniform (k + 1) r hr).length =>
      T.segmentFactorsDown A m hr (Fin.cast hm.symm j.succ)) =
      T.segmentFactorsDown A (k + 1) hr := by
    funext j
    change T.segmentFactor A ((m - 1 - ((j : ℕ) + 1) : ℕ) : ℝ) =
      T.segmentFactor A ((k + 1 - 1 - (j : ℕ) : ℕ) : ℝ)
    rw [show m - 1 - ((j : ℕ) + 1) = k + 1 - 1 - (j : ℕ) by omega]
  have hX := headTail_uniform_obj T hr hm (T.segmentFactorsDown A m hr)
  refine ⟨e1 ≪≫ eqToIso (hX.trans ?_)⟩
  exact congrArg (generalLinearRankCast T (uniform_split_rank hm)).obj
    (binary_obj_congr T (congrArg (fun X => SmoothRep.universeLift.{uF} X) hhead)
      (congrArg (T.normalizedProductInductionFunctor (BlockShape.uniform (k + 1) r hr)).obj
        htail))

/-- The increasing induction of length `k + 2` is the rank cast of
`A × (νA × ⋯ × ν^(k+1) A)`, with the tail written as the increasing induction of
length `k + 1` of `νA`. -/
theorem nonempty_iso_segmentInduced_split {m k : ℕ} (hm : m = k + 2)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Nonempty (T.segmentInduced A m hr ≅
      (generalLinearRankCast T (uniform_split_rank hm)).obj
        ((T.binaryNormalizedProductFunctor r ((k + 1) * r)).obj
          (SmoothRep.universeLift.{uF} (T.segmentFactor A ((0 : ℕ) : ℝ)),
            T.segmentInduced (T.segmentFactor A ((1 : ℕ) : ℝ)) (k + 1) hr))) := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  let e1 := T.headTailProductInductionIso B hm (T.segmentFactors A m hr)
  have hX := headTail_uniform_obj T hr hm (T.segmentFactors A m hr)
  let eT : (T.normalizedProductInductionFunctor (BlockShape.uniform (k + 1) r hr)).obj
      (fun j : Fin (k + 1) => T.segmentFactor A (((j : ℕ) + 1 : ℕ) : ℝ)) ≅
      T.segmentInduced (T.segmentFactor A ((1 : ℕ) : ℝ)) (k + 1) hr :=
    (T.normalizedProductInductionFunctor (BlockShape.uniform (k + 1) r hr)).mapIso
      (Pi.isoMk fun j => (segmentFactorTwistIso T (j : ℕ) A).symm)
  refine ⟨e1 ≪≫ eqToIso hX ≪≫ (generalLinearRankCast T _).mapIso
    ((T.binaryNormalizedProductFunctor r ((k + 1) * r)).mapIso
      (Iso.prod (Iso.refl _) eT))⟩

end Split

end Langlands.Classification.SegmentHeadSupport

import Langlands.Representation.Classification.TadicRectanglePrimeRing
import Langlands.Representation.Classification.TadicBlockReductionStatement
import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity
import Langlands.Representation.Aubert.SegmentPolynomialComparisonProof
import Langlands.Representation.Classification.TadicSocleIndependence
import Langlands.Representation.Classification.MultisegmentConstituentDataExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleExistenceProof
import Langlands.Representation.Aubert.SegmentProductClass
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# The Grothendieck ring `R` for Tadić's Lemma 4.8(ii)

Effective classes, products of effective classes, the multiplicity of `⟨a + b⟩` in
`⟨a⟩ × ⟨b⟩` (Zelevinsky 1980, Proposition 8.4) and injectivity of `a ↦ ⟨a⟩`, derived from
the published triangularity of `Aubert/SegmentPolynomialSurjectivity`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TadicBlockRing

open Aubert Aubert.SegmentPolynomialSurjectivity PadicField.TopologicalData
open SmoothRep SmoothRep.IrreducibleGrothendieckProof VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

export TadicRectanglePrime (ringR ψ₀ zetaR segmentEquiv basisSpan
  mem_basisSpan_of_isEffective isEffective_basisClass_mul isEffective_mul
  coeff_le_of_isEffective_sub rankLE_of_isLabel_of_coeff_pos
  coeff_zetaR_pos_of_isLabel eq_of_isLabel isEffective_zetaR_sub_basisClass
  coeff_zetaR_sub_basisClass_eq_zero)

attribute [local instance] ringR

/-- The class in `R` of a finite-length representation of `GL_N`. -/
abbrev cls {N : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (hπ : letI := T.topology; π.HasFiniteLength) : GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  gradedInclusion F T N (GeneralLinear.finiteLengthClass N F.Carrier π hπ)

/-! ### Effective classes -/

theorem isEffective_of_mem_basisSpan {x : GradedGrothendieckGroup.{uF, uV} F T}
    (hx : x ∈ basisSpan F T) : IsEffective F T x := by
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨m, c, rfl⟩ := hy
    exact isEffective_basisClass F T m c
  | zero => exact isEffective_zero F T
  | add y z _ _ hy hz => exact hy.add F T hz

/-! ### The rank order -/

theorem rankLE_add {a b a' b' : T.Multisegment.{max uF uV, uF}}
    (h : Multisegment.RankLE a b) (h' : Multisegment.RankLE a' b') :
    Multisegment.RankLE (a + a') (b + b') := by
  refine ⟨?_, fun I => ?_⟩
  · rw [Multisegment.cuspidalContent_add, Multisegment.cuspidalContent_add, h.1, h'.1]
  · rw [Multisegment.containmentCount_add, Multisegment.containmentCount_add]
    exact Nat.add_le_add (h.2 I) (h'.2 I)

theorem rankLE_of_add_right {a b c : T.Multisegment.{max uF uV, uF}}
    (h : Multisegment.RankLE (a + c) (b + c)) : Multisegment.RankLE a b := by
  refine ⟨?_, fun I => ?_⟩
  · have := h.1
    rw [Multisegment.cuspidalContent_add, Multisegment.cuspidalContent_add] at this
    exact add_right_cancel this
  · have := h.2 I
    rw [Multisegment.containmentCount_add, Multisegment.containmentCount_add] at this
    omega

/-! ### Labels -/

theorem one_le_coeff_zetaR_of_isLabel {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : IsLabel F T a m c) : 1 ≤ coeff F T m c (zetaR F T a) :=
  one_le_coeff_zeta_of_isLabel F T _ _ h

theorem zetaR_zero : zetaR.{uF, uV} F T 0 = 1 :=
  zeta_zero F T _ _

/-- The labels of `a` occur in `ζ(a)` with total multiplicity at most one. -/
theorem labelCount_le_one (a : T.Multisegment.{max uF uV, uF}) :
    weightedCount F T (labelWeight F T a) (zetaR F T a) ≤ 1 :=
  labelCount_zeta_le_one F T _ _ (ψ₀ F T) (highestDerivativeLabelStep F T (ψ₀ F T)) a

theorem label_unique {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c c' : Label.{uF, uV} F T m} (hc : IsLabel F T a m c) (hc' : IsLabel F T a m c') :
    c = c' := by
  by_contra hne
  have h0 := coeff_zetaR_sub_basisClass_eq_zero F T hc hc'
  rw [map_sub, coeff_basisClass_of_ne F T m hne, sub_zero] at h0
  have := coeff_zetaR_pos_of_isLabel F T hc'
  omega

/-! ### Socles and labels -/

theorem isIrreducible_of_isZelevinskySocle {N : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : a.IsZelevinskySocle π) : letI := T.topology; π.IsIrreducible := by
  obtain ⟨d, -, -, -, hsoc⟩ := h
  exact hsoc.1

theorem isLabel_of_isZelevinskySocle {N : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : a.IsZelevinskySocle π) :
    letI := T.topology
    IsLabel F T a N (GeneralLinear.irreducibleIsoClass N F.Carrier π
      (isIrreducible_of_isZelevinskySocle F T h)) := by
  let := T.topology
  obtain ⟨d, hd, hz⟩ := h
  exact ⟨π, _, rfl, d, hd, hz.isZelevinskySubrepresentation⟩

theorem exists_isZelevinskySocle (a : T.Multisegment.{max uF uV, uF}) :
    letI := T.topology
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a.degree F.Carrier),
      a.IsZelevinskySocle π := by
  let := T.topology
  obtain ⟨⟨d, hd, ho, hs⟩, -⟩ := multisegmentConstituentDataExistence.{uF, uV} F T a
  obtain ⟨π, hπ⟩ := orderedMultisegmentSocleExistence.{uF, uV} F T _ d ho hs
  exact ⟨π, d, hd, hπ⟩

theorem exists_isLabel_of (a : T.Multisegment.{max uF uV, uF}) :
    ∃ c : Label.{uF, uV} F T a.degree, IsLabel F T a a.degree c := by
  obtain ⟨π, hπ⟩ := exists_isZelevinskySocle F T a
  exact ⟨_, isLabel_of_isZelevinskySocle F T hπ⟩

/-! ### Zelevinsky's Proposition 8.4 -/

/-- Basis classes of labels of members of `S`, and their sums. -/
def spanIn (S : Set (T.Multisegment.{max uF uV, uF})) :
    AddSubmonoid (GradedGrothendieckGroup.{uF, uV} F T) :=
  AddSubmonoid.closure {y | ∃ m c, (∃ b ∈ S, IsLabel F T b m c) ∧ y = basisClass F T m c}

theorem isEffective_of_mem_spanIn {S : Set (T.Multisegment.{max uF uV, uF})}
    {x : GradedGrothendieckGroup.{uF, uV} F T} (hx : x ∈ spanIn F T S) : IsEffective F T x := by
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨m, c, -, rfl⟩ := hy
    exact isEffective_basisClass F T m c
  | zero => exact isEffective_zero F T
  | add y z _ _ hy hz => exact hy.add F T hz

theorem mem_spanIn {S : Set (T.Multisegment.{max uF uV, uF})}
    {x : GradedGrothendieckGroup.{uF, uV} F T} (hx : IsEffective F T x)
    (h : ∀ m c, 0 < coeff F T m c x → ∃ b ∈ S, IsLabel F T b m c) : x ∈ spanIn F T S := by
  classical
  let := T.topology
  rw [eq_sum_basisClass F T x]
  refine AddSubmonoid.sum_mem _ fun m _ => ?_
  rw [Finsupp.sum]
  refine AddSubmonoid.sum_mem _ fun c hc => ?_
  have hz : 0 ≤ factorMap (x m) c := hx m c
  have hne : factorMap (x m) c ≠ 0 := Finsupp.mem_support_iff.mp hc
  have hpos : 0 < coeff F T m c x := lt_of_le_of_ne hz (Ne.symm hne)
  have : factorMap (x m) c • basisClass F T m c =
      (factorMap (x m) c).toNat • basisClass F T m c := by
    conv_lhs => rw [← Int.toNat_of_nonneg hz]
    rw [natCast_zsmul]
  rw [this]
  exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure
    (show basisClass F T m c ∈
        {y | ∃ m c, (∃ b ∈ S, IsLabel F T b m c) ∧ y = basisClass F T m c} from
      ⟨m, c, h m c hpos, rfl⟩)) _

/-- `[c₁] [c₂] ≤ ζ(b₁ + b₂)` for labels `c_i` of `b_i`. -/
theorem isEffective_zetaR_add_sub_mul {b₁ b₂ : T.Multisegment.{max uF uV, uF}} {m₁ m₂ : ℕ}
    {c₁ : Label.{uF, uV} F T m₁} {c₂ : Label.{uF, uV} F T m₂} (h₁ : IsLabel F T b₁ m₁ c₁)
    (h₂ : IsLabel F T b₂ m₂ c₂) :
    IsEffective F T (zetaR F T (b₁ + b₂) - basisClass F T m₁ c₁ * basisClass F T m₂ c₂) := by
  have e : zetaR F T (b₁ + b₂) - basisClass F T m₁ c₁ * basisClass F T m₂ c₂ =
      (zetaR F T b₁ - basisClass F T m₁ c₁) * zetaR F T b₂ +
        basisClass F T m₁ c₁ * (zetaR F T b₂ - basisClass F T m₂ c₂) := by
    rw [zetaR, zeta_add]
    ring
  rw [e]
  exact (isEffective_mul F T (isEffective_zetaR_sub_basisClass F T h₁)
    (isEffective_zeta F T _ _ b₂)).add F T
    (isEffective_mul F T (isEffective_basisClass F T m₁ c₁)
      (isEffective_zetaR_sub_basisClass F T h₂))

/-- Triangularity for products: a label of `e` occurring in `u v` satisfies `e ≼ b₁ + b₂`
for labels of `b₁ ∈ S₁` in `u` and of `b₂ ∈ S₂` in `v`. -/
theorem rankLE_of_coeff_mul_pos {S₁ S₂ : Set (T.Multisegment.{max uF uV, uF})}
    {u v : GradedGrothendieckGroup.{uF, uV} F T} (hu : u ∈ spanIn F T S₁)
    (hv : v ∈ spanIn F T S₂) {e : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (he : IsLabel F T e m c) (h : 0 < coeff F T m c (u * v)) :
    ∃ b₁ ∈ S₁, ∃ b₂ ∈ S₂, Multisegment.RankLE e (b₁ + b₂) := by
  induction hu using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨m₁, c₁, ⟨b₁, hb₁, hl₁⟩, rfl⟩ := hy
    induction hv using AddSubmonoid.closure_induction with
    | mem z hz =>
      obtain ⟨m₂, c₂, ⟨b₂, hb₂, hl₂⟩, rfl⟩ := hz
      refine ⟨b₁, hb₁, b₂, hb₂, rankLE_of_isLabel_of_coeff_pos F T he ?_⟩
      exact lt_of_lt_of_le h
        (coeff_le_of_isEffective_sub F T (isEffective_zetaR_add_sub_mul F T hl₁ hl₂) m c)
    | zero => rw [mul_zero, map_zero] at h; exact absurd h (lt_irrefl 0)
    | add z w hz hw ihz ihw =>
      rw [mul_add, map_add] at h
      have h1 := isEffective_mul F T (isEffective_basisClass F T m₁ c₁)
        (isEffective_of_mem_spanIn F T hz) m c
      have h2 := isEffective_mul F T (isEffective_basisClass F T m₁ c₁)
        (isEffective_of_mem_spanIn F T hw) m c
      rcases lt_or_eq_of_le h1 with h1 | h1
      · exact ihz h1
      · rw [← h1, zero_add] at h
        exact ihw h
  | zero => rw [zero_mul, map_zero] at h; exact absurd h (lt_irrefl 0)
  | add y z hy hz ihy ihz =>
    rw [add_mul, map_add] at h
    have h1 := isEffective_mul F T (isEffective_of_mem_spanIn F T hy)
      (isEffective_of_mem_spanIn F T hv) m c
    rcases lt_or_eq_of_le h1 with h1 | h1
    · exact ihy h1
    · rw [← h1, zero_add] at h
      exact ihz h

theorem mem_spanIn_singleton {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (hc : IsLabel F T a m c) :
    basisClass F T m c ∈ spanIn F T {a} :=
  AddSubmonoid.subset_closure ⟨m, c, ⟨a, rfl, hc⟩, rfl⟩

/-- `ζ(a) - [⟨a⟩]` only contains labels of multisegments strictly below `a`. -/
theorem zetaR_sub_mem_spanIn {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (hc : IsLabel F T a m c) :
    zetaR F T a - basisClass F T m c ∈
      spanIn F T {b | Multisegment.RankLE b a ∧ b ≠ a} := by
  refine mem_spanIn F T (isEffective_zetaR_sub_basisClass F T hc) fun m' c' hpos => ?_
  obtain ⟨b, hb⟩ := exists_isLabel F T (multisegmentSocleExhaustion.{uF, uV} F T) m' c'
  have hz : 0 < coeff F T m' c' (zetaR F T a) := by
    have := isEffective_basisClass F T m c m' c'
    rw [map_sub] at hpos
    omega
  refine ⟨b, ⟨rankLE_of_isLabel_of_coeff_pos F T hb hz, ?_⟩, hb⟩
  rintro rfl
  have := coeff_zetaR_sub_basisClass_eq_zero F T hc hb
  omega

/-- **Zelevinsky 1980, Proposition 8.4** (two factors): the label of `a + b` occurs in
`[⟨a⟩] [⟨b⟩]`. -/
theorem one_le_coeff_basisClass_mul {a b : T.Multisegment.{max uF uV, uF}} {ma mb M : ℕ}
    {ca : Label.{uF, uV} F T ma} {cb : Label.{uF, uV} F T mb} {L : Label.{uF, uV} F T M}
    (ha : IsLabel F T a ma ca) (hb : IsLabel F T b mb cb) (hL : IsLabel F T (a + b) M L) :
    1 ≤ coeff F T M L (basisClass F T ma ca * basisClass F T mb cb) := by
  set x := basisClass F T ma ca
  set y := basisClass F T mb cb
  have hz : zetaR F T (a + b) = x * y + x * (zetaR F T b - y) + (zetaR F T a - x) * y +
      (zetaR F T a - x) * (zetaR F T b - y) := by
    rw [zetaR, zeta_add]
    ring
  have hxa := mem_spanIn_singleton F T ha
  have hyb := mem_spanIn_singleton F T hb
  have hEa := zetaR_sub_mem_spanIn F T ha
  have hEb := zetaR_sub_mem_spanIn F T hb
  have h1 : coeff F T M L (x * (zetaR F T b - y)) = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (isEffective_mul F T (isEffective_of_mem_spanIn F T hxa)
      (isEffective_of_mem_spanIn F T hEb) M L) (Ne.symm hne)
    obtain ⟨a', rfl, b', ⟨hb'b, hne'⟩, hr⟩ := rankLE_of_coeff_mul_pos F T hxa hEb hL hpos
    rw [add_comm a', add_comm a'] at hr
    exact hne' (Multisegment.RankLE.antisymm hb'b (rankLE_of_add_right F T hr))
  have h2 : coeff F T M L ((zetaR F T a - x) * y) = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (isEffective_mul F T (isEffective_of_mem_spanIn F T hEa)
      (isEffective_of_mem_spanIn F T hyb) M L) (Ne.symm hne)
    obtain ⟨a', ⟨ha'a, hne'⟩, b', rfl, hr⟩ := rankLE_of_coeff_mul_pos F T hEa hyb hL hpos
    exact hne' (Multisegment.RankLE.antisymm ha'a (rankLE_of_add_right F T hr))
  have h3 : coeff F T M L ((zetaR F T a - x) * (zetaR F T b - y)) = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (isEffective_mul F T (isEffective_of_mem_spanIn F T hEa)
      (isEffective_of_mem_spanIn F T hEb) M L) (Ne.symm hne)
    obtain ⟨a', ⟨ha'a, hne'⟩, b', ⟨hb'b, -⟩, hr⟩ := rankLE_of_coeff_mul_pos F T hEa hEb hL hpos
    have hr' : Multisegment.RankLE (a + b) (a' + b) :=
      hr.trans (rankLE_add F T (Multisegment.RankLE.refl a') hb'b)
    exact hne' (Multisegment.RankLE.antisymm ha'a (rankLE_of_add_right F T hr'))
  have h0 := one_le_coeff_zetaR_of_isLabel F T hL
  rw [hz, map_add, map_add, map_add, h1, h2, h3] at h0
  simpa using h0

theorem isEffective_prod {ι : Type*} (s : Finset ι)
    (f : ι → GradedGrothendieckGroup.{uF, uV} F T) (hf : ∀ i ∈ s, IsEffective F T (f i)) :
    IsEffective F T (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f (IsEffective F T) (fun x y hx hy => isEffective_mul F T hx hy)
    ?_ hf
  obtain ⟨c0, hc0⟩ := gradedUnit_eq_basisClass.{uF, uV} F T
  change IsEffective F T (gradedUnit F T)
  rw [hc0]
  exact isEffective_basisClass F T 0 c0

/-- **Zelevinsky 1980, Proposition 8.4**: the label of `∑ a_i` occurs in `∏ [⟨a_i⟩]`. -/
theorem one_le_coeff_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → T.Multisegment.{max uF uV, uF}) (m : ι → ℕ) (c : ∀ i, Label.{uF, uV} F T (m i))
    (hc : ∀ i ∈ s, IsLabel F T (a i) (m i) (c i)) {M : ℕ} {L : Label.{uF, uV} F T M}
    (hL : IsLabel F T (∑ i ∈ s, a i) M L) :
    1 ≤ coeff F T M L (∏ i ∈ s, basisClass F T (m i) (c i)) := by
  induction s using Finset.induction_on generalizing M with
  | empty =>
    rw [Finset.prod_empty]
    rw [Finset.sum_empty] at hL
    have h0 := one_le_coeff_zetaR_of_isLabel F T hL
    rwa [zetaR_zero] at h0
  | insert i s his ih =>
    rw [Finset.sum_insert his] at hL
    rw [Finset.prod_insert his]
    obtain ⟨Ls, hLs⟩ := exists_isLabel_of F T (∑ i ∈ s, a i)
    have hih := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj)) hLs
    have hE : IsEffective F T ((∏ i ∈ s, basisClass F T (m i) (c i)) -
        basisClass F T _ Ls) := isEffective_sub_basisClass F T
      (isEffective_prod F T s _ fun j _ => isEffective_basisClass F T _ _) hih
    have e : basisClass F T (m i) (c i) * ∏ i ∈ s, basisClass F T (m i) (c i) =
        basisClass F T (m i) (c i) * basisClass F T _ Ls +
          basisClass F T (m i) (c i) * ((∏ i ∈ s, basisClass F T (m i) (c i)) -
            basisClass F T _ Ls) := by ring
    rw [e, map_add]
    have h1 := one_le_coeff_basisClass_mul F T (hc i (Finset.mem_insert_self i s)) hLs hL
    have h2 := isEffective_mul F T (isEffective_basisClass F T _ (c i)) hE M L
    omega

/-! ### Classes of products -/

section Products

open GeneralLinear Derivative

/-- A product of irreducible blocks has finite length. -/
theorem hasFiniteLength_product {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor B).obj σ).HasFiniteLength := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ProductDerivativesFiniteLength.hasFiniteLength_of_iso
      (T.emptyProductUnitIso B σ).symm (binaryProductUnit_hasFiniteLength F T)
  · exact irreducibleProductFiniteLength.{uF, max uF uV} F T n hn B σ hσ

/-- A product with at least two blocks is the binary product of its first block and the
product of the others. -/
theorem nonempty_iso_binary {n k : ℕ} (B : BlockShape n) (h : B.length = k + 2)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
      (generalLinearRankCast T (B.headRank_add_tailRank h)).obj
        ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj
          (σ (B.headIndex h), (T.normalizedProductInductionFunctor (B.tailShape h)).obj
            (fun j => σ (B.tailIndex h j))))) := by
  let _ := T.topology
  let e1 := T.headTailProductInductionIso B h σ
  let lift := SmoothRep.universeLift.{uF} (σ (B.headIndex h))
  have hX : (T.normalizedProductInductionFunctor (B.headTailShape h)).obj
      (T.headTailProductFactors B h σ) =
      (generalLinearRankCast T (B.headRank_add_tailRank h)).obj
        ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj
          (lift, (T.normalizedProductInductionFunctor (B.tailShape h)).obj
            (fun j => σ (B.tailIndex h j)))) := by
    rw [SegmentProductSplit.binaryNormalizedProductFunctor_obj_eq T (B.headRank_pos h)
      (B.tailRank_pos h) lift _ (T.headTailProductFactors B h σ) rfl rfl]
    exact SegmentProductSplit.normalizedProductInductionFunctor_rankCast_obj T _ _ _
  let eL : lift ≅ σ (B.headIndex h) :=
    SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} (σ (B.headIndex h))).symm
  exact ⟨e1 ≪≫ eqToIso hX ≪≫ (generalLinearRankCast T _).mapIso
    ((T.binaryNormalizedProductFunctor _ _).mapIso (Iso.prod eL (Iso.refl _)))⟩

theorem cls_eq_of_iso {N : ℕ}
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (e : letI := T.topology; π ≅ π') (hπ : letI := T.topology; π.HasFiniteLength)
    (hπ' : letI := T.topology; π'.HasFiniteLength) : cls F T π hπ = cls F T π' hπ' := by
  let := T.topology
  exact congrArg (gradedInclusion F T N)
    (SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso (A := ⟨π, hπ⟩) (B := ⟨π', hπ'⟩) e)

/-- **The class of a product of irreducible blocks** is the product of their classes. -/
theorem cls_product_of_length_eq_succ (k : ℕ) :
    letI := T.topology
    ∀ {n : ℕ} (B : BlockShape n) (_ : B.length = k + 1)
      (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (hσ : ∀ i, (σ i).IsIrreducible),
      cls F T ((T.normalizedProductInductionFunctor B).obj σ)
          (hasFiniteLength_product F T B σ hσ) =
        ∏ i, cls F T (σ i) (SmoothRep.hasFiniteLength_of_isIrreducible (hσ i)) := by
  let := T.topology
  induction k with
  | zero =>
    intro n B h σ hσ
    let i : Fin B.length := Fin.cast h.symm 0
    have hsz := B.singleBlock_size h i
    have hb := SmoothRep.hasFiniteLength_of_isIrreducible (hσ i)
    have : Subsingleton (Fin B.length) :=
      ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
    let e : (T.normalizedProductInductionFunctor B).obj σ ≅
        (generalLinearRankCast T hsz).obj (σ i) :=
      SmoothRep.mkIso ((T.singleBlockNormalizedProductEquiv B h
        (fun j => (σ j).representation) (fun j => (σ j).isSmooth) i).trans
          (SegmentProductOrderedAssembly.rankCastEquiv T hsz (σ i)))
    calc cls F T ((T.normalizedProductInductionFunctor B).obj σ) _
        = gradedInclusion F T n
            (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
              ((generalLinearRankCast T hsz).obj (σ i))
              (ProductDerivativesFiniteLength.hasFiniteLength_rankCast T hsz _ hb)) :=
          cls_eq_of_iso F T e _ _
      _ = cls F T (σ i) hb := gradedInclusion_rankCast F T hsz _ hb
      _ = ∏ j, cls F T (σ j) (SmoothRep.hasFiniteLength_of_isIrreducible (hσ j)) :=
          (Fintype.prod_subsingleton
            (fun j => cls F T (σ j) (SmoothRep.hasFiniteLength_of_isIrreducible (hσ j))) i).symm
  | succ k ih =>
    intro n B h' σ hσ
    have h : B.length = k + 2 := h'
    obtain ⟨e⟩ := nonempty_iso_binary F T B h σ
    have hab := B.headRank_add_tailRank h
    have hA := SmoothRep.hasFiniteLength_of_isIrreducible (hσ (B.headIndex h))
    have hB := hasFiniteLength_product F T (B.tailShape h) (fun j => σ (B.tailIndex h j))
      (fun j => hσ _)
    have hP := binaryProduct_preservesFiniteLength F T (B.headRank h) (B.tailRank h) _ _ hA hB
    calc cls F T ((T.normalizedProductInductionFunctor B).obj σ) _
        = gradedInclusion F T n
            (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
              ((generalLinearRankCast T hab).obj
                ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj
                  (σ (B.headIndex h), (T.normalizedProductInductionFunctor (B.tailShape h)).obj
                    (fun j => σ (B.tailIndex h j)))))
              (ProductDerivativesFiniteLength.hasFiniteLength_rankCast T hab _ hP)) :=
          cls_eq_of_iso F T e _ _
      _ = gradedInclusion F T (B.headRank h + B.tailRank h)
            (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
              ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj
                  (σ (B.headIndex h), (T.normalizedProductInductionFunctor (B.tailShape h)).obj
                    (fun j => σ (B.tailIndex h j)))) hP) :=
          gradedInclusion_rankCast F T hab _ hP
      _ = gradedInclusion F T (B.headRank h + B.tailRank h)
            (binaryProductK0 F T (binaryProductExactness F T) (B.headRank h) (B.tailRank h)
              (SmoothRep.FiniteLengthGrothendieckGroup.ofObject ⟨σ (B.headIndex h), hA⟩)
              (SmoothRep.FiniteLengthGrothendieckGroup.ofObject ⟨_, hB⟩)) := by
          rw [binaryProductK0_classes]
      _ = cls F T (σ (B.headIndex h)) hA * cls F T _ hB :=
          (gradedMultiplication_homogeneous F T _ _ _ _ _).symm
      _ = cls F T (σ (B.headIndex h)) hA *
            ∏ j, cls F T (σ (B.tailIndex h j))
              (SmoothRep.hasFiniteLength_of_isIrreducible (hσ (B.tailIndex h j))) := by
          exact congrArg _ (ih (B.tailShape h) rfl (fun j => σ (B.tailIndex h j)) (fun j => hσ _))
      _ = ∏ i, cls F T (σ i) (SmoothRep.hasFiniteLength_of_isIrreducible (hσ i)) := by
          rcases B with ⟨r, size, pos, sum⟩
          dsimp at h
          subst r
          conv_rhs => rw [Fin.prod_univ_succ]
          rfl

theorem cls_product {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible) :
    letI := T.topology
    cls F T ((T.normalizedProductInductionFunctor B).obj σ)
        (hasFiniteLength_product F T B σ hσ) =
      ∏ i, cls F T (σ i) (SmoothRep.hasFiniteLength_of_isIrreducible (hσ i)) := by
  let := T.topology
  by_cases hB : B.length = 0
  · have : IsEmpty (Fin B.length) := by rw [hB]; infer_instance
    have hn : n = 0 := by
      rw [← B.sum_eq]
      exact Finset.sum_of_isEmpty _
    subst hn
    rw [Fintype.prod_empty]
    change _ = gradedUnit F T
    exact congrArg (gradedInclusion F T 0)
      (SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
        (A := ⟨_, hasFiniteLength_product F T B σ hσ⟩)
        (B := ⟨_, binaryProductUnit_hasFiniteLength F T⟩) (T.emptyProductUnitIso B σ))
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hB
    exact cls_product_of_length_eq_succ F T k B hk σ hσ

end Products

/-! ### Irreducible classes -/

theorem cls_eq_basisClass {N : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hfl : letI := T.topology; π.HasFiniteLength) :
    letI := T.topology
    cls F T π hfl = basisClass F T N (GeneralLinear.irreducibleIsoClass N F.Carrier π hπ) :=
  (basisClass_irreducibleIsoClass F T N π hπ).symm

theorem eq_of_basisClass_eq {N : ℕ} {c c' : Label.{uF, uV} F T N}
    (h : basisClass F T N c = basisClass F T N c') : c = c' := by
  by_contra hne
  have h1 := coeff_basisClass_self F T N c
  rw [h, coeff_basisClass_of_ne F T N (Ne.symm hne)] at h1
  exact zero_ne_one h1

/-- Irreducible representations with equal classes are isomorphic. -/
theorem nonempty_iso_of_cls_eq {N : ℕ}
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hπ' : letI := T.topology; π'.IsIrreducible)
    (hfl : letI := T.topology; π.HasFiniteLength) (hfl' : letI := T.topology; π'.HasFiniteLength)
    (h : cls F T π hfl = cls F T π' hfl') : letI := T.topology; Nonempty (π ≅ π') := by
  let := T.topology
  rw [cls_eq_basisClass F T hπ, cls_eq_basisClass F T hπ'] at h
  exact (SmoothRep.irreducibleIsoClass_eq_iff hπ hπ').mp (eq_of_basisClass_eq F T h)

/-- **Products of socles.** If the class of an irreducible `π` is a product of classes of
labels of `a_i`, then `π` is a Zelevinsky socle of `∑ a_i`. -/
theorem isZelevinskySocle_of_cls_eq_prod {N : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hfl : letI := T.topology; π.HasFiniteLength)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → T.Multisegment.{max uF uV, uF})
    (m : ι → ℕ) (c : ∀ i, Label.{uF, uV} F T (m i)) (hc : ∀ i ∈ s, IsLabel F T (a i) (m i) (c i))
    (h : cls F T π hfl = ∏ i ∈ s, basisClass F T (m i) (c i)) :
    (∑ i ∈ s, a i).IsZelevinskySocle π := by
  let := T.topology
  obtain ⟨τ, hτ⟩ := exists_isZelevinskySocle F T (∑ i ∈ s, a i)
  have hL := isLabel_of_isZelevinskySocle F T hτ
  have h1 := one_le_coeff_prod F T s a m c hc hL
  rw [← h, cls_eq_basisClass F T hπ] at h1
  by_cases hN : (∑ i ∈ s, a i).degree = N
  · subst hN
    by_cases hc' : GeneralLinear.irreducibleIsoClass _ F.Carrier π hπ =
        GeneralLinear.irreducibleIsoClass _ F.Carrier τ (isIrreducible_of_isZelevinskySocle F T hτ)
    · obtain ⟨e⟩ := (SmoothRep.irreducibleIsoClass_eq_iff hπ _).mp hc'
      exact Multisegment.IsZelevinskySocle.of_iso hτ e.symm
    · rw [coeff_basisClass_of_ne F T _ hc'] at h1
      omega
  · rw [basisClass, coeff_gradedInclusion_of_ne F T hN] at h1
    omega

/-! ### Factorization in `R` -/

/-- A divisor of a product of primes in a cancellative monoid is associated to a
sub-product. -/
theorem exists_le_associated_of_dvd_prod {M₀ : Type*} [CommMonoidWithZero M₀]
    [IsCancelMulZero M₀] (s : Multiset M₀) (hs : ∀ q ∈ s, Prime q) {x : M₀}
    (h : x ∣ s.prod) : ∃ t ≤ s, Associated x t.prod := by
  induction s using Multiset.induction_on generalizing x with
  | empty =>
    rw [Multiset.prod_zero] at h
    refine ⟨0, le_rfl, ?_⟩
    rw [Multiset.prod_zero]
    exact associated_one_iff_isUnit.mpr (isUnit_of_dvd_one h)
  | cons q s ih =>
    have hq : Prime q := hs q (Multiset.mem_cons_self q s)
    have hs' : ∀ r ∈ s, Prime r := fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.prod_cons] at h
    by_cases hqx : q ∣ x
    · obtain ⟨y, rfl⟩ := hqx
      have hy : y ∣ s.prod := (mul_dvd_mul_iff_left hq.ne_zero).mp h
      obtain ⟨t, hts, hyt⟩ := ih hs' hy
      exact ⟨q ::ₘ t, Multiset.cons_le_cons q hts, by
        rw [Multiset.prod_cons]; exact hyt.mul_left q⟩
    · obtain ⟨c, hc⟩ := h
      have hqc : q ∣ c := by
        rcases hq.dvd_or_dvd (Dvd.intro _ hc) with h1 | h1
        · exact absurd h1 hqx
        · exact h1
      obtain ⟨c', rfl⟩ := hqc
      have hx : x ∣ s.prod := by
        refine ⟨c', ?_⟩
        have : q * s.prod = q * (x * c') := by rw [hc, mul_left_comm]
        exact mul_left_cancel₀ hq.ne_zero this
      obtain ⟨t, hts, hxt⟩ := ih hs' hx
      exact ⟨t, hts.trans (Multiset.le_cons_self s q), hxt⟩

theorem isDomain_R : IsDomain (GradedGrothendieckGroup.{uF, uV} F T) :=
  (segmentEquiv F T).symm.toMulEquiv.isDomain (MvPolynomial T.Segment.{max uF uV, uF} ℤ)

/-- The units of `R` are `±1`. -/
theorem isUnit_R {u : GradedGrothendieckGroup.{uF, uV} F T} (hu : IsUnit u) :
    u = 1 ∨ u = -1 := by
  have hu' : IsUnit ((segmentEquiv F T).symm u) := hu.map (segmentEquiv F T).symm
  obtain ⟨r, hr, hre⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu'
  have hu'' : u = segmentEquiv F T (MvPolynomial.C r) := by
    rw [← hre, RingEquiv.apply_symm_apply]
  rcases Int.isUnit_iff.mp hr with rfl | rfl
  · left; rw [hu'', map_one, map_one]
  · right; rw [hu'', map_neg, map_one, map_neg, map_one]

theorem eq_or_eq_neg_of_associated {x y : GradedGrothendieckGroup.{uF, uV} F T}
    (h : Associated x y) : x = y ∨ x = -y := by
  obtain ⟨u, hu⟩ := h
  rcases isUnit_R F T u.isUnit with h1 | h1
  · left; rw [← hu, h1, mul_one]
  · right; rw [← hu, h1]; ring

end Langlands.Classification.TadicBlockRing

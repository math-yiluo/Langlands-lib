import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Tensor.ProductFiltration

/-!
# Raising the carrier universe of segments and multisegments

Supercuspidal representatives, their classes, cuspidal data, segments and
multisegments with carriers in `Type uV` are lifted to the saturated carrier
universe `max uF uV` by `ULift`. The lift is injective, commutes with real
twists, and preserves and reflects linkage, precedence, segment heads and the
multisegment Langlands-head relation. No classification theorem is assumed.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

namespace GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

namespace SupercuspidalRep

/-- The supercuspidal object with carrier raised to `Type (max uF uV)`. -/
def universeLift (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    SupercuspidalRep.{uF, max uF uV} (F := F) (n := n) :=
  ⟨SmoothRep.universeLift.{uF} A.obj,
    (SmoothRep.isIrreducible_universeLift_iff A.obj).mpr A.property.1,
    isSupercuspidal_of_equiv (SmoothRep.universeLiftEquiv A.obj) A.property.2⟩

@[simp]
theorem universeLift_obj (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    (universeLift A).obj = SmoothRep.universeLift.{uF} A.obj := rfl

/-- The actual equivalence `v ↦ ULift.up v` of a representative with its lift. -/
def universeLiftEquiv (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    A.obj.representation.Equiv (universeLift A).obj.representation :=
  SmoothRep.universeLiftEquiv.{uF} A.obj

/-- The underlying equivalence of an isomorphism of supercuspidal objects. -/
def equivOfIso {A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)} (e : A ≅ B) :
    A.obj.representation.Equiv B.obj.representation :=
  SmoothRep.equivOfIso ((supercuspidalProperty (F := F) (n := n)).ι.mapIso e)

/-- Lifting is compatible with isomorphisms. -/
def universeLiftIso {A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)} (e : A ≅ B) :
    universeLift A ≅ universeLift B :=
  isoMk (SmoothRep.mkIso
    (((universeLiftEquiv A).symm.trans (equivOfIso e)).trans (universeLiftEquiv B)))

/-- Isomorphic lifts come from isomorphic objects. -/
def isoOfUniverseLiftIso {A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)}
    (e : universeLift A ≅ universeLift B) : A ≅ B :=
  isoMk (SmoothRep.mkIso
    (((universeLiftEquiv A).trans (equivOfIso e)).trans (universeLiftEquiv B).symm))

/-- Lifting commutes with twisting by a character of the determinant. -/
def universeLiftTwistIso (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    universeLift (twist χ hχ hdet A) ≅ twist χ hχ hdet (universeLift A) :=
  isoMk (SmoothRep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => rfl))

end SupercuspidalRep

namespace SupercuspidalClass

/-- Lift supercuspidal isomorphism classes to the carrier universe `max uF uV`. -/
def universeLift :
    SupercuspidalClass.{uV, uF} (F := F) (n := n) →
      SupercuspidalClass.{max uF uV, uF} (F := F) (n := n) :=
  Quotient.map SupercuspidalRep.universeLift
    (fun _ _ ⟨e⟩ => ⟨SupercuspidalRep.universeLiftIso e⟩)

@[simp]
theorem universeLift_isoClass (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    universeLift A.isoClass = (SupercuspidalRep.universeLift A).isoClass := rfl

theorem universeLift_injective :
    Function.Injective
      (universeLift : SupercuspidalClass.{uV, uF} (F := F) (n := n) →
        SupercuspidalClass.{max uF uV, uF} (F := F) (n := n)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro A B h
  obtain ⟨e⟩ := Quotient.exact h
  exact Quotient.sound ⟨SupercuspidalRep.isoOfUniverseLiftIso e⟩

theorem universeLift_twist (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    universeLift (twist χ hχ hdet a) = twist χ hχ hdet (universeLift a) := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨SupercuspidalRep.universeLiftTwistIso χ hχ hdet A⟩

end SupercuspidalClass

end GeneralLinear

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem supercuspidalClassRealPowerTwist_universeLift (n : ℕ) (s : ℝ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.universeLift (T.supercuspidalClassRealPowerTwist n s a) =
      T.supercuspidalClassRealPowerTwist n s (GeneralLinear.SupercuspidalClass.universeLift a) :=
  letI := T.topology
  GeneralLinear.SupercuspidalClass.universeLift_twist _ _ _ a

namespace CuspidalDatum

/-- The cuspidal datum with carrier universe raised to `max uF uV`. -/
def universeLift (ρ : CuspidalDatum.{uV, uF} T) : CuspidalDatum.{max uF uV, uF} T where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := letI := T.topology
    GeneralLinear.SupercuspidalClass.universeLift ρ.cls

@[simp]
theorem universeLift_rank (ρ : CuspidalDatum.{uV, uF} T) : ρ.universeLift.rank = ρ.rank :=
  rfl

theorem universeLift_injective :
    Function.Injective (universeLift : CuspidalDatum.{uV, uF} T → CuspidalDatum.{max uF uV, uF} T) := by
  let := T.topology
  rintro ⟨r, hr, a⟩ ⟨r', hr', a'⟩ h
  simp only [universeLift, mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have := GeneralLinear.SupercuspidalClass.universeLift_injective (eq_of_heq h)
  subst this
  rfl

theorem universeLift_inj {ρ ρ' : CuspidalDatum.{uV, uF} T} :
    ρ.universeLift = ρ'.universeLift ↔ ρ = ρ' :=
  universeLift_injective.eq_iff

theorem universeLift_twist (s : ℝ) (ρ : CuspidalDatum.{uV, uF} T) :
    (ρ.twist s).universeLift = ρ.universeLift.twist s := by
  obtain ⟨r, hr, a⟩ := ρ
  exact congrArg (CuspidalDatum.mk r hr) (supercuspidalClassRealPowerTwist_universeLift r s a)

end CuspidalDatum

namespace Segment

/-- The segment with the same length and lifted beginning. -/
def universeLift (Δ : Segment.{uV, uF} T) : Segment.{max uF uV, uF} T where
  base := Δ.base.universeLift
  length := Δ.length
  length_pos := Δ.length_pos

@[simp]
theorem universeLift_base (Δ : Segment.{uV, uF} T) : Δ.universeLift.base = Δ.base.universeLift :=
  rfl

@[simp]
theorem universeLift_length (Δ : Segment.{uV, uF} T) : Δ.universeLift.length = Δ.length := rfl

@[simp]
theorem universeLift_rank (Δ : Segment.{uV, uF} T) : Δ.universeLift.rank = Δ.rank := rfl

@[simp]
theorem universeLift_degree (Δ : Segment.{uV, uF} T) : Δ.universeLift.degree = Δ.degree := rfl

theorem universeLift_injective :
    Function.Injective (universeLift : Segment.{uV, uF} T → Segment.{max uF uV, uF} T) := by
  rintro ⟨ρ, m, hm⟩ ⟨ρ', m', hm'⟩ h
  simp only [universeLift, mk.injEq, CuspidalDatum.universeLift_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem universeLift_inj {Δ Δ' : Segment.{uV, uF} T} :
    Δ.universeLift = Δ'.universeLift ↔ Δ = Δ' :=
  universeLift_injective.eq_iff

theorem universeLift_member (Δ : Segment.{uV, uF} T) (i : ℕ) :
    Δ.universeLift.member i = (Δ.member i).universeLift :=
  (CuspidalDatum.universeLift_twist _ _).symm

theorem universeLift_support (Δ : Segment.{uV, uF} T) :
    Δ.universeLift.support = CuspidalDatum.universeLift '' Δ.support := by
  ext ρ
  simp only [support, Set.mem_ofPred_eq, Set.mem_image, universeLift_length,
    universeLift_member]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Δ.member i, ⟨i, hi, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩

/-- Every segment whose beginning is a lift is the lift of a segment. -/
theorem exists_universeLift_eq (Δ' : Segment.{max uF uV, uF} T) (ρ : CuspidalDatum.{uV, uF} T)
    (hρ : Δ'.base = ρ.universeLift) : ∃ Δ : Segment.{uV, uF} T, Δ.universeLift = Δ' := by
  obtain ⟨ρ', m, hm⟩ := Δ'
  subst hρ
  exact ⟨⟨ρ, m, hm⟩, rfl⟩

theorem isLinked_universeLift_iff (Δ₁ Δ₂ : Segment.{uV, uF} T) :
    Δ₁.universeLift.IsLinked Δ₂.universeLift ↔ Δ₁.IsLinked Δ₂ := by
  have hinj := CuspidalDatum.universeLift_injective (T := T)
  simp only [IsLinked, universeLift_support, Set.image_subset_image_iff hinj]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨Δ', hΔ'⟩
    have hb : Δ'.base ∈ CuspidalDatum.universeLift '' (Δ₁.support ∪ Δ₂.support) := by
      rw [Set.image_union, ← hΔ']
      exact Δ'.base_mem_support
    obtain ⟨ρ, -, hρ⟩ := hb
    obtain ⟨Δ, rfl⟩ := exists_universeLift_eq Δ' ρ hρ.symm
    refine ⟨Δ, ?_⟩
    rw [universeLift_support, ← Set.image_union] at hΔ'
    exact (Set.image_injective.mpr hinj) hΔ'
  · rintro ⟨Δ, hΔ⟩
    exact ⟨Δ.universeLift, by rw [universeLift_support, hΔ, Set.image_union]⟩

theorem precedes_universeLift_iff (Δ₁ Δ₂ : Segment.{uV, uF} T) :
    Δ₁.universeLift.Precedes Δ₂.universeLift ↔ Δ₁.Precedes Δ₂ := by
  simp only [Precedes, isLinked_universeLift_iff, universeLift_base,
    ← CuspidalDatum.universeLift_twist, CuspidalDatum.universeLift_inj]

end Segment

theorem isPrecedenceOrdered_universeLift_iff {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) :
    T.IsPrecedenceOrdered (fun i => (Δ i).universeLift) ↔ T.IsPrecedenceOrdered Δ := by
  simp only [IsPrecedenceOrdered, Segment.precedes_universeLift_iff]

namespace Multisegment

/-- Lift every segment of a multisegment. -/
def universeLift (a : Multisegment.{uV, uF} T) : Multisegment.{max uF uV, uF} T :=
  a.map Segment.universeLift

theorem universeLift_injective :
    Function.Injective
      (universeLift : Multisegment.{uV, uF} T → Multisegment.{max uF uV, uF} T) :=
  Multiset.map_injective Segment.universeLift_injective

theorem universeLift_inj {a b : Multisegment.{uV, uF} T} :
    a.universeLift = b.universeLift ↔ a = b :=
  universeLift_injective.eq_iff

theorem universeLift_degree (a : Multisegment.{uV, uF} T) :
    a.universeLift.degree = a.degree := by
  simp only [degree, universeLift, Multiset.map_map]
  rfl

theorem universeLift_coe (l : List (Segment.{uV, uF} T)) :
    universeLift (l : Multisegment.{uV, uF} T) = ((l.map Segment.universeLift : List _) : Multiset _) :=
  Multiset.map_coe _ _

end Multisegment

section Induced

variable (T)

/-- The block factors of a lifted representative are equivalent to the
original ones. -/
def segmentFactorUniverseLiftEquiv {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (s : ℝ) :
    letI := T.topology
    (T.segmentFactor A s).representation.Equiv
      (T.segmentFactor (SmoothRep.universeLift.{uF} A) s).representation :=
  letI := T.topology
  twistEquiv _ (SmoothRep.universeLiftEquiv.{uF} A)

/-- `i(A, νA, …, ν^(m-1) A)` is equivalent to the induced representation of the
lifted representative. -/
def segmentInducedUniverseLiftEquiv {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    (T.segmentInduced A m hr).representation.Equiv
      (T.segmentInduced (SmoothRep.universeLift.{uF} A) m hr).representation :=
  letI := T.topology
  T.normalizedParabolicInducedEquiv (GeneralLinear.BlockShape.uniform m r hr)
    (FiniteTensorFiltration.externalCongr fun i =>
      T.segmentFactorUniverseLiftEquiv A ((i : ℕ) : ℝ))

variable {T}

theorem CuspidalDatum.universeLift_isRepresentedBy {ρ : CuspidalDatum.{uV, uF} T}
    {A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) :
    letI := T.topology
    ρ.universeLift.IsRepresentedBy (GeneralLinear.SupercuspidalRep.universeLift A) := by
  let := T.topology
  change (GeneralLinear.SupercuspidalRep.universeLift A).isoClass =
    GeneralLinear.SupercuspidalClass.universeLift ρ.cls
  rw [← hA]
  rfl

/-- Segment heads of a segment and of its lift are the same representations. -/
theorem isSegmentHead_universeLift_iff (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) :
    T.IsSegmentHead Δ.universeLift π ↔ T.IsSegmentHead Δ π := by
  let := T.topology
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  have hrep : Δ.base.IsRepresentedBy A := hA
  refine (T.isSegmentHead_iff Δ.universeLift π (GeneralLinear.SupercuspidalRep.universeLift A)
      (CuspidalDatum.universeLift_isRepresentedBy hrep)).trans ?_
  rw [T.isSegmentHead_iff Δ π A hrep]
  exact (Classification.isIrreducibleHead_iff_of_equiv
    (T.segmentInducedUniverseLiftEquiv A.obj Δ.length Δ.rank_pos)).symm

end Induced

namespace SegmentProductDatum

/-- The datum with lifted segments and the same blocks. -/
def universeLift {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    SegmentProductDatum.{max uF uV, uF} T n where
  length := d.length
  segments i := (d.segments i).universeLift
  degree_sum := d.degree_sum
  blocks := d.blocks

theorem universeLift_multisegment {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    d.universeLift.multisegment = d.multisegment.universeLift := by
  simp only [multisegment, universeLift, Multisegment.universeLift_coe, List.map_ofFn]
  rfl

theorem universeLift_isLanglandsHead_iff {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    d.universeLift.IsLanglandsHead π ↔ d.IsLanglandsHead π := by
  let := T.topology
  refine and_congr (isPrecedenceOrdered_universeLift_iff d.segments) (and_congr ?_ Iff.rfl)
  exact forall_congr' fun i => isSegmentHead_universeLift_iff (d.segments i) (d.blocks i)

/-- A datum whose segments are lifts is the lift of a datum. -/
theorem exists_universeLift_eq {n : ℕ} (d' : SegmentProductDatum.{max uF uV, uF} T n)
    (s : Fin d'.length → Segment.{uV, uF} T)
    (hs : ∀ i, d'.segments i = (s i).universeLift) :
    ∃ d : SegmentProductDatum.{uV, uF} T n, d.universeLift = d' := by
  obtain ⟨r, segs, hsum, blocks⟩ := d'
  change Fin r → Segment.{uV, uF} T at s
  change ∀ i, segs i = (s i).universeLift at hs
  obtain rfl : segs = fun i => (s i).universeLift := funext hs
  exact ⟨⟨r, s, hsum, blocks⟩, rfl⟩

end SegmentProductDatum

/-- A multisegment and its lift have the same Langlands heads. -/
theorem Multisegment.isLanglandsHead_universeLift_iff {n : ℕ} (a : Multisegment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    a.universeLift.IsLanglandsHead π ↔ a.IsLanglandsHead π := by
  constructor
  · rintro ⟨d', hd', hπ⟩
    have hmem : ∀ i, ∃ Δ : Segment.{uV, uF} T, Δ.universeLift = d'.segments i := by
      intro i
      have hi : d'.segments i ∈ d'.multisegment := by
        simp [SegmentProductDatum.multisegment, List.mem_ofFn]
      rw [hd'] at hi
      obtain ⟨Δ, -, hΔ⟩ := Multiset.mem_map.mp hi
      exact ⟨Δ, hΔ⟩
    choose s hs using hmem
    obtain ⟨d, rfl⟩ := SegmentProductDatum.exists_universeLift_eq d' s fun i => (hs i).symm
    refine ⟨d, ?_, (d.universeLift_isLanglandsHead_iff π).mp hπ⟩
    rw [SegmentProductDatum.universeLift_multisegment] at hd'
    exact Multisegment.universeLift_injective hd'
  · rintro ⟨d, rfl, hπ⟩
    exact ⟨d.universeLift, d.universeLift_multisegment, (d.universeLift_isLanglandsHead_iff π).mpr hπ⟩

end PadicField.TopologicalData

end Langlands

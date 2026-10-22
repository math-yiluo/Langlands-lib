import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Segments of supercuspidal classes and their special constituents

Zelevinsky's segments `[ρ, ν^(m-1) ρ]` of irreducible supercuspidal classes,
their linkage relations and multisegments. The representation
`i(ρ, νρ, …, ν^(m-1) ρ)` is normalized parabolic induction of the actual twists
of a representative. Its special constituent is recorded only by a relation:
neither existence nor uniqueness of an irreducible quotient is assumed.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uV uW uF

namespace Classification

variable {G : Type uG} [Group G]
variable {V V' W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]

/-- Irreducible quotients are transported along an actual equivalence of the source. -/
theorem IsIrreducibleQuotient.of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ')
    (h : IsIrreducibleQuotient ρ π) : IsIrreducibleQuotient ρ' π := by
  obtain ⟨hπ, q, hq⟩ := h
  refine ⟨hπ, q.comp e.symm.toIntertwiningMap, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := hq w
  exact ⟨e v, by simp [Representation.IntertwiningMap.comp_apply]⟩

theorem isIrreducibleQuotient_iff_of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ') :
    IsIrreducibleQuotient ρ π ↔ IsIrreducibleQuotient ρ' π :=
  ⟨IsIrreducibleQuotient.of_equiv e, IsIrreducibleQuotient.of_equiv e.symm⟩

/-- The irreducible head relation is transported along an actual equivalence of the
source; the uniqueness clause is carried by the kernels. -/
theorem IsIrreducibleHead.of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ')
    (h : IsIrreducibleHead ρ π) : IsIrreducibleHead ρ' π := by
  obtain ⟨hπ, q, hq, huniq⟩ := h
  refine ⟨hπ, q.comp e.symm.toIntertwiningMap, fun w => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hq w
    exact ⟨e v, by simp [Representation.IntertwiningMap.comp_apply]⟩
  · intro W' _ _ π' hπ' q' hq'
    have hsurj : Function.Surjective (q'.comp e.toIntertwiningMap) := fun w => by
      obtain ⟨v, rfl⟩ := hq' w
      exact ⟨e.symm v, by simp [Representation.IntertwiningMap.comp_apply]⟩
    have hker := huniq W' π' hπ' _ hsurj
    ext x
    have hx : e.symm x ∈ (q'.comp e.toIntertwiningMap).toLinearMap.ker ↔
        e.symm x ∈ q.toLinearMap.ker := by
      rw [hker]
    simpa [LinearMap.mem_ker, Representation.IntertwiningMap.comp_apply] using hx

theorem isIrreducibleHead_iff_of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ') :
    IsIrreducibleHead ρ π ↔ IsIrreducibleHead ρ' π :=
  ⟨IsIrreducibleHead.of_equiv e, IsIrreducibleHead.of_equiv e.symm⟩

/-- Irreducible subrepresentations are transported along an actual equivalence of
the ambient representation. -/
theorem IsIrreducibleSubrepresentation.of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ')
    (h : IsIrreducibleSubrepresentation ρ π) : IsIrreducibleSubrepresentation ρ' π := by
  obtain ⟨hπ, j, hj⟩ := h
  exact ⟨hπ, e.toIntertwiningMap.comp j, fun x y hxy => hj (e.injective hxy)⟩

theorem isIrreducibleSubrepresentation_iff_of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ') :
    IsIrreducibleSubrepresentation ρ π ↔ IsIrreducibleSubrepresentation ρ' π :=
  ⟨IsIrreducibleSubrepresentation.of_equiv e, IsIrreducibleSubrepresentation.of_equiv e.symm⟩

/-- The irreducible socle relation is transported along an actual equivalence of the
ambient representation; the uniqueness clause is carried by the images. -/
theorem IsIrreducibleSocle.of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ')
    (h : IsIrreducibleSocle ρ π) : IsIrreducibleSocle ρ' π := by
  obtain ⟨hπ, j, hj, huniq⟩ := h
  refine ⟨hπ, e.toIntertwiningMap.comp j, fun x y hxy => hj (e.injective hxy), ?_⟩
  intro W' _ _ π' hπ' j' hj'
  have hinj : Function.Injective (e.symm.toIntertwiningMap.comp j') :=
    fun x y hxy => hj' (e.symm.injective hxy)
  have hrange := huniq W' π' hπ' _ hinj
  ext x
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    have hw : e.symm (j' w) ∈ j.toLinearMap.range := by
      rw [← hrange]
      exact LinearMap.mem_range.mpr ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := LinearMap.mem_range.mp hw
    exact ⟨w', (congrArg (fun v => e v) hw').trans (e.apply_symm_apply _)⟩
  · rintro ⟨w, rfl⟩
    have hw : j w ∈ (e.symm.toIntertwiningMap.comp j').toLinearMap.range := by
      rw [hrange]
      exact LinearMap.mem_range.mpr ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := LinearMap.mem_range.mp hw
    exact ⟨w', (e.apply_symm_apply _).symm.trans (congrArg (fun v => e v) hw')⟩

theorem isIrreducibleSocle_iff_of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} (e : ρ.Equiv ρ') :
    IsIrreducibleSocle ρ π ↔ IsIrreducibleSocle ρ' π :=
  ⟨IsIrreducibleSocle.of_equiv e, IsIrreducibleSocle.of_equiv e.symm⟩

end Classification

namespace GeneralLinear

/-- The block shape `(r, …, r)` with `m` diagonal blocks of size `r`. -/
def BlockShape.uniform (m r : ℕ) (hr : 0 < r) : BlockShape (m * r) where
  length := m
  size _ := r
  positive _ := hr
  sum_eq := by simp

@[simp]
theorem BlockShape.uniform_length (m r : ℕ) (hr : 0 < r) :
    (BlockShape.uniform m r hr).length = m := rfl

@[simp]
theorem BlockShape.uniform_size (m r : ℕ) (hr : 0 < r)
    (i : Fin (BlockShape.uniform m r hr).length) :
    (BlockShape.uniform m r hr).size i = r := rfl

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- Twisting supercuspidal classes depends only on the character. -/
theorem SupercuspidalClass.twist_congr {χ η : GeneralLinear n F →* ℂˣ} (h : χ = η)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hη : IsOpen (η.ker : Set (GeneralLinear n F)))
    (hdetχ : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (hdetη : (determinant : GeneralLinear n F →* Fˣ).ker ≤ η.ker)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    SupercuspidalClass.twist χ hχ hdetχ a = SupercuspidalClass.twist η hη hdetη a := by
  subst h
  rfl

end GeneralLinear

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem supercuspidalClassRealPowerTwist_zero (n : ℕ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    T.supercuspidalClassRealPowerTwist n 0 a = a := by
  let := T.topology
  have h1 : IsOpen ((1 : GeneralLinear n F.Carrier →* ℂˣ).ker :
      Set (GeneralLinear n F.Carrier)) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  unfold supercuspidalClassRealPowerTwist
  rw [GeneralLinear.SupercuspidalClass.twist_congr (realPowerCharacter_zero _) _ h1 _
    GeneralLinear.ker_determinant_le_ker_one]
  exact GeneralLinear.SupercuspidalClass.twist_one h1 a

theorem supercuspidalClassRealPowerTwist_add (n : ℕ) (s t : ℝ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    T.supercuspidalClassRealPowerTwist n s (T.supercuspidalClassRealPowerTwist n t a) =
      T.supercuspidalClassRealPowerTwist n (s + t) a := by
  let := T.topology
  have hst : IsOpen ((T.determinantPowerCharacter n s * T.determinantPowerCharacter n t).ker :
      Set (GeneralLinear n F.Carrier)) := by
    rw [← realPowerCharacter_add]
    exact T.isOpen_ker_determinantPowerCharacter n (s + t)
  unfold supercuspidalClassRealPowerTwist
  rw [GeneralLinear.SupercuspidalClass.twist_twist _ _ _ _ hst]
  exact GeneralLinear.SupercuspidalClass.twist_congr (realPowerCharacter_add _ s t).symm _ _ _ _ a

/-- An element of Zelevinsky's set `𝒞`: the isomorphism class of an irreducible
supercuspidal representation of `GL_r(F)` for some `r ≥ 1`, with carriers in
`Type uV`. -/
structure CuspidalDatum where
  /-- The size `r` of the general linear group. -/
  rank : ℕ
  rank_pos : 0 < rank
  /-- The supercuspidal isomorphism class. -/
  cls : letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := rank)

namespace CuspidalDatum

variable {T}

/-- Zelevinsky's twist `ρ ↦ ν^s ρ`, with `ν = |det|` for the residue-normalized
absolute value. -/
def twist (s : ℝ) (ρ : CuspidalDatum.{uV, uF} T) : CuspidalDatum.{uV, uF} T where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := T.supercuspidalClassRealPowerTwist ρ.rank s ρ.cls

@[simp]
theorem twist_rank (s : ℝ) (ρ : CuspidalDatum.{uV, uF} T) : (ρ.twist s).rank = ρ.rank := rfl

@[simp]
theorem twist_zero (ρ : CuspidalDatum.{uV, uF} T) : ρ.twist 0 = ρ := by
  obtain ⟨r, hr, a⟩ := ρ
  simp only [twist, mk.injEq, heq_eq_eq, true_and]
  exact T.supercuspidalClassRealPowerTwist_zero r a

theorem twist_twist (s t : ℝ) (ρ : CuspidalDatum.{uV, uF} T) :
    (ρ.twist t).twist s = ρ.twist (s + t) := by
  obtain ⟨r, hr, a⟩ := ρ
  exact congrArg (CuspidalDatum.mk r hr) (T.supercuspidalClassRealPowerTwist_add r s t a)

end CuspidalDatum

/-- Zelevinsky's segment `[ρ, ν^(m-1) ρ] = {ρ, νρ, …, ν^(m-1) ρ}`, recorded by its
beginning `ρ` and its number `m ≥ 1` of elements. -/
structure Segment where
  /-- The beginning `ρ` of the segment. -/
  base : CuspidalDatum.{uV, uF} T
  /-- The number `m` of elements of the segment. -/
  length : ℕ
  length_pos : 0 < length

namespace Segment

variable {T}

/-- The common rank `r` of the supercuspidal classes in the segment. -/
abbrev rank (Δ : Segment.{uV, uF} T) : ℕ := Δ.base.rank

theorem rank_pos (Δ : Segment.{uV, uF} T) : 0 < Δ.rank := Δ.base.rank_pos

/-- The size `m r` of the general linear group carrying `i(ρ, νρ, …, ν^(m-1) ρ)`. -/
abbrev degree (Δ : Segment.{uV, uF} T) : ℕ := Δ.length * Δ.rank

theorem degree_pos (Δ : Segment.{uV, uF} T) : 0 < Δ.degree :=
  Nat.mul_pos Δ.length_pos Δ.rank_pos

/-- The element `ν^i ρ`. -/
def member (Δ : Segment.{uV, uF} T) (i : ℕ) : CuspidalDatum.{uV, uF} T :=
  Δ.base.twist (i : ℝ)

@[simp]
theorem member_zero (Δ : Segment.{uV, uF} T) : Δ.member 0 = Δ.base := by
  simp [member]

/-- The end `ν^(m-1) ρ` of the segment. -/
def last (Δ : Segment.{uV, uF} T) : CuspidalDatum.{uV, uF} T :=
  Δ.member (Δ.length - 1)

/-- The segment as a subset of `𝒞`. -/
def support (Δ : Segment.{uV, uF} T) : Set (CuspidalDatum.{uV, uF} T) :=
  {ρ | ∃ i < Δ.length, Δ.member i = ρ}

theorem member_mem_support (Δ : Segment.{uV, uF} T) {i : ℕ} (hi : i < Δ.length) :
    Δ.member i ∈ Δ.support := ⟨i, hi, rfl⟩

theorem base_mem_support (Δ : Segment.{uV, uF} T) : Δ.base ∈ Δ.support := by
  simpa using Δ.member_mem_support Δ.length_pos

theorem last_mem_support (Δ : Segment.{uV, uF} T) : Δ.last ∈ Δ.support :=
  Δ.member_mem_support (Nat.sub_lt Δ.length_pos Nat.one_pos)

/-- The twisted segment `ν^s Δ = [ν^s ρ, ν^(s+m-1) ρ]`. -/
def twist (s : ℝ) (Δ : Segment.{uV, uF} T) : Segment.{uV, uF} T where
  base := Δ.base.twist s
  length := Δ.length
  length_pos := Δ.length_pos

@[simp]
theorem twist_length (s : ℝ) (Δ : Segment.{uV, uF} T) : (Δ.twist s).length = Δ.length := rfl

@[simp]
theorem twist_rank (s : ℝ) (Δ : Segment.{uV, uF} T) : (Δ.twist s).rank = Δ.rank := rfl

@[simp]
theorem twist_zero (Δ : Segment.{uV, uF} T) : Δ.twist 0 = Δ := by
  simp [twist]

theorem twist_twist (s t : ℝ) (Δ : Segment.{uV, uF} T) :
    (Δ.twist t).twist s = Δ.twist (s + t) := by
  simp [twist, CuspidalDatum.twist_twist]

theorem member_twist (s : ℝ) (Δ : Segment.{uV, uF} T) (i : ℕ) :
    (Δ.twist s).member i = (Δ.member i).twist s := by
  simp only [member, twist, CuspidalDatum.twist_twist, add_comm]

/-- Zelevinsky's linkage: neither segment contains the other and their union is a
segment. -/
def IsLinked (Δ₁ Δ₂ : Segment.{uV, uF} T) : Prop :=
  ¬ Δ₁.support ⊆ Δ₂.support ∧ ¬ Δ₂.support ⊆ Δ₁.support ∧
    ∃ Δ : Segment.{uV, uF} T, Δ.support = Δ₁.support ∪ Δ₂.support

theorem IsLinked.symm {Δ₁ Δ₂ : Segment.{uV, uF} T} (h : Δ₁.IsLinked Δ₂) :
    Δ₂.IsLinked Δ₁ := by
  obtain ⟨h₁, h₂, Δ, hΔ⟩ := h
  exact ⟨h₂, h₁, Δ, hΔ.trans (Set.union_comm _ _)⟩

theorem isLinked_comm (Δ₁ Δ₂ : Segment.{uV, uF} T) : Δ₁.IsLinked Δ₂ ↔ Δ₂.IsLinked Δ₁ :=
  ⟨IsLinked.symm, IsLinked.symm⟩

theorem not_isLinked_self (Δ : Segment.{uV, uF} T) : ¬ Δ.IsLinked Δ :=
  fun h => h.1 subset_rfl

/-- Linked segments with disjoint supports. -/
def IsJuxtaposed (Δ₁ Δ₂ : Segment.{uV, uF} T) : Prop :=
  Δ₁.IsLinked Δ₂ ∧ Disjoint Δ₁.support Δ₂.support

/-- `Δ₁` precedes `Δ₂`: they are linked and the beginning of `Δ₂` is `ν^k` times
the beginning of `Δ₁` for some integer `k > 0`. -/
def Precedes (Δ₁ Δ₂ : Segment.{uV, uF} T) : Prop :=
  Δ₁.IsLinked Δ₂ ∧ ∃ k : ℕ, 0 < k ∧ Δ₂.base = Δ₁.base.twist (k : ℝ)

theorem Precedes.isLinked {Δ₁ Δ₂ : Segment.{uV, uF} T} (h : Δ₁.Precedes Δ₂) :
    Δ₁.IsLinked Δ₂ := h.1

end Segment

/-- Finite multisets of segments, the empty multiset included. -/
abbrev Multisegment := Multiset (Segment.{uV, uF} T)

namespace Multisegment

variable {T}

/-- The size `∑ m_i r_i` of the general linear group of the multisegment. -/
def degree (a : Multisegment.{uV, uF} T) : ℕ := (a.map Segment.degree).sum

/-- Twist every segment by `ν^s`. -/
def twist (s : ℝ) (a : Multisegment.{uV, uF} T) : Multisegment.{uV, uF} T :=
  a.map (Segment.twist s)

/-- A finite sequence of segments lists the multisegment with multiplicities. -/
def IsOrdering (a : Multisegment.{uV, uF} T) {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) :
    Prop :=
  (List.ofFn Δ : Multiset (Segment.{uV, uF} T)) = a

/-- A list of segments lists the multisegment with multiplicities. -/
def IsListOrdering (a : Multisegment.{uV, uF} T) (l : List (Segment.{uV, uF} T)) : Prop :=
  (l : Multiset (Segment.{uV, uF} T)) = a

theorem isOrdering_iff_isListOrdering (a : Multisegment.{uV, uF} T) {r : ℕ}
    (Δ : Fin r → Segment.{uV, uF} T) : a.IsOrdering Δ ↔ a.IsListOrdering (List.ofFn Δ) :=
  Iff.rfl

/-- No two segments of the multisegment are linked. -/
def IsUnlinked (a : Multisegment.{uV, uF} T) : Prop :=
  ∀ Δ₁ ∈ a, ∀ Δ₂ ∈ a, ¬ Δ₁.IsLinked Δ₂

end Multisegment

/-- A finite sequence of segments in which no earlier segment precedes a later one. -/
def IsPrecedenceOrdered {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) : Prop :=
  ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)

/-- A list of segments in which no earlier segment precedes a later one. -/
def IsPrecedenceOrderedList (l : List (Segment.{uV, uF} T)) : Prop :=
  l.Pairwise fun Δ₁ Δ₂ => ¬ Δ₁.Precedes Δ₂

theorem isPrecedenceOrdered_iff_list {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) :
    T.IsPrecedenceOrdered Δ ↔ T.IsPrecedenceOrderedList (List.ofFn Δ) := by
  unfold IsPrecedenceOrdered IsPrecedenceOrderedList
  rw [List.pairwise_ofFn]

section Induced

variable {r : ℕ}

/-- The block factor `ν^s A = A ⊗ |det|^s`. -/
abbrev segmentFactor
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (s : ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier) :=
  letI := T.topology
  A.twist (T.determinantPowerCharacter r s) (T.isOpen_ker_determinantPowerCharacter r s)

/-- The block factors `(A, νA, …, ν^(m-1) A)` of `uniform m r`. -/
def segmentFactors
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    ∀ i : Fin (GeneralLinear.BlockShape.uniform m r hr).length,
      SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((GeneralLinear.BlockShape.uniform m r hr).size i) F.Carrier) :=
  fun i => T.segmentFactor A ((i : ℕ) : ℝ)

/-- `i(A, νA, …, ν^(m-1) A)` on `GL_{mr}(F)`: normalized parabolic induction from
the standard upper block parabolic with `m` blocks of size `r`. -/
def segmentInduced
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (GeneralLinear.BlockShape.uniform m r hr)).obj
    (T.segmentFactors A m hr)

theorem segmentInduced_representation
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    (T.segmentInduced A m hr).representation =
      T.normalizedProductInduced (GeneralLinear.BlockShape.uniform m r hr)
        (fun i => (T.segmentFactors A m hr i).representation) := rfl

/-- An isomorphism of representatives gives an isomorphism of induced representations. -/
def segmentInducedIso
    {A A' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)}
    (e : A ≅ A') (m : ℕ) (hr : 0 < r) :
    T.segmentInduced A m hr ≅ T.segmentInduced A' m hr :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (GeneralLinear.BlockShape.uniform m r hr)).mapIso
    (Pi.isoMk fun i => SmoothRep.twistIso _
      (T.isOpen_ker_determinantPowerCharacter r ((i : ℕ) : ℝ)) e)

/-- The block factors `(ν^(m-1) A, …, νA, A)` of `uniform m r`, in decreasing order. -/
def segmentFactorsDown
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    ∀ i : Fin (GeneralLinear.BlockShape.uniform m r hr).length,
      SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((GeneralLinear.BlockShape.uniform m r hr).size i) F.Carrier) :=
  fun i => T.segmentFactor A ((m - 1 - (i : ℕ) : ℕ) : ℝ)

/-- `i(ν^(m-1) A, …, νA, A)` on `GL_{mr}(F)`, the decreasing order. -/
def segmentInducedDown
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (GeneralLinear.BlockShape.uniform m r hr)).obj
    (T.segmentFactorsDown A m hr)

theorem segmentInducedDown_representation
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    (T.segmentInducedDown A m hr).representation =
      T.normalizedProductInduced (GeneralLinear.BlockShape.uniform m r hr)
        (fun i => (T.segmentFactorsDown A m hr i).representation) := rfl

/-- An isomorphism of representatives gives an isomorphism of the decreasing-order
induced representations. -/
def segmentInducedDownIso
    {A A' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)}
    (e : A ≅ A') (m : ℕ) (hr : 0 < r) :
    T.segmentInducedDown A m hr ≅ T.segmentInducedDown A' m hr :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (GeneralLinear.BlockShape.uniform m r hr)).mapIso
    (Pi.isoMk fun i => SmoothRep.twistIso _
      (T.isOpen_ker_determinantPowerCharacter r ((m - 1 - (i : ℕ) : ℕ) : ℝ)) e)

end Induced

variable {T} in
/-- The actual supercuspidal representatives of a cuspidal datum. -/
def CuspidalDatum.IsRepresentedBy (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)) : Prop :=
  letI := T.topology
  A.isoClass = ρ.cls

/-- `π` is an irreducible quotient of `i(ρ, νρ, …, ν^(m-1) ρ)` for an actual
supercuspidal representative `ρ` of the beginning of `Δ`. This is the relation
satisfied by the special representation `St_m(ρ)`; it asserts neither existence
nor uniqueness. -/
def IsSegmentQuotient (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) : Prop :=
  letI := T.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
    Δ.base.IsRepresentedBy A ∧
      Classification.IsIrreducibleQuotient
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation

/-- The irreducible head form: `π` is an irreducible quotient of
`i(ρ, νρ, …, ν^(m-1) ρ)` and every irreducible quotient map has the same kernel. -/
def IsSegmentHead (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) : Prop :=
  letI := T.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
    Δ.base.IsRepresentedBy A ∧
      Classification.IsIrreducibleHead
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation

/-- `π` is an irreducible subrepresentation of `i(ρ, νρ, …, ν^(m-1) ρ)` for an
actual supercuspidal representative `ρ` of the beginning of `Δ`. This is the relation
satisfied by Zelevinsky's `⟨Δ⟩`; it asserts neither existence nor uniqueness. -/
def IsSegmentSubrepresentation (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) : Prop :=
  letI := T.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
    Δ.base.IsRepresentedBy A ∧
      Classification.IsIrreducibleSubrepresentation
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation

/-- The irreducible socle form: `π` is an irreducible subrepresentation of
`i(ρ, νρ, …, ν^(m-1) ρ)` and every irreducible embedding has the same image. -/
def IsSegmentSocle (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) : Prop :=
  letI := T.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
    Δ.base.IsRepresentedBy A ∧
      Classification.IsIrreducibleSocle
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation

/-- Two representatives of the same class induce isomorphic representations. -/
def segmentInducedIsoOfRepresented {ρ : CuspidalDatum.{uV, uF} T}
    {A A' : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) (hA' : ρ.IsRepresentedBy A') (m : ℕ) :
    T.segmentInduced A.obj m ρ.rank_pos ≅ T.segmentInduced A'.obj m ρ.rank_pos :=
  letI := T.topology
  T.segmentInducedIso
    ((GeneralLinear.supercuspidalProperty (F := F.Carrier) (n := ρ.rank)).ι.mapIso
      (Classical.choice
        ((GeneralLinear.SupercuspidalRep.isoClass_eq_iff A A').mp (hA.trans hA'.symm))))
    m ρ.rank_pos

/-- Two representatives of the same class induce isomorphic decreasing-order
representations. -/
def segmentInducedDownIsoOfRepresented {ρ : CuspidalDatum.{uV, uF} T}
    {A A' : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) (hA' : ρ.IsRepresentedBy A') (m : ℕ) :
    T.segmentInducedDown A.obj m ρ.rank_pos ≅ T.segmentInducedDown A'.obj m ρ.rank_pos :=
  letI := T.topology
  T.segmentInducedDownIso
    ((GeneralLinear.supercuspidalProperty (F := F.Carrier) (n := ρ.rank)).ι.mapIso
      (Classical.choice
        ((GeneralLinear.SupercuspidalRep.isoClass_eq_iff A A').mp (hA.trans hA'.symm))))
    m ρ.rank_pos

/-- The segment-quotient relation does not depend on the chosen representative. -/
theorem isSegmentQuotient_iff (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    T.IsSegmentQuotient Δ π ↔
      Classification.IsIrreducibleQuotient
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation := by
  let := T.topology
  constructor
  · rintro ⟨A', hA', h⟩
    exact h.of_equiv
      (SmoothRep.equivOfIso (T.segmentInducedIsoOfRepresented hA' hA Δ.length))
  · exact fun h => ⟨A, hA, h⟩

/-- The segment-head relation does not depend on the chosen representative. -/
theorem isSegmentHead_iff (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    T.IsSegmentHead Δ π ↔
      Classification.IsIrreducibleHead
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation := by
  let := T.topology
  constructor
  · rintro ⟨A', hA', h⟩
    exact h.of_equiv
      (SmoothRep.equivOfIso (T.segmentInducedIsoOfRepresented hA' hA Δ.length))
  · exact fun h => ⟨A, hA, h⟩

/-- The segment-subrepresentation relation does not depend on the chosen representative. -/
theorem isSegmentSubrepresentation_iff (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    T.IsSegmentSubrepresentation Δ π ↔
      Classification.IsIrreducibleSubrepresentation
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation := by
  let := T.topology
  constructor
  · rintro ⟨A', hA', h⟩
    exact h.of_equiv
      (SmoothRep.equivOfIso (T.segmentInducedIsoOfRepresented hA' hA Δ.length))
  · exact fun h => ⟨A, hA, h⟩

/-- The segment-socle relation does not depend on the chosen representative. -/
theorem isSegmentSocle_iff (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    T.IsSegmentSocle Δ π ↔
      Classification.IsIrreducibleSocle
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation := by
  let := T.topology
  constructor
  · rintro ⟨A', hA', h⟩
    exact h.of_equiv
      (SmoothRep.equivOfIso (T.segmentInducedIsoOfRepresented hA' hA Δ.length))
  · exact fun h => ⟨A, hA, h⟩

theorem IsSegmentHead.isSegmentQuotient {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentHead Δ π) : T.IsSegmentQuotient Δ π := by
  obtain ⟨A, hA, hπ, q, hq, -⟩ := h
  exact ⟨A, hA, hπ, q, hq⟩

theorem IsSegmentSocle.isSegmentSubrepresentation {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) : T.IsSegmentSubrepresentation Δ π := by
  obtain ⟨A, hA, hπ, j, hj, -⟩ := h
  exact ⟨A, hA, hπ, j, hj⟩

end PadicField.TopologicalData

end Langlands

import Langlands.Representation.Classification.MultisegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.SegmentConstituentCharacterTwistCompatibilityProof
import Langlands.Representation.Classification.HeadTargetTransport
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle

/-! # Character twists of multisegment socles and Langlands heads -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The product of two characters with open kernels has open kernel. -/
theorem isOpen_ker_mul_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {χ η : G →* ℂˣ} (hχ : IsOpen (χ.ker : Set G))
    (hη : IsOpen (η.ker : Set G)) : IsOpen ((χ * η).ker : Set G) := by
  apply Subgroup.isOpen_mono (H₁ := χ.ker ⊓ η.ker)
  · intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hg.1, hg.2, mul_one]
  · exact hχ.inter hη

/-- The inverse of a character with open kernel has open kernel. -/
theorem isOpen_ker_inv_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    {χ : G →* ℂˣ} (hχ : IsOpen (χ.ker : Set G)) : IsOpen ((χ⁻¹).ker : Set G) := by
  have h : (χ⁻¹).ker = χ.ker := by
    ext g
    simp
  rw [h]
  exact hχ

/-- `isOpen_ker_inv_of_isOpen` for the topology of `F^×` given by `T`. -/
theorem isOpen_ker_inv_units (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ)) :
    letI := T.topology
    IsOpen ((χ⁻¹).ker : Set F.Carrierˣ) := by
  let := T.topology
  exact isOpen_ker_inv_of_isOpen hχ

/-- Twists of supercuspidal classes by two characters commute. -/
theorem supercuspidalClass_twist_comm {K : Type uF} [Field K] [TopologicalSpace K] {n : ℕ}
    (χ η : GeneralLinear n K →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n K)))
    (hη : IsOpen (η.ker : Set (GeneralLinear n K)))
    (hχη : IsOpen ((χ * η).ker : Set (GeneralLinear n K)))
    (hηχ : IsOpen ((η * χ).ker : Set (GeneralLinear n K)))
    (hdetχ : (determinant : GeneralLinear n K →* Kˣ).ker ≤ χ.ker)
    (hdetη : (determinant : GeneralLinear n K →* Kˣ).ker ≤ η.ker)
    (a : SupercuspidalClass.{uV, uF} (F := K) (n := n)) :
    SupercuspidalClass.twist χ hχ hdetχ (SupercuspidalClass.twist η hη hdetη a) =
      SupercuspidalClass.twist η hη hdetη (SupercuspidalClass.twist χ hχ hdetχ a) := by
  rw [SupercuspidalClass.twist_twist _ _ _ _ hχη, SupercuspidalClass.twist_twist _ _ _ _ hηχ]
  exact SupercuspidalClass.twist_congr (mul_comm _ _) _ _ _ _ a

/-- Twisting by `χ⁻¹` undoes twisting by `χ` on supercuspidal classes. -/
theorem supercuspidalClass_twist_inv_twist {K : Type uF} [Field K] [TopologicalSpace K]
    {n : ℕ} (χ : GeneralLinear n K →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n K)))
    (hχ' : IsOpen ((χ⁻¹).ker : Set (GeneralLinear n K)))
    (h1 : IsOpen ((χ⁻¹ * χ).ker : Set (GeneralLinear n K)))
    (hdetχ : (determinant : GeneralLinear n K →* Kˣ).ker ≤ χ.ker)
    (hdetχ' : (determinant : GeneralLinear n K →* Kˣ).ker ≤ (χ⁻¹).ker)
    (a : SupercuspidalClass.{uV, uF} (F := K) (n := n)) :
    SupercuspidalClass.twist χ⁻¹ hχ' hdetχ' (SupercuspidalClass.twist χ hχ hdetχ a) = a := by
  have hone : χ⁻¹ * χ = 1 := inv_mul_cancel χ
  have hopen1 : IsOpen ((1 : GeneralLinear n K →* ℂˣ).ker : Set (GeneralLinear n K)) := by
    rw [← hone]
    exact h1
  rw [SupercuspidalClass.twist_twist _ _ _ _ h1,
    SupercuspidalClass.twist_congr hone _ hopen1 _ ker_determinant_le_ker_one a]
  exact SupercuspidalClass.twist_one hopen1 a

section CharacterTwist

variable (χ : F.Carrierˣ →* ℂˣ)
  (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ))

/-- Twist of a cuspidal datum `ρ` of rank `r` by the character `χ ∘ det` of
`GL_r(F)`. -/
def cuspidalCharacterTwist (ρ : T.CuspidalDatum.{uV, uF}) : T.CuspidalDatum.{uV, uF} :=
  letI := T.topology
  { rank := ρ.rank
    rank_pos := ρ.rank_pos
    cls := SupercuspidalClass.twist
      (χ.comp (determinant : GeneralLinear ρ.rank F.Carrier →* F.Carrierˣ))
      (hχ.preimage (T.generalLinearDeterminant ρ.rank).continuous)
      (ker_determinant_le_ker_comp χ) ρ.cls }

/-- Twist of a segment by `χ ∘ det`: the base is twisted and the length kept.
This is the `twistSegment` of `MultisegmentConstituentCharacterTwistCompatibility`. -/
def segmentCharacterTwist (Δ : T.Segment.{uV, uF}) : T.Segment.{uV, uF} where
  base := cuspidalCharacterTwist χ hχ Δ.base
  length := Δ.length
  length_pos := Δ.length_pos

/-- Character twists commute with the real twists `ν^s`. -/
theorem cuspidalCharacterTwist_twist (s : ℝ) (ρ : T.CuspidalDatum.{uV, uF}) :
    cuspidalCharacterTwist χ hχ (ρ.twist s) = (cuspidalCharacterTwist χ hχ ρ).twist s := by
  let := T.topology
  obtain ⟨r, hr, a⟩ := ρ
  have := T.generalLinearTopologicalGroup r
  have hdχ : IsOpen ((χ.comp (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)).ker :
      Set (GeneralLinear r F.Carrier)) :=
    hχ.preimage (T.generalLinearDeterminant r).continuous
  have hs := T.isOpen_ker_determinantPowerCharacter r s
  apply congrArg (CuspidalDatum.mk r hr)
  exact supercuspidalClass_twist_comm _ _ hdχ hs (isOpen_ker_mul_of_isOpen hdχ hs)
    (isOpen_ker_mul_of_isOpen hs hdχ) (ker_determinant_le_ker_comp χ)
    (T.ker_determinant_le_ker_determinantPowerCharacter r s) a

/-- Twisting by `χ⁻¹ ∘ det` undoes twisting by `χ ∘ det`. -/
theorem cuspidalCharacterTwist_inv_twist (ρ : T.CuspidalDatum.{uV, uF}) :
    cuspidalCharacterTwist χ⁻¹ (isOpen_ker_inv_units χ hχ)
      (cuspidalCharacterTwist χ hχ ρ) = ρ := by
  let := T.topology
  obtain ⟨r, hr, a⟩ := ρ
  have := T.generalLinearTopologicalGroup r
  have hdχ : IsOpen ((χ.comp (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)).ker :
      Set (GeneralLinear r F.Carrier)) :=
    hχ.preimage (T.generalLinearDeterminant r).continuous
  have hdχ' : IsOpen ((χ⁻¹.comp (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)).ker :
      Set (GeneralLinear r F.Carrier)) :=
    (isOpen_ker_inv_units χ hχ).preimage (T.generalLinearDeterminant r).continuous
  apply congrArg (CuspidalDatum.mk r hr)
  exact supercuspidalClass_twist_inv_twist _ hdχ hdχ' (isOpen_ker_mul_of_isOpen hdχ' hdχ)
    (ker_determinant_le_ker_comp χ) (ker_determinant_le_ker_comp χ⁻¹) a

theorem segmentCharacterTwist_inv_twist (Δ : T.Segment.{uV, uF}) :
    segmentCharacterTwist χ⁻¹ (isOpen_ker_inv_units χ hχ)
      (segmentCharacterTwist χ hχ Δ) = Δ := by
  obtain ⟨ρ, m, hm⟩ := Δ
  exact congrArg (fun ρ' => Segment.mk ρ' m hm) (cuspidalCharacterTwist_inv_twist χ hχ ρ)

theorem cuspidalCharacterTwist_injective :
    Function.Injective (cuspidalCharacterTwist.{uF, uV} (T := T) χ hχ) :=
  Function.LeftInverse.injective (cuspidalCharacterTwist_inv_twist χ hχ)

theorem member_segmentCharacterTwist (Δ : T.Segment.{uV, uF}) (i : ℕ) :
    (segmentCharacterTwist χ hχ Δ).member i = cuspidalCharacterTwist χ hχ (Δ.member i) :=
  (cuspidalCharacterTwist_twist χ hχ (i : ℝ) Δ.base).symm

theorem support_segmentCharacterTwist (Δ : T.Segment.{uV, uF}) :
    (segmentCharacterTwist χ hχ Δ).support = cuspidalCharacterTwist χ hχ '' Δ.support := by
  ext ρ
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Δ.member i, Δ.member_mem_support hi,
      (member_segmentCharacterTwist χ hχ Δ i).symm⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, member_segmentCharacterTwist χ hχ Δ i⟩

/-- Character twists preserve the precedence relation. -/
theorem precedes_segmentCharacterTwist {Δ₁ Δ₂ : T.Segment.{uV, uF}}
    (h : Δ₁.Precedes Δ₂) :
    (segmentCharacterTwist χ hχ Δ₁).Precedes (segmentCharacterTwist χ hχ Δ₂) := by
  obtain ⟨⟨h₁, h₂, Δ, hΔ⟩, k, hk, hb⟩ := h
  have hinj := cuspidalCharacterTwist_injective χ hχ
  refine ⟨⟨?_, ?_, segmentCharacterTwist χ hχ Δ, ?_⟩, k, hk, ?_⟩
  · rw [support_segmentCharacterTwist, support_segmentCharacterTwist,
      Set.image_subset_image_iff hinj]
    exact h₁
  · rw [support_segmentCharacterTwist, support_segmentCharacterTwist,
      Set.image_subset_image_iff hinj]
    exact h₂
  · rw [support_segmentCharacterTwist, support_segmentCharacterTwist,
      support_segmentCharacterTwist, hΔ, Set.image_union]
  · change cuspidalCharacterTwist χ hχ Δ₂.base =
      (cuspidalCharacterTwist χ hχ Δ₁.base).twist (k : ℝ)
    rw [hb, cuspidalCharacterTwist_twist]

/-- Character twists reflect the precedence relation. -/
theorem precedes_of_segmentCharacterTwist {Δ₁ Δ₂ : T.Segment.{uV, uF}}
    (h : (segmentCharacterTwist χ hχ Δ₁).Precedes (segmentCharacterTwist χ hχ Δ₂)) :
    Δ₁.Precedes Δ₂ := by
  have h' := precedes_segmentCharacterTwist χ⁻¹ (isOpen_ker_inv_units χ hχ) h
  rwa [segmentCharacterTwist_inv_twist, segmentCharacterTwist_inv_twist] at h'

/-- Twist every segment by `χ ∘ det` and every block by the character `χ ∘ det`
of its own general linear group. -/
def datumCharacterTwist {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    SegmentProductDatum.{uV, uF} T n := by
  letI := T.topology
  exact {
    length := d.length
    segments := fun i => segmentCharacterTwist χ hχ (d.segments i)
    degree_sum := d.degree_sum
    blocks := fun i => (d.blocks i).twist (χ.comp determinant)
      (hχ.preimage (T.generalLinearDeterminant (d.segments i).degree).continuous) }

theorem datumCharacterTwist_shape {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    (datumCharacterTwist χ hχ d).shape = d.shape := rfl

theorem datumCharacterTwist_blocks {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (i : Fin d.length) :
    letI := T.topology
    ((datumCharacterTwist χ hχ d).blocks i).representation =
      twist (χ.comp determinant) (d.blocks i).representation := rfl

theorem datumCharacterTwist_induced {n : ℕ}
    (d : SegmentProductDatum.{uV, uF} T n) :
    letI := T.topology
    (datumCharacterTwist χ hχ d).induced =
      (T.normalizedProductInductionFunctor d.shape).obj (fun i => (d.blocks i).twist
        (χ.comp determinant)
        (hχ.preimage (T.generalLinearDeterminant (d.segments i).degree).continuous)) := rfl

theorem multisegment_datumCharacterTwist {n : ℕ}
    (d : SegmentProductDatum.{uV, uF} T n) :
    (datumCharacterTwist χ hχ d).multisegment =
      d.multisegment.map (segmentCharacterTwist χ hχ) := by
  change ((List.ofFn fun i => segmentCharacterTwist χ hχ (d.segments i) :
      List (T.Segment.{uV, uF})) : Multiset (T.Segment.{uV, uF})) =
    Multiset.map (segmentCharacterTwist χ hχ) (List.ofFn d.segments : Multiset _)
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

theorem isPrecedenceOrdered_datumCharacterTwist {n : ℕ}
    {d : SegmentProductDatum.{uV, uF} T n} (h : d.IsPrecedenceOrdered) :
    (datumCharacterTwist χ hχ d).IsPrecedenceOrdered :=
  fun i j hij hp => h i j hij (precedes_of_segmentCharacterTwist χ hχ hp)

/-- The induced object of the twisted datum is isomorphic to the twist of the
induced object of the original datum: multiplication of induced functions by
`χ(det g)`. -/
def datumCharacterTwistInducedIso {n : ℕ}
    (d : SegmentProductDatum.{uV, uF} T n) :
    letI := T.topology
    d.induced.twist (χ.comp determinant)
        (hχ.preimage (T.generalLinearDeterminant n).continuous) ≅
      (datumCharacterTwist χ hχ d).induced := by
  letI := T.topology
  rw [datumCharacterTwist_induced]
  exact SmoothRep.mkIso (T.normalizedProductDeterminantTwistEquiv d.shape ⟨χ, hχ⟩
    (fun i => (d.blocks i).representation))

/-- `datumCharacterTwistInducedIso` as an equivalence of actual actions. -/
def datumCharacterTwistInducedEquiv {n : ℕ}
    (d : SegmentProductDatum.{uV, uF} T n) :
    letI := T.topology
    (twist (χ.comp determinant) d.induced.representation).Equiv
      (datumCharacterTwist χ hχ d).induced.representation :=
  letI := T.topology
  SmoothRep.equivOfIso (datumCharacterTwistInducedIso χ hχ d)

/-- Forward direction: a character twist carries the socle and head relations
of `a` and `π` to those of the twisted multisegment and any representation
equivalent to the twist of `π`. -/
theorem characterTwist_forward (n : ℕ) (a : T.Multisegment.{uV, uF}) :
    letI := T.topology
    ∀ (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      (twist (χ.comp (determinant : GeneralLinear n F.Carrier →* F.Carrierˣ))
        π.representation).Equiv π'.representation →
      (Multisegment.IsZelevinskySocle a π →
          Multisegment.IsZelevinskySocle (a.map (segmentCharacterTwist χ hχ)) π') ∧
        (Multisegment.IsLanglandsHead a π →
          Multisegment.IsLanglandsHead (a.map (segmentCharacterTwist χ hχ)) π') := by
  let := T.topology
  intro π π' e
  have hseg (Δ : T.Segment.{uV, uF})
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) :=
    segmentConstituentCharacterTwistCompatibility.{uF, uV} F T Δ χ
      (hχ.preimage (T.generalLinearDeterminant Δ.rank).continuous)
      (hχ.preimage (T.generalLinearDeterminant Δ.degree).continuous) σ
  constructor
  · rintro ⟨d, rfl, ho, hs, hπ⟩
    refine ⟨datumCharacterTwist χ hχ d, multisegment_datumCharacterTwist χ hχ d,
      isPrecedenceOrdered_datumCharacterTwist χ hχ ho,
      fun i => (hseg (d.segments i) (d.blocks i)).1.mp (hs i), ?_⟩
    exact (((isIrreducibleSocle_twist_iff _ _ _).mpr hπ).of_equiv
      (datumCharacterTwistInducedEquiv χ hχ d)).of_targetEquiv e
  · rintro ⟨d, rfl, ho, hh, hπ⟩
    refine ⟨datumCharacterTwist χ hχ d, multisegment_datumCharacterTwist χ hχ d,
      isPrecedenceOrdered_datumCharacterTwist χ hχ ho,
      fun i => (hseg (d.segments i) (d.blocks i)).2.1.mp (hh i), ?_⟩
    exact (((isIrreducibleHead_twist_iff _ _ _).mpr hπ).of_equiv
      (datumCharacterTwistInducedEquiv χ hχ d)).of_targetEquiv e

end CharacterTwist

variable (F T)

/-- Twisting by a smooth character of `F^×` composed with the determinant
preserves and reflects the multisegment socle and Langlands head relations. -/
theorem multisegmentConstituentCharacterTwistCompatibility :
    MultisegmentConstituentCharacterTwistCompatibility.{uF, uV} F T := by
  let := T.topology
  intro χ hχ hdet twistSegment n hn a π aχ πχ
  have hχ' := isOpen_ker_inv_units χ hχ
  have fwd := characterTwist_forward χ hχ n a π πχ (equivOfRepresentationEq rfl)
  have hπ : twist (χ⁻¹.comp (determinant : GeneralLinear n F.Carrier →* F.Carrierˣ))
      πχ.representation = π.representation := by
    change twist (χ⁻¹.comp determinant) (twist (χ.comp determinant) π.representation) =
      π.representation
    rw [MonoidHom.inv_comp, twist_inv_twist]
  have bwd := characterTwist_forward χ⁻¹ hχ' n (a.map (segmentCharacterTwist χ hχ)) πχ π
    (equivOfRepresentationEq hπ)
  have ha : (a.map (segmentCharacterTwist χ hχ)).map (segmentCharacterTwist χ⁻¹ hχ') = a := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id a]
    congr 1
    funext Δ
    exact segmentCharacterTwist_inv_twist χ hχ Δ
  rw [ha] at bwd
  exact ⟨⟨fwd.1, bwd.1⟩, ⟨fwd.2, bwd.2⟩⟩

end Langlands.Classification

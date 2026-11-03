import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.Group.RelativeWeylSolomonProof

/-! # Twisted root support under actual point-Coxeter comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

omit [IsAffineHom G.X.hom] in
private theorem point_action_inv_cancel (w : Weyl i) (α : characterLattice T) :
    weylCharacterAction i hN hZ w⁻¹ (weylCharacterAction i hN hZ w α) = α := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Right-face positive monoid elements whose transported pairing vanishes. -/
def pointTwistedStandardPositiveZeroSupport
    (J : Finset (SimpleRoot i ν)) (w : Weyl i) (ζ : cocharacterLattice T) :
    AddSubmonoid (characterLattice T) where
  carrier := {β | β ∈ AddSubmonoid.closure (rootSet i ν J) ∧
    latticePairing T (weylCharacterAction i hN hZ w β) ζ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    exact ⟨AddSubmonoid.add_mem _ hx hy, by simp [hx0, hy0]⟩

variable {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)

include hLength

/-- A double-coset minimum sends every right-face simple root to a positive root. -/
theorem point_weyl_simple_positive_of_isMinimal
    {I J : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hw : IsMinimal cs I J w) {a : SimpleRoot i ν} (ha : a ∈ J) :
    weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν :=
  (hLength w a).mp (((minimalityLengthCriterion_proof cs I J w).mp hw).2 a ha)

/-- Positive roots in the zero face of a left standard cocharacter remain
positive under the inverse of a double-coset minimum. -/
theorem point_weyl_inv_positive_of_pairing_eq_zero
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : Weyl i} (hw : IsMinimal cs I J w)
    {β : characterLattice T} (hβ : β ∈ positiveRelativeRoots i ν)
    (hzero : latticePairing T β ζ = 0) :
    weylCharacterAction i hN hZ w⁻¹ β ∈ positiveRelativeRoots i ν := by
  refine ⟨(weylCharacterAction_mem_relativeRoots_iff i hN hZ w⁻¹ β).mpr hβ.1, ?_⟩
  have hpos := positiveRelativeRoots_induction i ν
    (P := fun β => latticePairing T β ζ = 0 →
      0 < latticePairing T (weylCharacterAction i hN hZ w⁻¹ β) ν)
    (hsimple := fun α hα hα0 => by
      have hαI : α ∈ rootSet i ν I := by
        by_contra hn
        have := hζ.2.2 α hα hn
        omega
      obtain ⟨a, ha, rfl⟩ := hαI
      exact (point_weyl_simple_positive_of_isMinimal i ν hN hZ cs hLength
        (isMinimal_inv cs hw) ha).2)
    (hadd := fun α hα γ hγ ihα ihγ hsum0 => by
      have hnα := hζ.pairing_nonneg_of_positive i ν hα
      have hnγ := hζ.pairing_nonneg_of_positive i ν hγ
      have hsum : latticePairing T α ζ + latticePairing T γ ζ = 0 := by
        simpa using hsum0
      have hpα := ihα (by omega)
      have hpγ := ihγ (by omega)
      simpa using add_pos hpα hpγ) hβ
  exact hpos hzero

/-- A transported right-face simple root has zero left pairing exactly when
it is a simple root of the left face. Indecomposability supplies simplicity. -/
theorem point_weyl_simple_pairing_eq_zero_iff
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : Weyl i} (hw : IsMinimal cs I J w)
    {a : SimpleRoot i ν} (ha : a ∈ J) :
    latticePairing T (weylCharacterAction i hN hZ w a.val) ζ = 0 ↔
      ∃ b ∈ I, weylCharacterAction i hN hZ w a.val = b.val := by
  constructor
  · intro hzero
    have hpos := point_weyl_simple_positive_of_isMinimal i ν hN hZ cs hLength hw ha
    have hs : weylCharacterAction i hN hZ w a.val ∈ simpleRelativeRoots i ν := by
      refine ⟨hpos, ?_⟩
      rintro ⟨β, hβ, γ, hγ, hsum⟩
      have hnβ := hζ.pairing_nonneg_of_positive i ν hβ
      have hnγ := hζ.pairing_nonneg_of_positive i ν hγ
      have hsum0 : latticePairing T β ζ + latticePairing T γ ζ = 0 := by
        simpa only [hsum, map_add, LinearMap.add_apply] using hzero
      have hpβ := point_weyl_inv_positive_of_pairing_eq_zero
        i ν hN hZ cs hLength hζ hw hβ (by omega)
      have hpγ := point_weyl_inv_positive_of_pairing_eq_zero
        i ν hN hZ cs hLength hζ hw hγ (by omega)
      apply a.property.2
      refine ⟨_, hpβ, _, hpγ, ?_⟩
      have he := congrArg (weylCharacterAction i hN hZ w⁻¹) hsum
      simpa only [map_add, point_action_inv_cancel] using he
    have hmem : weylCharacterAction i hN hZ w a.val ∈ rootSet i ν I := by
      by_contra hn
      have := hζ.2.2 _ hs hn
      omega
    obtain ⟨b, hb, heq⟩ := hmem
    exact ⟨b, hb, heq.symm⟩
  · rintro ⟨b, hb, heq⟩
    rw [heq]
    exact hζ.2.1 b.val ⟨b, hb, rfl⟩

/-- The transported pairing is nonnegative on the entire right-face positive
monoid, including its elements that are not roots. -/
theorem point_pairing_weyl_nonneg_of_mem_closure
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : Weyl i} (hw : IsMinimal cs I J w)
    {β : characterLattice T} (hβ : β ∈ AddSubmonoid.closure (rootSet i ν J)) :
    0 ≤ latticePairing T (weylCharacterAction i hN hZ w β) ζ := by
  induction hβ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    obtain ⟨a, ha, rfl⟩ := hβ
    exact hζ.pairing_nonneg_of_positive i ν
      (point_weyl_simple_positive_of_isMinimal i ν hN hZ cs hLength hw ha)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_nonneg hx hy

variable [Fintype (SimpleRoot i ν)]
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)

include hSimple

/-- The canonical Coxeter intersection subset is exactly the right-face
simple roots whose actual transported character has zero left pairing. -/
theorem point_mem_intersectionSubset_iff_pairing_eq_zero
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : Weyl i} (hw : IsMinimal cs I J w) (a : SimpleRoot i ν) :
    a ∈ intersectionSubset cs I J w ↔
      a ∈ J ∧ latticePairing T (weylCharacterAction i hN hZ w a.val) ζ = 0 := by
  classical
  simp only [intersectionSubset, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hmem⟩
    obtain ⟨b, hb, he⟩ := exists_conj_simple_eq_of_isMinimal cs hw ha hmem
    have hab := (hSimple w a b
      (point_weyl_simple_positive_of_isMinimal i ν hN hZ cs hLength hw ha)).mp he
    exact ⟨ha, (point_weyl_simple_pairing_eq_zero_iff
      i ν hN hZ cs hLength hζ hw ha).mpr ⟨b, hb, hab⟩⟩
  · rintro ⟨ha, hzero⟩
    obtain ⟨b, hb, hab⟩ := (point_weyl_simple_pairing_eq_zero_iff
      i ν hN hZ cs hLength hζ hw ha).mp hzero
    refine ⟨ha, ?_⟩
    rw [(hSimple w a b
      (point_weyl_simple_positive_of_isMinimal i ν hN hZ cs hLength hw ha)).mpr hab]
    exact simple_mem_standardSubgroup cs hb

/-- Inside the right-face positive monoid, vanishing after transport cuts out
the monoid generated by the intrinsic intersection subset. -/
theorem point_mem_closure_intersectionSubset_iff
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : Weyl i} (hw : IsMinimal cs I J w)
    {β : characterLattice T} (hβ : β ∈ AddSubmonoid.closure (rootSet i ν J)) :
    β ∈ AddSubmonoid.closure (rootSet i ν (intersectionSubset cs I J w)) ↔
      latticePairing T (weylCharacterAction i hN hZ w β) ζ = 0 := by
  constructor
  · intro hβK
    clear hβ
    induction hβK using AddSubmonoid.closure_induction with
    | mem β hβ =>
      obtain ⟨a, ha, rfl⟩ := hβ
      exact ((point_mem_intersectionSubset_iff_pairing_eq_zero
        i ν hN hZ cs hLength hSimple hζ hw a).mp ha).2
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
  · induction hβ using AddSubmonoid.closure_induction with
    | mem β hβ =>
      obtain ⟨a, ha, rfl⟩ := hβ
      intro hzero
      exact AddSubmonoid.subset_closure ⟨a,
        (point_mem_intersectionSubset_iff_pairing_eq_zero
          i ν hN hZ cs hLength hSimple hζ hw a).mpr ⟨ha, hzero⟩, rfl⟩
    | zero => intro _; exact AddSubmonoid.zero_mem _
    | add x y hx hy ihx ihy =>
      intro hzero
      have hnx := point_pairing_weyl_nonneg_of_mem_closure
        i ν hN hZ cs hLength hζ hw hx
      have hny := point_pairing_weyl_nonneg_of_mem_closure
        i ν hN hZ cs hLength hζ hw hy
      have hsum : latticePairing T (weylCharacterAction i hN hZ w x) ζ +
          latticePairing T (weylCharacterAction i hN hZ w y) ζ = 0 := by
        simpa using hzero
      exact AddSubmonoid.add_mem _ (ihx (by omega)) (ihy (by omega))

/-- The actual point-action zero support has the canonical Coxeter generators. -/
theorem pointTwistedStandardPositiveZeroSupport_eq
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : Weyl i} (hw : IsMinimal cs I J w) :
    pointTwistedStandardPositiveZeroSupport i ν hN hZ J w ζ =
      AddSubmonoid.closure (rootSet i ν (intersectionSubset cs I J w)) := by
  ext β
  change (β ∈ AddSubmonoid.closure (rootSet i ν J) ∧
    latticePairing T (weylCharacterAction i hN hZ w β) ζ = 0) ↔ _
  constructor
  · rintro ⟨hβ, hzero⟩
    exact (point_mem_closure_intersectionSubset_iff
      i ν hN hZ cs hLength hSimple hζ hw hβ).mpr hzero
  · intro hβ
    have hsub : rootSet i ν (intersectionSubset cs I J w) ⊆ rootSet i ν J := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, intersectionSubset_subset cs I J w ha, rfl⟩
    have hβJ := AddSubmonoid.closure_mono hsub hβ
    exact ⟨hβJ, (point_mem_closure_intersectionSubset_iff
      i ν hN hZ cs hLength hSimple hζ hw hβJ).mp hβ⟩

end Langlands.Aubert.General.RationalPointFamily

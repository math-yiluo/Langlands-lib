import Langlands.GroupScheme.Rational.CoxeterCocharacterStabilizer

/-! # Actual root supports for twisted standard-Levi intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- A conjugate simple reflection preserves a cocharacter pairing exactly when
the transported simple root has zero pairing. -/
theorem IsRelativeWeylCoxeterRealization.conjugate_simple_mem_pairingStabilizer_iff
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    (w : relativeWeylGroup i) (a : SimpleRoot i ν) (ζ : cocharacterLattice T) :
    w * cs.simple a * w⁻¹ ∈ cocharacterPairingWeylStabilizer i ζ ↔
      latticePairing T (schemeWeylCharacterAction i w a.1) ζ = 0 := by
  constructor
  · intro hmem
    have heq := hmem (schemeWeylCharacterAction i w a.1)
    have hflip : schemeWeylCharacterAction i (w * cs.simple a * w⁻¹)
        (schemeWeylCharacterAction i w a.1) =
        -(schemeWeylCharacterAction i w a.1) := by
      have hc : schemeWeylCharacterAction i w⁻¹
          (schemeWeylCharacterAction i w a.1) = a.1 := by
        simpa only [map_mul, LinearEquiv.mul_apply] using
          (show schemeWeylCharacterAction i (w⁻¹ * w) a.1 = a.1 by simp)
      simp only [map_mul, LinearEquiv.mul_apply, hc,
        h.simple_action_self a, map_neg]
    rw [hflip] at heq
    simp only [map_neg, LinearMap.neg_apply] at heq
    omega
  · intro hzero χ
    obtain ⟨f, hf, ha⟩ := h.1 a
    change latticePairing T
      (schemeWeylCharacterAction i (w * cs.simple a * w⁻¹) χ) ζ = _
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [ha]
    simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
      hzero, smul_zero, sub_zero]
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

/-- Membership of the intrinsic Coxeter intersection subset is detected by the
zero pairing of the transported actual simple root. -/
theorem IsRelativeWeylCoxeterRealization.mem_intersectionSubset_iff_pairing_eq_zero
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (w : relativeWeylGroup i) (a : SimpleRoot i ν) :
    a ∈ intersectionSubset cs I J w ↔
      a ∈ J ∧ latticePairing T (schemeWeylCharacterAction i w a.1) ζ = 0 := by
  simp only [intersectionSubset, Finset.mem_filter]
  rw [← h.pairingStabilizer_eq_standardSubgroup hν hζ,
    h.conjugate_simple_mem_pairingStabilizer_iff]

/-- A minimum double-coset representative sends the positive monoid generated
by the right face into roots having nonnegative pairing with the left standard
cocharacter. The assertion concerns all monoid elements, not only roots. -/
theorem IsRelativeWeylCoxeterRealization.pairing_weyl_nonneg_of_mem_closure
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    {β : characterLattice T} (hβ : β ∈ AddSubmonoid.closure (rootSet i ν J)) :
    0 ≤ latticePairing T (schemeWeylCharacterAction i w β) ζ := by
  induction hβ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    obtain ⟨a, ha, rfl⟩ := hβ
    apply hζ.pairing_nonneg_of_positive i ν
    apply (h.2.2.1 w a).mp
    exact ((minimalityLengthCriterion_proof cs I J w).mp hw).2 a ha
  | zero => simp
  | add x y _ _ hx hy => simpa using add_nonneg hx hy

/-- Inside the right-face positive monoid, vanishing after transport cuts out
exactly the positive monoid of the intrinsic intersection subset. -/
theorem IsRelativeWeylCoxeterRealization.mem_closure_intersectionSubset_iff
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    {β : characterLattice T} (hβ : β ∈ AddSubmonoid.closure (rootSet i ν J)) :
    β ∈ AddSubmonoid.closure (rootSet i ν (intersectionSubset cs I J w)) ↔
      latticePairing T (schemeWeylCharacterAction i w β) ζ = 0 := by
  constructor
  · intro hβK
    clear hβ
    induction hβK using AddSubmonoid.closure_induction with
    | mem β hβ =>
      obtain ⟨a, ha, rfl⟩ := hβ
      exact ((h.mem_intersectionSubset_iff_pairing_eq_zero hν hζ w a).mp ha).2
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
  · induction hβ using AddSubmonoid.closure_induction with
    | mem β hβ =>
      obtain ⟨a, ha, rfl⟩ := hβ
      intro hzero
      exact AddSubmonoid.subset_closure ⟨a,
        (h.mem_intersectionSubset_iff_pairing_eq_zero hν hζ w a).mpr ⟨ha, hzero⟩, rfl⟩
    | zero => intro _; exact AddSubmonoid.zero_mem _
    | add x y hx hy ihx ihy =>
      intro hzero
      have hnx := h.pairing_weyl_nonneg_of_mem_closure hζ hw hx
      have hny := h.pairing_weyl_nonneg_of_mem_closure hζ hw hy
      have hsum : latticePairing T (schemeWeylCharacterAction i w x) ζ +
          latticePairing T (schemeWeylCharacterAction i w y) ζ = 0 := by
        simpa using hzero
      exact AddSubmonoid.add_mem _ (ihx (by omega)) (ihy (by omega))

/-- The positive right-face monoid elements with zero transported pairing. -/
def twistedStandardPositiveZeroSupport
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (J : Finset (SimpleRoot i ν))
    (w : relativeWeylGroup i) (ζ : cocharacterLattice T) :
    AddSubmonoid (characterLattice T) where
  carrier := {β | β ∈ AddSubmonoid.closure (rootSet i ν J) ∧
    latticePairing T (schemeWeylCharacterAction i w β) ζ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    exact ⟨AddSubmonoid.add_mem _ hx hy, by simp [hx0, hy0]⟩

/-- The actual positive zero-support monoid is generated by the intrinsic
Coxeter intersection subset. -/
theorem IsRelativeWeylCoxeterRealization.twistedStandardPositiveZeroSupport_eq
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w) :
    twistedStandardPositiveZeroSupport i ν J w ζ =
      AddSubmonoid.closure (rootSet i ν (intersectionSubset cs I J w)) := by
  ext β
  change (β ∈ AddSubmonoid.closure (rootSet i ν J) ∧
    latticePairing T (schemeWeylCharacterAction i w β) ζ = 0) ↔ _
  constructor
  · rintro ⟨hβ, hzero⟩
    exact (h.mem_closure_intersectionSubset_iff hν hζ hw hβ).mpr hzero
  · intro hβ
    have hsub : rootSet i ν (intersectionSubset cs I J w) ⊆ rootSet i ν J := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, intersectionSubset_subset cs I J w ha, rfl⟩
    have hβJ := AddSubmonoid.closure_mono hsub hβ
    exact ⟨hβJ, (h.mem_closure_intersectionSubset_iff hν hζ hw hβJ).mp hβ⟩

end Langlands.GroupScheme

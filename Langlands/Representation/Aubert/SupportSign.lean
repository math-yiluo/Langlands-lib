import Langlands.Representation.Aubert.IrreducibleImageProof
import Langlands.VirtualRepresentation.DescentProof

/-!
# The support-sign adjustment on actual exact GL Grothendieck groups

The sign is characterized by effectivity and proved to agree with every actual
quasicuspidal support presentation. The additive extension uses the published
Jordan–Holder isomorphism to the actual exact Grothendieck group.
-/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear SmoothRep VirtualRepresentation
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator

universe uF uV

private theorem effective_sign_unique {ι : Type*} (v : IntegralLattice ι) (hv : v ≠ 0)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hsv : s • v ∈ effective) (htv : t • v ∈ effective) : s = t := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rfl
  · exfalso
    apply hv
    ext i
    have h₁ := hsv i
    have h₂ := htv i
    simp only [one_smul, neg_one_smul, Finsupp.neg_apply] at h₁ h₂
    simp only [Finsupp.zero_apply]
    omega
  · exfalso
    apply hv
    ext i
    have h₁ := hsv i
    have h₂ := htv i
    simp only [one_smul, neg_one_smul, Finsupp.neg_apply] at h₁ h₂
    simp only [Finsupp.zero_apply]
    omega
  · rfl

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The Aubert image of an irreducible basis vector is nonzero in actual
Jordan–Holder coordinates. -/
theorem irreducibleAubertVector_ne_zero (n : ℕ) :
    letI := T.topology
    ∀ c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier,
      onIrreducibles (alternatingOperator.{uF, uV} F T n) (generator c) ≠ 0 := by
  let := T.topology
  intro c h
  have hinj := onIrreducibles_injective (alternatingOperator.{uF, uV} F T n)
    (alternatingOperator_injective.{uF, uV} F T n)
  have hz : generator c = (0 : GeneralLinear.IrreducibleLattice.{uV, uF} n F.Carrier) :=
    hinj (h.trans (map_zero _).symm)
  have := congrArg (fun v => v c) hz
  simp [generator] at this

/-- Every actual irreducible class has a sign making its unadjusted Aubert
image effective. Positive rank uses an actual quasicuspidal embedding and the
published signed-effectivity theorem; rank zero uses the actual identity. -/
theorem exists_effectiveSupportSign (n : ℕ) :
    letI := T.topology
    ∀ c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier,
      ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
        s • onIrreducibles (alternatingOperator.{uF, uV} F T n) (generator c) ∈ effective := by
  let := T.topology
  intro c
  obtain ⟨π, hπ, rfl⟩ := SmoothRep.IrreducibleIsoClass.exists_eq c
  by_cases hn : n = 0
  · subst n
    refine ⟨1, Or.inl rfl, ?_⟩
    have hv : onIrreducibles (alternatingOperator.{uF, uV} F T 0)
        (generator (SmoothRep.irreducibleIsoClass π hπ)) =
        generator (SmoothRep.irreducibleIsoClass π hπ) := by
      rw [alternatingOperator_rankZero]
      exact LinearMap.congr_fun factorMap_comp_realize _
    rw [one_smul, hv]
    intro c
    classical
    simp only [generator, Finsupp.single_apply]
    split_ifs <;> omega
  · obtain ⟨B, σ, hσ, hqc, j, hj⟩ :=
      CuspidalSupport.normalizedQuasicuspidalEmbedding.{uF, max uF uV}
        F T n (Nat.pos_of_ne_zero hn) π hπ
    let M := normalizedInducedFiniteLengthObject.{uF, uV} F T B σ
      (hasFiniteLength_of_isIrreducible hσ)
    have hsub : IsSubquotient π M.val :=
      (mem_support_compositionFactors_iff_isSubquotient M π hπ).mp
        (mem_support_compositionFactors_of_injective π M.val hπ M.property j hj)
    refine ⟨(-1 : ℤ) ^ (n - B.length), neg_one_pow_eq_or ℤ _, ?_⟩
    have he := signedEffectivity.{uF, uV} F T n B σ hσ hqc π hπ hsub
    rw [map_zsmul] at he
    simpa only [onIrreducibles, LinearMap.comp_apply, GeneralLinear.finiteLengthClass,
      SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
        (hasFiniteLength_of_isIrreducible hπ)] using he

/-- The unique sign whose unadjusted Aubert image has nonnegative actual
irreducible multiplicities. The support formula below identifies it with
Aubert Definition 2.1, without choosing a preferred cuspidal support. -/
def supportSign (n : ℕ) :
    letI := T.topology
    GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier → ℤ :=
  letI := T.topology
  fun c => Classical.choose (exists_effectiveSupportSign.{uF, uV} F T n c)

theorem supportSign_eq_one_or_neg_one (n : ℕ) :
    letI := T.topology
    ∀ c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier,
      supportSign.{uF, uV} F T n c = 1 ∨ supportSign.{uF, uV} F T n c = -1 := by
  let := T.topology
  intro c
  exact (Classical.choose_spec (exists_effectiveSupportSign.{uF, uV} F T n c)).1

theorem supportSign_effective (n : ℕ) :
    letI := T.topology
    ∀ c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier,
      supportSign.{uF, uV} F T n c •
        onIrreducibles (alternatingOperator.{uF, uV} F T n) (generator c) ∈ effective := by
  let := T.topology
  intro c
  exact (Classical.choose_spec (exists_effectiveSupportSign.{uF, uV} F T n c)).2

/-- The sign is determined by effectivity, because the unadjusted image is
nonzero. In particular it is independent of all support presentations. -/
theorem supportSign_eq_of_effective (n : ℕ) :
    letI := T.topology
    ∀ (c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier) (s : ℤ),
      (s = 1 ∨ s = -1) →
      s • onIrreducibles (alternatingOperator.{uF, uV} F T n) (generator c) ∈ effective →
      supportSign.{uF, uV} F T n c = s := by
  let := T.topology
  intro c s hs he
  exact effective_sign_unique _ (irreducibleAubertVector_ne_zero.{uF, uV} F T n c)
    (supportSign_eq_one_or_neg_one.{uF, uV} F T n c) hs
    (supportSign_effective.{uF, uV} F T n c) he

/-- On every actual quasicuspidal support presentation the sign is
`(-1)^(n - B.length)`, exactly Aubert Definition 2.1 in the GL conventions.
This includes rank zero whenever such a presentation is supplied. -/
theorem supportSign_of_support {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.IsIrreducible),
      CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.IsIrreducible),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        supportSign.{uF, uV} F T n (SmoothRep.irreducibleIsoClass π hπ) =
          (-1 : ℤ) ^ (n - B.length) := by
  let := T.topology
  intro σ hσ hqc π hπ hsub
  apply supportSign_eq_of_effective.{uF, uV} F T n _ _ (neg_one_pow_eq_or ℤ _)
  have he := signedEffectivity.{uF, uV} F T n B σ hσ hqc π hπ hsub
  rw [map_zsmul] at he
  simpa only [onIrreducibles, LinearMap.comp_apply, GeneralLinear.finiteLengthClass,
    SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
      (hasFiniteLength_of_isIrreducible hπ)] using he

/-- The support sign is one for every actual rank-zero irreducible. -/
theorem supportSign_rankZero :
    letI := T.topology
    ∀ c : GeneralLinear.IrreducibleIsoClass.{uV, uF} 0 F.Carrier,
      supportSign.{uF, uV} F T 0 c = 1 := by
  let := T.topology
  intro c
  apply supportSign_eq_of_effective.{uF, uV} F T 0 c 1 (Or.inl rfl)
  have hv : onIrreducibles (alternatingOperator.{uF, uV} F T 0) (generator c) =
      generator c := by
    rw [alternatingOperator_rankZero]
    exact LinearMap.congr_fun factorMap_comp_realize _
  rw [one_smul, hv]
  intro d
  classical
  simp only [generator, Finsupp.single_apply]
  split_ifs <;> omega

/-- The support-adjusted operator on the actual exact finite-length GL K0.
It extends Definition 2.1 additively along the proved Jordan–Holder comparison;
no multiplicativity premise or conclusion is built into this construction. -/
def adjustedOperator (n : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  (extend fun c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier =>
    supportSign.{uF, uV} F T n c • alternatingOperator.{uF, uV} F T n
      (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (generator c))).comp
        factorMap

/-- The defining irreducible formula is an equality of exact classes. -/
theorem adjustedOperator_irreducible (n : ℕ) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : π.IsIrreducible),
      adjustedOperator.{uF, uV} F T n
          (GeneralLinear.finiteLengthClass n F.Carrier π (hasFiniteLength_of_isIrreducible hπ)) =
        supportSign.{uF, uV} F T n (SmoothRep.irreducibleIsoClass π hπ) •
          alternatingOperator.{uF, uV} F T n
            (GeneralLinear.finiteLengthClass n F.Carrier π
              (hasFiniteLength_of_isIrreducible hπ)) := by
  let := T.topology
  intro π hπ
  change extend _ (factorMap (FiniteLengthGrothendieckGroup.ofRepresentation π _)) = _
  rw [factorMap_ofRepresentation, compositionFactors_irreducible π hπ]
  rw [extend_generator,
    SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
      (hasFiniteLength_of_isIrreducible hπ)]
  rfl

/-- The additive adjustment is the identity on the complete actual K0 in rank
zero, so its eventual graded extension retains the degree-zero unit. -/
theorem adjustedOperator_rankZero :
    letI := T.topology
    adjustedOperator.{uF, uV} F T 0 = LinearMap.id := by
  let := T.topology
  have he : (extend fun c : GeneralLinear.IrreducibleIsoClass.{uV, uF} 0 F.Carrier =>
      supportSign.{uF, uV} F T 0 c • alternatingOperator.{uF, uV} F T 0
        (SmoothRep.realizeIrreducibles ℂ (GeneralLinear 0 F.Carrier) (generator c))) =
      SmoothRep.realizeIrreducibles.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier) := by
    apply SmoothRep.eq_realizeIrreducibles
    intro c
    simp only [extend_generator, supportSign_rankZero, one_smul,
      alternatingOperator_rankZero, LinearMap.id_apply,
      SmoothRep.realizeIrreducibles_generator]
  exact (congrArg (fun f => f.comp factorMap) he).trans realize_comp_factorMap

end Langlands.Aubert

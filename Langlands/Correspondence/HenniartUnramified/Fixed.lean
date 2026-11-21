import Langlands.Correspondence.HenniartUnramified.Occurrence
import Langlands.Correspondence.HenniartUnramified.Arith

/-! # Fixed inertia types and torsion-one classes over unramified extensions -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation FiniteRepresentation.SplitDegree Weil.Local
open VirtualRepresentation VirtualRepresentation.LocalWeil.Ramification

universe uF uW

section General

variable {J : Type*} [Group J] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Equal representations are equivalent. -/
def equivOfEq {ρ σ : Representation ℂ J V} (h : ρ = σ) : Representation.Equiv ρ σ := by
  subst h
  exact Representation.Equiv.refl ρ

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Conjugating the inertia restriction by a power of the lift gives an equivalent
representation. -/
def restrictConjEquiv (D : SplitDegree G) (τ : Representation ℂ G V) (k : ℕ) :
    Representation.Equiv ((τ.comp D.inertia.subtype).comp (D.cj k)) (τ.comp D.inertia.subtype) :=
  Representation.Equiv.mk
    (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom (D.lift ^ k)⁻¹)) fun n => by
    apply LinearMap.ext
    intro v
    change τ (D.lift ^ k)⁻¹ (τ ((D.cj k n : D.inertia) : G) v) = τ (n : G) (τ (D.lift ^ k)⁻¹ v)
    rw [coe_cj, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

end General

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (φ : localWeilGroup F)
  (hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ))

/-- Rank `r` and `r · break = t`. -/
def TypeGood (r t : ℕ) (B : WType.{uF, uW} F φ hφ) : Prop :=
  Module.finrank ℂ B.1 = r ∧ (r : ℝ) * inertiaBreak F B.1.representation = t

/-- Classes of inertia types of rank `r` with `r · break = t`. -/
def goodTypes (r t : ℕ) : Set (TypeClass.{uF, uW} (weilSplit F φ hφ)) :=
  {x | ∃ B, (weilSplit F φ hφ).toClass B = x ∧ TypeGood F φ hφ r t B}

variable {F φ hφ}

theorem typeGood_congr {r t : ℕ} {B B' : WType.{uF, uW} F φ hφ}
    (e : Representation.Equiv B.1.representation B'.1.representation) :
    TypeGood F φ hφ r t B ↔ TypeGood F φ hφ r t B' := by
  unfold TypeGood
  rw [e.toLinearEquiv.finrank_eq, inertiaBreak_equiv F e]

theorem mem_goodTypes_iff {r t : ℕ} (B : WType.{uF, uW} F φ hφ) :
    (weilSplit F φ hφ).toClass B ∈ goodTypes F φ hφ r t ↔ TypeGood F φ hφ r t B := by
  constructor
  · rintro ⟨B', h, hB'⟩
    exact (typeGood_congr ((toClass_eq_iff _ B' B).mp h).some).mp hB'
  · intro h
    exact ⟨B, rfl, h⟩

theorem inertiaBreak_comp_cj {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (weilSplit F φ hφ).inertia V) (j : ℕ) :
    inertiaBreak F (ρ.comp ((weilSplit F φ hφ).cj j)) = inertiaBreak F ρ := by
  apply inertiaBreak_congr F
  intro v _
  change (∀ n : (weilSplit F φ hφ).inertia, (n : localWeilGroup F) ∈ upperGroup F v →
      ρ ((weilSplit F φ hφ).cj j n) = 1) ↔
    (∀ n : (weilSplit F φ hφ).inertia, (n : localWeilGroup F) ∈ upperGroup F v → ρ n = 1)
  have hN : (upperGroup F v).Normal := inferInstance
  constructor
  · intro h n hn
    obtain ⟨n', rfl⟩ := (weilSplit F φ hφ).cj_surjective j n
    apply h n'
    have h2 := hN.conj_mem _ hn ((weilSplit F φ hφ).lift ^ j)⁻¹
    rw [coe_cj] at h2
    simpa [mul_assoc] using h2
  · intro h n hn
    apply h ((weilSplit F φ hφ).cj j n)
    rw [coe_cj]
    exact hN.conj_mem _ hn _

theorem typeGood_conjObj {r t : ℕ} (j : ℕ) (B : WType.{uF, uW} F φ hφ) :
    TypeGood F φ hφ r t ((weilSplit F φ hφ).conjObj j B) ↔ TypeGood F φ hφ r t B := by
  have h := inertiaBreak_comp_cj (φ := φ) (hφ := hφ) B.1.representation j
  change (Module.finrank ℂ B.1 = r ∧
    (r : ℝ) * inertiaBreak F (B.1.representation.comp ((weilSplit F φ hφ).cj j)) = t) ↔ _
  rw [h]
  rfl

theorem conjType_mem_goodTypes {r t : ℕ} (j : ℕ) (x : TypeClass.{uF, uW} (weilSplit F φ hφ)) :
    (weilSplit F φ hφ).conjType j x ∈ goodTypes F φ hφ r t ↔ x ∈ goodTypes F φ hφ r t := by
  induction x using Quotient.inductionOn with
  | h B =>
    change (weilSplit F φ hφ).conjType j ((weilSplit F φ hφ).toClass B) ∈ _ ↔
      (weilSplit F φ hφ).toClass B ∈ _
    rw [conjType_mk, mem_goodTypes_iff, mem_goodTypes_iff, typeGood_conjObj]

section Stage

variable (m : ℕ)

theorem block_twist {V : Type*} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (localWeilGroup ((unramifiedStage F (m + 1)).asPadicField (p := p))) V)
    (z : ℂˣ) :
    (weilStage F φ hφ m).block
        (Langlands.twist (unramifiedCharacter (localDegree _) z).toMonoidHom τ) 0 =
      (weilStage F φ hφ m).block τ 0 := by
  ext n : 1
  change ((unramifiedCharacter (localDegree _) z ((weilStage F φ hφ m).κ
      ((weilSplit F φ hφ).cj 0 n)) : ℂˣ) : ℂ) • τ ((weilStage F φ hφ m).κ
      ((weilSplit F φ hφ).cj 0 n)) = τ ((weilStage F φ hφ m).κ ((weilSplit F φ hφ).cj 0 n))
  rw [unramifiedCharacter_on_kernel _ z ((weilStage F φ hφ m).κ_mem _), Units.val_one, one_smul]

/-- Fixed types of the right rank and break correspond to torsion-one orbits over the
unramified extension of degree `m + 1`. -/
theorem encard_fixed_goodTypes (r' t : ℕ) :
    (weilRefinedStratum.{uF, uW} ((unramifiedStage F (m + 1)).asPadicField (p := p)) r' t
      1).encard =
      {x ∈ goodTypes.{uF, uW} F φ hφ (r' + 1) t |
        (weilSplit F φ hφ).conjType (m + 1) x = x}.encard := by
  let L := (unramifiedStage F (m + 1)).asPadicField (p := p)
  let S := weilStage F φ hφ m
  let lam := stageLift F φ hφ m
  let hlam := stageLift_degree F φ hφ m
  let R : Weil.UnramifiedOrbitClasses.{uF, uW} (localDegree L) →
      TypeClass.{uF, uW} (weilSplit F φ hφ) → Prop := fun c x =>
    ∃ (A : WeilObj.{uF, uW} L) (h : A.1.rank = r' + 1),
      Weil.unramifiedOrbitClass (localDegree L) ⟨r'.succPNat, weilClassOf L A h⟩ = c ∧
      ∃ B : WType.{uF, uW} F φ hφ, (weilSplit F φ hφ).toClass B = x ∧
        Nonempty (Representation.Equiv (S.block A.1.representation 0) B.1.representation)
  apply encard_eq_of_rel R
  · -- every torsion-one orbit gives a fixed type
    rintro c ⟨σ, hc, hs, ht⟩
    obtain ⟨A, h, rfl⟩ := weilClassOf_surjective L σ
    have hirrJ := inertia_irreducible_of_torsion_one (φ := lam) (hφ := hlam) A h ht
    have hblock := S.block_isIrreducible A.1.representation hirrJ
    have hcont : (FiniteRepresentation.of (S.block A.1.representation 0)).IsContinuous :=
      isContinuous_restrict (S.κ.comp ((weilSplit F φ hφ).cj 0))
        (S.continuous_κ.comp ((weilSplit F φ hφ).continuous_cj 0)) A.2.1
    let B : WType.{uF, uW} F φ hφ := ⟨FiniteRepresentation.of (S.block A.1.representation 0),
      hcont, hblock⟩
    refine ⟨(weilSplit F φ hφ).toClass B, ⟨?_, ?_⟩, A, h, hc, B, rfl,
      ⟨Representation.Equiv.refl _⟩⟩
    · rw [mem_goodTypes_iff]
      refine ⟨h, ?_⟩
      have h1 := (hasWeilSwan_weilClassOf L A h t).mp hs
      have h2 := lastBreak_stage F φ hφ m A.1.representation
      change lastBreak L A.1 = _ at h2
      rw [h2] at h1
      exact h1.symm
    · rw [conjType_mk]
      exact (toClass_eq_iff _ _ _).mpr ⟨(S.blockConjEquiv A.1.representation).symm⟩
  · -- every fixed type gives a torsion-one orbit
    rintro x ⟨⟨B, rfl, hgood⟩, hfix⟩
    rw [conjType_mk] at hfix
    obtain ⟨e⟩ := (toClass_eq_iff _ _ _).mp hfix
    obtain ⟨τ, h1, h2, h3⟩ := S.exists_extension B.1.representation e
    have hτc : (FiniteRepresentation.of τ).IsContinuous := h3 B.2.1
    have hτJ : Representation.IsIrreducible
        (τ.comp (weilSplit L lam hlam).inertia.subtype) := by
      rw [h2]
      exact isIrreducible_comp_surjective _ _ S.ιJ_surjective B.2.2
    have hτ : τ.IsIrreducible := isIrreducible_of_comp τ _ hτJ
    let A : WeilObj.{uF, uW} L := ⟨FiniteRepresentation.of τ, hτc, hτ⟩
    have hA : A.1.rank = r' + 1 := hgood.1
    refine ⟨_, ⟨weilClassOf L A hA, rfl, ?_, ?_⟩, A, hA, rfl, B, rfl, ⟨equivOfEq h1⟩⟩
    · rw [hasWeilSwan_weilClassOf]
      have h4 := lastBreak_stage F φ hφ m τ
      change lastBreak L A.1 = _ at h4
      rw [h4, h1]
      exact hgood.2.symm
    · have : Nontrivial A.1 := nontrivial_of_isIrreducible _ hτ
      let B'' : WType.{uF, uW} L lam hlam :=
        ⟨FiniteRepresentation.of (τ.comp (weilSplit L lam hlam).inertia.subtype),
          isContinuous_restrict _ continuous_subtype_val hτc, hτJ⟩
      have hp : Function.minimalPeriod ((weilSplit L lam hlam).conjType 1)
          ((weilSplit L lam hlam).toClass B'') = 0 + 1 := by
        rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
        change (weilSplit L lam hlam).conjType 1 ((weilSplit L lam hlam).toClass B'') = _
        rw [conjType_mk]
        exact (toClass_eq_iff _ _ _).mpr ⟨restrictConjEquiv (weilSplit L lam hlam) τ 1⟩
      exact weilTorsionNumber_eq_period L lam hlam A hA B''
        (Representation.IntertwiningMap.id _)
        (equiv_toIntertwiningMap_ne_zero (Representation.Equiv.refl _)) hp
  · -- functional
    rintro c - x - x' - ⟨A, h, hc, B, hB, ⟨e⟩⟩ ⟨A', h', hc', B', hB', ⟨e'⟩⟩
    obtain ⟨z, ⟨f⟩⟩ := (weilOrbit_eq_iff L A A' h h').mp (hc.trans hc'.symm)
    let E1 : Representation.Equiv (S.block A'.1.representation 0) (S.block A.1.representation 0) :=
      (equivOfEq (block_twist m A'.1.representation z).symm).trans
        (equivComp f (S.κ.comp ((weilSplit F φ hφ).cj 0)))
    rw [← hB, ← hB']
    exact (toClass_eq_iff _ _ _).mpr ⟨e.symm.trans (E1.symm.trans e')⟩
  · -- injective
    rintro c - c' - x - ⟨A, h, hc, B, hB, ⟨e⟩⟩ ⟨A', h', hc', B', hB', ⟨e'⟩⟩
    obtain ⟨g⟩ := (toClass_eq_iff _ _ _).mp (hB.trans hB'.symm)
    let G0 := e.trans (g.trans e'.symm)
    let G1 : Representation.Equiv (A.1.representation.comp (weilSplit L lam hlam).inertia.subtype)
        (A'.1.representation.comp (weilSplit L lam hlam).inertia.subtype) :=
      (equivOfEq (S.comp_inertia_eq_block A.1.representation)).trans
        ((equivComp G0 S.ιJ).trans (equivOfEq (S.comp_inertia_eq_block A'.1.representation).symm))
    have : Nontrivial A.1 := nontrivial_of_isIrreducible _ A.2.2
    obtain ⟨z, hz⟩ := twist_equiv_of_inertia_ne_zero (weilSplit L lam hlam) A.1.representation
      A'.1.representation A.2.2 A'.2.2 G1.toIntertwiningMap (equiv_toIntertwiningMap_ne_zero G1)
    rw [← hc, ← hc']
    exact ((weilOrbit_eq_iff L A' A h' h).mpr ⟨z, hz⟩).symm

end Stage

end Langlands.Henniart.Numerical

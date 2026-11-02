import Langlands.Global.PositiveRealTorusLog
import Langlands.Global.RelativeRootChamber
import Mathlib.Analysis.Convex.Basic

/-! # Logarithmic halfspaces for actual positive-torus chambers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (T₀ T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (j : T₀ ⟶ T)
variable (Δ : Set (characterLattice T)) (b : characterLattice T → ℝ≥0ˣ)

/-- Weak halfspaces in the actual real character dual, with normalized log thresholds. -/
def weakLogCharacterChamber : Set (RealCharacterDual F T₀.toGrp) :=
  {ℓ | ∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) ≤ ℓ (j ≫ χ)}

/-- Strict halfspaces retain the same actual character restriction and thresholds. -/
def strictLogCharacterChamber : Set (RealCharacterDual F T₀.toGrp) :=
  {ℓ | ∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) < ℓ (j ≫ χ)}

omit [NumberField F] in
theorem weakLogCharacterChamber_eq_iInter :
    weakLogCharacterChamber F T₀ T j Δ b =
      ⋂ χ ∈ Δ, (dualEval F T₀.toGrp (j ≫ χ)) ⁻¹'
        Set.Ici (Real.log ((b χ : ℝ≥0) : ℝ)) := by
  ext ℓ
  simp only [weakLogCharacterChamber, Set.mem_ofPred_eq, Set.mem_iInter,
    Set.mem_preimage, Set.mem_Ici]
  rfl

omit [NumberField F] in
theorem strictLogCharacterChamber_eq_iInter :
    strictLogCharacterChamber F T₀ T j Δ b =
      ⋂ χ ∈ Δ, (dualEval F T₀.toGrp (j ≫ χ)) ⁻¹'
        Set.Ioi (Real.log ((b χ : ℝ≥0) : ℝ)) := by
  ext ℓ
  simp only [strictLogCharacterChamber, Set.mem_ofPred_eq, Set.mem_iInter,
    Set.mem_preimage, Set.mem_Ioi]
  rfl

omit [NumberField F] in
/-- Arbitrary weak chambers are closed convex intersections of linear halfspaces. -/
theorem isClosed_weakLogCharacterChamber :
    IsClosed (weakLogCharacterChamber F T₀ T j Δ b) := by
  rw [weakLogCharacterChamber_eq_iInter]
  exact isClosed_iInter fun χ => isClosed_iInter fun _ =>
    isClosed_Ici.preimage (continuous_dualEval F T₀.toGrp (j ≫ χ))

omit [NumberField F] in
theorem convex_weakLogCharacterChamber :
    Convex ℝ (weakLogCharacterChamber F T₀ T j Δ b) := by
  rw [weakLogCharacterChamber_eq_iInter]
  exact convex_iInter fun χ => convex_iInter fun _ =>
    (convex_Ici _).linear_preimage (dualEval F T₀.toGrp (j ≫ χ))

omit [NumberField F] in
theorem convex_strictLogCharacterChamber :
    Convex ℝ (strictLogCharacterChamber F T₀ T j Δ b) := by
  rw [strictLogCharacterChamber_eq_iInter]
  exact convex_iInter fun χ => convex_iInter fun _ =>
    (convex_Ioi _).linear_preimage (dualEval F T₀.toGrp (j ≫ χ))

omit [NumberField F] in
/-- Openness of the strict chamber requires only finiteness of the selected characters. -/
theorem isOpen_strictLogCharacterChamber (hΔ : Δ.Finite) :
    IsOpen (strictLogCharacterChamber F T₀ T j Δ b) := by
  rw [strictLogCharacterChamber_eq_iInter]
  exact hΔ.isOpen_biInter fun χ _ =>
    isOpen_Ioi.preimage (continuous_dualEval F T₀.toGrp (j ≫ χ))

omit [NumberField F] in
theorem weakLogCharacterChamber_empty :
    weakLogCharacterChamber F T₀ T j ∅ b = Set.univ := by
  ext ℓ
  simp [weakLogCharacterChamber]

omit [NumberField F] in
theorem strictLogCharacterChamber_empty :
    strictLogCharacterChamber F T₀ T j ∅ b = Set.univ := by
  ext ℓ
  simp [strictLogCharacterChamber]

/-- The logarithm compares positive units without changing a weak threshold. -/
theorem log_unit_le_log_unit_iff (x y : ℝ≥0ˣ) :
    Real.log ((x : ℝ≥0) : ℝ) ≤ Real.log ((y : ℝ≥0) : ℝ) ↔ x ≤ y := by
  have hx : 0 < ((x : ℝ≥0) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr x.ne_zero)
  have hy : 0 < ((y : ℝ≥0) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr y.ne_zero)
  rw [Real.log_le_log_iff hx hy]
  exact_mod_cast (Iff.rfl : (x : ℝ≥0) ≤ (y : ℝ≥0) ↔ x ≤ y)

theorem log_unit_lt_log_unit_iff (x y : ℝ≥0ˣ) :
    Real.log ((x : ℝ≥0) : ℝ) < Real.log ((y : ℝ≥0) : ℝ) ↔ x < y := by
  have hx : 0 < ((x : ℝ≥0) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr x.ne_zero)
  have hy : 0 < ((y : ℝ≥0) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr y.ne_zero)
  rw [Real.log_lt_log_iff hx hy]
  exact_mod_cast (Iff.rfl : (x : ℝ≥0) < (y : ℝ≥0) ↔ x < y)

/-- The intrinsic weak chamber is exactly the inverse image under the actual adelic log. -/
theorem mem_weakCharacterChamber_iff_log (a : intrinsicSubgroup F T₀) :
    a ∈ weakCharacterChamber F T₀ T j Δ b ↔
      characterLog F T₀.toGrp a.val ∈ weakLogCharacterChamber F T₀ T j Δ b := by
  change (∀ χ ∈ Δ, b χ ≤ normCharacter F T₀ (j ≫ χ) a.val) ↔
    ∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) ≤ characterLog F T₀.toGrp a.val (j ≫ χ)
  apply forall₂_congr
  intro χ _
  exact (log_unit_le_log_unit_iff (b χ) (normCharacter F T₀ (j ≫ χ) a.val)).symm

theorem mem_strictCharacterChamber_iff_log (a : intrinsicSubgroup F T₀) :
    a ∈ strictCharacterChamber F T₀ T j Δ b ↔
      characterLog F T₀.toGrp a.val ∈ strictLogCharacterChamber F T₀ T j Δ b := by
  change (∀ χ ∈ Δ, b χ < normCharacter F T₀ (j ≫ χ) a.val) ↔
    ∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) < characterLog F T₀.toGrp a.val (j ≫ χ)
  apply forall₂_congr
  intro χ _
  exact (log_unit_lt_log_unit_iff (b χ) (normCharacter F T₀ (j ≫ χ) a.val)).symm

section Coordinates

variable (I : Type u) [Fintype I]
variable (e : T₀.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

include I e in
/-- For a supplied finite splitting, every weak log halfspace point is attained. -/
theorem characterLog_image_weakCharacterChamber :
    (fun a : intrinsicSubgroup F T₀ => characterLog F T₀.toGrp a.val) ''
        weakCharacterChamber F T₀ T j Δ b =
      weakLogCharacterChamber F T₀ T j Δ b := by
  ext ℓ
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_weakCharacterChamber_iff_log F T₀ T j Δ b a).mp ha
  · intro hℓ
    refine ⟨positiveExp F T₀ I e ℓ, ?_, characterLog_full_logParameters F T₀ I e ℓ⟩
    apply (mem_weakCharacterChamber_iff_log F T₀ T j Δ b _).mpr
    change characterLog F T₀.toGrp (full F I T₀ e (logParameters F T₀ I e ℓ)) ∈ _
    rwa [characterLog_full_logParameters]

include I e in
theorem characterLog_image_strictCharacterChamber :
    (fun a : intrinsicSubgroup F T₀ => characterLog F T₀.toGrp a.val) ''
        strictCharacterChamber F T₀ T j Δ b =
      strictLogCharacterChamber F T₀ T j Δ b := by
  ext ℓ
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_strictCharacterChamber_iff_log F T₀ T j Δ b a).mp ha
  · intro hℓ
    refine ⟨positiveExp F T₀ I e ℓ, ?_, characterLog_full_logParameters F T₀ I e ℓ⟩
    apply (mem_strictCharacterChamber_iff_log F T₀ T j Δ b _).mpr
    change characterLog F T₀.toGrp (full F I T₀ e (logParameters F T₀ I e ℓ)) ∈ _
    rwa [characterLog_full_logParameters]

/-- Scalar coordinates give degree-weighted linear inequalities in their ordinary logs. -/
theorem mem_weakCharacterChamber_fullIntrinsic_iff_log (x : I → ℝ≥0ˣ) :
    fullIntrinsic F T₀ I e x ∈ weakCharacterChamber F T₀ T j Δ b ↔
      ∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) ≤
        (Module.finrank ℚ F : ℝ) *
          ∑ i, (characterExponents F I T₀ e (j ≫ χ) i : ℝ) *
            Real.log ((x i : ℝ≥0) : ℝ) := by
  rw [mem_weakCharacterChamber_iff_log]
  change (∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) ≤
    characterLog F T₀.toGrp (full F I T₀ e x) (j ≫ χ)) ↔ _
  apply forall₂_congr
  intro χ _
  exact Iff.of_eq (congrArg (fun r => Real.log ((b χ : ℝ≥0) : ℝ) ≤ r)
    (characterLog_full_eq_sum F T₀ I e (j ≫ χ) x))

theorem mem_strictCharacterChamber_fullIntrinsic_iff_log (x : I → ℝ≥0ˣ) :
    fullIntrinsic F T₀ I e x ∈ strictCharacterChamber F T₀ T j Δ b ↔
      ∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) <
        (Module.finrank ℚ F : ℝ) *
          ∑ i, (characterExponents F I T₀ e (j ≫ χ) i : ℝ) *
            Real.log ((x i : ℝ≥0) : ℝ) := by
  rw [mem_strictCharacterChamber_iff_log]
  change (∀ χ ∈ Δ, Real.log ((b χ : ℝ≥0) : ℝ) <
    characterLog F T₀.toGrp (full F I T₀ e x) (j ≫ χ)) ↔ _
  apply forall₂_congr
  intro χ _
  exact Iff.of_eq (congrArg (fun r => Real.log ((b χ : ℝ≥0) : ℝ) < r)
    (characterLog_full_eq_sum F T₀ I e (j ≫ χ) x))

end Coordinates

section RelativeRoots

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The GH weak simple-root convention uses the ordinary log of its common threshold. -/
theorem mem_weakSimpleRootChamber_iff_log
    (t : ℝ≥0ˣ) (a : intrinsicSubgroup F T₀) :
    a ∈ weakSimpleRootChamber F T₀ T j G i ν t ↔
      ∀ χ ∈ simpleRelativeRoots i ν,
        Real.log ((t : ℝ≥0) : ℝ) ≤ characterLog F T₀.toGrp a.val (j ≫ χ) :=
  mem_weakCharacterChamber_iff_log F T₀ T j (simpleRelativeRoots i ν) (fun _ => t) a

/-- A torus reference point gives its actual log as the strict comparison threshold. -/
theorem mem_basedStrictSimpleRootChamber_iff_log
    (a₀ : Lie.AffinePoints T.toGrp (Adeles F)) (a : intrinsicSubgroup F T₀) :
    a ∈ basedStrictSimpleRootChamber F T₀ T j G i ν a₀ ↔
      ∀ χ ∈ simpleRelativeRoots i ν,
        characterLog F T.toGrp a₀ χ < characterLog F T₀.toGrp a.val (j ≫ χ) := by
  rw [basedStrictSimpleRootChamber, strictSimpleRootChamber,
    mem_strictCharacterChamber_iff_log]
  change (∀ χ ∈ simpleRelativeRoots i ν,
    Real.log ((normCharacter F T χ a₀ : ℝ≥0) : ℝ) <
      characterLog F T₀.toGrp a.val (j ≫ χ)) ↔ _
  simp only [normCharacter_apply, characterLog_eq_log_characterValue]

end RelativeRoots

end Langlands.Global.PositiveRealTorus

import Langlands.Representation.Derivative.MirabolicHighestLayerLift
import Langlands.Representation.Aubert.ZelevinskyHighestDerivative
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof

/-!
# Homogeneity descends through mirabolic `Φ⁻`

The mirabolic restriction of an irreducible representation of `GL_(N+1)` is
homogeneous. A homogeneous representation of level at least two stays homogeneous
under `Φ⁻`, with level lowered by one, and it has no nonzero vector fixed by the whole
radical. These are the homogeneity inputs of Bernstein 1984, §7.4.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A representation of level at least two has exactly one more level than its `Φ⁻`. -/
theorem level_phiMinus_add_one {M : ℕ} :
    letI := T.topology
    ∀ W : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier), 2 ≤ level T ψ W →
      level T ψ ((phiMinus T ψ M).obj W) + 1 = level T ψ W := by
  let := T.topology
  intro W hW
  have : Nontrivial ((phiMinus T ψ M).obj W) :=
    (LevelCalculus.nontrivial_phiMinus_iff T ψ W).mpr (by omega)
  exact (LevelCalculus.level_eq_level_phiMinus_succ T ψ W
    (LevelCalculus.level_pos T ψ ((phiMinus T ψ M).obj W))).symm

/-- One `Φ⁻` step keeps homogeneity at level at least two and lowers the level by one. -/
theorem isHomogeneous_phiMinus {M : ℕ} :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      IsHomogeneous T ψ B → 2 ≤ level T ψ B →
        IsHomogeneous T ψ ((phiMinus T ψ M).obj B) ∧
          level T ψ ((phiMinus T ψ M).obj B) + 1 = level T ψ B := by
  let := T.topology
  intro B hB hlev
  refine ⟨fun X hX => ?_, level_phiMinus_add_one T ψ B hlev⟩
  have himg := HighestLayer.imageStep_liftStep T ψ M B X
  have hW : HighestLayer.liftStep T ψ M B X ≠ ⊥ := by
    intro h
    apply hX
    rw [← himg, h, HighestLayer.imageStep_bot]
  have hlevW := hB _ hW
  rw [← himg, ← LevelCalculus.level_eq_of_iso T ψ
    (HighestLayer.phiMinusSubIso T ψ M B (HighestLayer.liftStep T ψ M B X))]
  have h1 := level_phiMinus_add_one T ψ
    (SmoothRep.subrepresentation B (HighestLayer.liftStep T ψ M B X)) (by omega)
  have h2 := level_phiMinus_add_one T ψ B hlev
  omega

/-- Iterating: `(Φ⁻)^j` keeps homogeneity while the level exceeds `j`, lowering it by `j`. -/
theorem isHomogeneous_phiMinusIterate (n : ℕ) :
    letI := T.topology
    ∀ (j : ℕ) (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)),
      IsHomogeneous T ψ B → j + 1 ≤ level T ψ B →
        IsHomogeneous T ψ ((phiMinusIterate T ψ n j).obj B) ∧
          level T ψ ((phiMinusIterate T ψ n j).obj B) + j = level T ψ B := by
  let := T.topology
  intro j
  induction j with
  | zero => exact fun B hB _ => ⟨hB, rfl⟩
  | succ j ih =>
    intro B hB hlev
    obtain ⟨h1, h2⟩ := isHomogeneous_phiMinus T ψ (M := n + j) B hB (by omega)
    obtain ⟨h3, h4⟩ := ih _ h1 (by omega)
    have he : (phiMinusIterate T ψ n (j + 1)).obj B =
        (phiMinusIterate T ψ n j).obj ((phiMinus T ψ (n + j)).obj B) := rfl
    rw [he]
    exact ⟨h3, by omega⟩

/-- A homogeneous representation of level at least two has no nonzero radical-fixed
vector: those vectors span an invariant subspace on which `Φ⁻` vanishes, so it would
have level at most one. -/
theorem eq_zero_of_radical_fixed {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      IsHomogeneous T ψ A → 2 ≤ level T ψ A →
        ∀ v : A, (∀ u : radical (M + 1) F.Carrier,
          A.representation (u : mirabolic (M + 1) F.Carrier) v = v) → v = 0 := by
  let := T.topology
  intro A hA hlev v hv
  let U : Subrepresentation A.representation :=
    { toSubmodule :=
        { carrier := {w | ∀ u : radical (M + 1) F.Carrier,
            A.representation (u : mirabolic (M + 1) F.Carrier) w = w}
          add_mem' := fun {a b} ha hb u => by
            change A.representation _ (a + b) = a + b
            rw [map_add, ha u, hb u]
          zero_mem' := fun u => map_zero _
          smul_mem' := fun c w hw u => by
            change A.representation _ (c • w) = c • w
            rw [map_smul, hw u] }
      apply_mem_toSubmodule := fun g w hw u => by
        have hmem : g⁻¹ * (u : mirabolic (M + 1) F.Carrier) * g ∈ radical (M + 1) F.Carrier := by
          simpa using (radical_normal (n := M + 1) (F := F.Carrier)).conj_mem _ u.property g⁻¹
        change A.representation u (A.representation g w) = A.representation g w
        have hw' := hw ⟨_, hmem⟩
        change A.representation (g⁻¹ * (u : mirabolic (M + 1) F.Carrier) * g) w = w at hw'
        rw [← Module.End.mul_apply, ← map_mul,
          show (u : mirabolic (M + 1) F.Carrier) * g =
            g * (g⁻¹ * (u : mirabolic (M + 1) F.Carrier) * g) by group,
          map_mul, Module.End.mul_apply, hw'] }
  by_contra hv0
  have hU : U ≠ ⊥ := (HighestLayer.ne_bot_iff_exists U).mpr ⟨v, hv, hv0⟩
  have hlevU := hA U hU
  have hsub : Subsingleton ((phiMinus T ψ M).obj (SmoothRep.subrepresentation A U)) := by
    obtain ⟨c, u, hcu⟩ := HighestLayer.exists_radical_difference T ψ M
    have hz : ∀ w : SmoothRep.subrepresentation A U,
        phiMinusQuotient T ψ M (SmoothRep.subrepresentation A U) w = 0 := by
      intro w
      rw [← hcu _ w]
      have hfix : (SmoothRep.subrepresentation A U).representation
          (u : mirabolic (M + 1) F.Carrier) w = w := Subtype.ext (w.2 u)
      rw [hfix, sub_self, smul_zero, map_zero]
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := phiMinusQuotient_surjective T ψ M _ x
    obtain ⟨y, rfl⟩ := phiMinusQuotient_surjective T ψ M _ y
    rw [hz, hz]
  have := LevelCalculus.level_le_one_of_subsingleton_phiMinus T ψ _ hsub
  omega

/-- Zelevinsky 1980, Theorem 6.2, through the socle exhaustion of §6: the mirabolic
restriction of an irreducible representation of `GL_(N+1)` is homogeneous. -/
theorem isHomogeneous_restriction_of_isIrreducible {N : ℕ} :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      Representation.IsIrreducible π.representation →
        IsHomogeneous T ψ ((generalLinearRestriction T N).obj π) := by
  let := T.topology
  intro π hπ
  obtain ⟨a, -, d, -, hd⟩ := Classification.multisegmentSocleExhaustion.{uF, uV} F T (N + 1) π hπ
  obtain ⟨ho, hs, -, j, hj⟩ := hd.isZelevinskySubrepresentation
  have hsep := Classification.precedenceOrdered_endpointSeparated.{uF, max uF uV} F T
    (Classification.cuspidalIntegralTwistFreeness.{uF, max uF uV} F T) d.segments ho
  have hhom : IsHomogeneous T ψ ((generalLinearRestriction T N).obj d.induced) :=
    (isGeneralLinearHomogeneous_iff T ψ d.induced).mp
      (Classification.segmentSocleProductHomogeneity.{uF, max uF uV} F T ψ N d hs hsep)
  let jS : π ⟶ d.induced := SmoothRep.ofHom j
  have hjR : Function.Injective (SmoothRep.hom ((generalLinearRestriction T N).map jS)) :=
    LevelCalculus.map_injective_of_exact (generalLinearRestriction_mapsShortExact F T N) jS hj
  refine LevelCalculus.isHomogeneous_of_forall_injective T ψ _
    (level T ψ ((generalLinearRestriction T N).obj d.induced)) fun W f hf hW => ?_
  exact LevelCalculus.level_eq_of_isHomogeneous T ψ hhom
    (f ≫ (generalLinearRestriction T N).map jS) (hjR.comp hf) hW

end Langlands.Derivative.Mirabolic

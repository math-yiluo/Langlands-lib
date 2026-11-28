import Langlands.Global.AdelicLocalFinitenessBoundaryLogBounds
import Langlands.Global.AdelicPositiveTorusLogHeightBound
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicSiegelChamberGeometryStatement
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Upper logarithmic height on a Siegel chamber -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus RepresentationGrowth

/-- **Linear upper bound for the logarithmic height on Siegel chambers** (Delorme 2023, (2.8)).
The simple-root logarithms of `b` and the logarithms of finitely many rational characters of `G`
at `z b ω` bound `adelicLogHeight` at `z b ω` linearly, uniformly for `ω` in a compact set. -/
theorem siegelChamberHeightComparison : SiegelChamberHeightComparisonStatement := by
  classical
  intro F _ _ G _ _ _ hG N rho _ T i ν T₀ j hsetup Ω hΩ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, Fin.elim0, adelicLogHeight F G rho 1, fun z hz b ω hω R hR _ _ => ?_⟩
    have h : adelicSourceNorm F G rho (z * positiveMap F G T i T₀ j b * ω) =
        adelicSourceNorm F G rho 1 :=
      congrArg (AdelicMatrixHeight.sourceNorm F 0) (Subsingleton.elim _ _)
    rw [adelicLogHeight, h, ← adelicLogHeight]
    exact le_mul_of_one_le_right (zero_le_one.trans (one_le_adelicLogHeight rho 1))
      (by linarith)
  obtain ⟨hi, hν, _, _, _, _, _, _, Z, zc, hZc, _⟩ := hsetup
  obtain ⟨S, hS, hSambient, hSpan⟩ := exists_finite_ambient_characters_span F i ν hG hi hν
  let : Fintype S := hS.fintype
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  have hRange (q : Fin r) : ∃ χ : rationalCharacters G, torusCharacterRestrict i χ = (e q).val :=
    hSambient (e q).property
  choose χ hχ using hRange
  obtain ⟨A, rate, hA, hRate, hHeight⟩ :=
    adelicPositiveTorusLogHeightBound i rho _ hi.isSplitSubtorus.1 hSpan hN
  obtain ⟨B₀, hB₀⟩ := (hΩ.image (continuous_adelicHeight F G rho hN)).bddAbove
  let B := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hωBound (ω : AdelicGroupPoints F G) (hω : ω ∈ Ω) :
      adelicHeight F G rho ω ≤ B :=
    (hB₀ ⟨ω, hω, rfl⟩).trans (le_max_right _ _)
  have hCoordBound (q : Fin r) : ∃ Dq : ℝ, ∀ ω ∈ Ω, |characterLog F G ω (χ q)| ≤ Dq := by
    obtain ⟨Dq, hDq⟩ :=
      (hΩ.image (continuous_characterLog_eval F G (χ q)).abs).bddAbove
    exact ⟨Dq, fun ω hω => hDq ⟨ω, hω, rfl⟩⟩
  choose Dq hDq using hCoordBound
  let D := ∑ q, max 0 (Dq q)
  have hD : 0 ≤ D := Finset.sum_nonneg fun q _ => le_max_left _ _
  let C₀ := 1 + Real.log (A * B) + rate * D
  refine ⟨r, χ, max C₀ rate, fun z hz b ω hω R hR hRoots hChars => ?_⟩
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hZc] at hz
  obtain ⟨a, ha, hza⟩ := hz
  let aT := map F Z.toGrp T.toGrp (CommGroupScheme.groupHom zc) a
  let bT := map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) b.val
  let ab : intrinsicSubgroup F T :=
    ⟨aT * bT, (intrinsicSubgroup F T).mul_mem
      (map_intrinsicSubgroup_le F Z T zc ⟨a, ha, rfl⟩)
      (map_intrinsicSubgroup_le F T₀ T j ⟨b.val, b.property, rfl⟩)⟩
  have hab : map F T.toGrp G i ab.val = z * positiveMap F G T i T₀ j b := by
    change map F T.toGrp G i (aT * bT) = _
    rw [map_mul, ← map_comp_apply_of_hom, ← map_comp_apply_of_hom]
    exact congrArg (· * positiveMap F G T i T₀ j b) hza
  have hBounds : ∀ ψ ∈ simpleRelativeRoots i ν ∪ S, |logNormHom F T ab.val ψ| ≤ R + D := by
    intro ψ hψ
    rcases hψ with hψ | hψ
    · have hzψ := root_restrict_eq_zero_of_isCentral i zc hZc.1.1.1 hZc.1.2 hψ.1.1
      change |characterLog F T.toGrp (aT * bT) ψ| ≤ R + D
      rw [characterLog_mul, AddMonoidHom.add_apply]
      have haψ : characterLog F T.toGrp aT ψ = 0 := by
        rw [show aT = map F Z.toGrp T.toGrp (CommGroupScheme.groupHom zc) a from rfl,
          characterLog_map]
        change logNormHom F Z a (zc ≫ ψ) = 0
        rw [hzψ, map_zero]
      have hbψ : characterLog F T.toGrp bT ψ = logNormHom F T₀ b.val (j ≫ ψ) := by
        rw [show bT = map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) b.val from rfl,
          characterLog_map]
        rfl
      rw [haψ, zero_add, hbψ]
      exact (hRoots ψ hψ).trans (le_add_of_nonneg_right hD)
    · obtain ⟨q, hq⟩ := e.surjective ⟨ψ, hψ⟩
      rw [← show torusCharacterRestrict i (χ q) = ψ from (hχ q).trans (congrArg Subtype.val hq)]
      have heval : logNormHom F T ab.val (torusCharacterRestrict i (χ q)) =
          characterLog F G (map F T.toGrp G i ab.val) (χ q) := by
        rw [characterLog_map]
        rfl
      rw [heval, hab]
      have heq : characterLog F G (z * positiveMap F G T i T₀ j b) (χ q) =
          characterLog F G (z * positiveMap F G T i T₀ j b * ω) (χ q) -
            characterLog F G ω (χ q) := by
        rw [characterLog_mul F G (z * positiveMap F G T i T₀ j b) ω,
          AddMonoidHom.add_apply, add_sub_cancel_right]
      rw [heq]
      have := Finset.single_le_sum (f := fun q => max 0 (Dq q))
        (fun q _ => le_max_left 0 (Dq q)) (Finset.mem_univ q)
      exact (abs_sub _ _).trans (add_le_add (hChars q)
        ((hDq q ω hω).trans ((le_max_right _ _).trans this)))
  let g := z * positiveMap F G T i T₀ j b * ω
  have hTop : adelicHeight F G rho g ≤ A * B * Real.exp (rate * (R + D)) := by
    calc
      _ ≤ adelicHeight F G rho (z * positiveMap F G T i T₀ j b) *
          adelicHeight F G rho ω := adelicHeight_mul_le F G rho hN _ _
      _ ≤ (A * Real.exp (rate * (R + D))) * B := by
        apply mul_le_mul _ (hωBound ω hω)
          (zero_le_one.trans (one_le_adelicHeight F G rho hN ω)) (by positivity)
        rw [← hab]
        exact hHeight ab _ (add_nonneg hR hD) hBounds
      _ = _ := by ring
  have hNorm : max 1 (adelicSourceNorm F G rho g) ≤ adelicHeight F G rho g := by
    refine max_le (one_le_adelicHeight F G rho hN g) ?_
    rw [adelicHeight_eq_scalar_mul_sourceNorm]
    exact le_mul_of_one_le_left (adelicSourceNorm_pos F G rho hN g).le
      (one_le_pow₀ (by exact_mod_cast hN))
  have hLog := Real.log_le_log (zero_lt_one.trans_le (le_max_left 1 (adelicSourceNorm F G rho g)))
    (hNorm.trans hTop)
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hLog
  change 1 + Real.log (max 1 (adelicSourceNorm F G rho g)) ≤ max C₀ rate * (1 + R)
  calc
    _ ≤ C₀ + rate * R := by dsimp [C₀]; linarith
    _ ≤ max C₀ rate + max C₀ rate * R :=
      add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
    _ = _ := by ring

end Langlands.Global

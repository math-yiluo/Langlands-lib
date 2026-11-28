import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Global.CuspidalTestExpansion.ProperPiece
import Langlands.Global.AdelicLeadingCuspidalPairing

/-! # Split-component shift equations for relative Eisenstein series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily.NestedLeviParabolic

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {L J : StandardIndex F G fam.i fam.ν}
  (t : NestedLeviParabolic fam L J)

local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "ΓL" => parabolicQuotientSubgroup F (fam.p L) (fam.iU L) (fam.l L)
local notation "ΓJ" => rationalImage F (fam.p J)

attribute [local instance] positiveSplitComponentCommGroup

/-- The rational parabolic cosets indexing a relative Eisenstein series in the target Levi. -/
abbrev RelativeCosets :=
  RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J)

/-- The relative series on ambient adelic points. -/
def relativeEisensteinSeries (f : Fun) : Fun :=
  fun g => ∑' c : t.RelativeCosets, f (((c.out : ΓJ) : AdelicGroupPoints F G) * g)

/-- Absolute summability at every ambient argument of the relative series. -/
def HasSummableRelativeSeries (f : Fun) : Prop :=
  ∀ g, Summable (fun c : t.RelativeCosets => f (((c.out : ΓJ) : AdelicGroupPoints F G) * g))

private theorem rationalImage_inclusion_le :
    rationalImage F (t.inclusion ≫ fam.p J) ≤ ΓL := by
  rw [t.inclusion_comp]
  exact rationalImage_le_parabolicQuotientSubgroup (fam.p L) (fam.iU L) (fam.l L)
    (fam.isCompatible L).levi (fam.isUnipotentRadical L)

private theorem unnormalizedAction_preserves_invariance (hLJ : L ≤ J)
    {f : Fun} (hf : IsLeftInvariantUnder F G ΓL f) (a : fam.positiveSplitComponent J) :
    IsLeftInvariantUnder F G ΓL (fam.unnormalizedAction J a f) := by
  rw [← fam.unnormalizedAction_splitLift hLJ a]
  exact ((fam.isParabolicGeneratorInvariant_of_isLeftInvariantUnder L hf).adelicLeftShift
    fam (fam.splitLift hLJ a)).isLeftInvariantUnder fam

private theorem eval_relativeCoset_unnormalizedAction (hLJ : L ≤ J)
    {f : Fun} (hf : IsLeftInvariantUnder F G ΓL f) (a : fam.positiveSplitComponent J)
    (g : AdelicGroupPoints F G) (c : t.RelativeCosets) :
    fam.unnormalizedAction J a f (((c.out : ΓJ) : AdelicGroupPoints F G) * g) =
      f (((c.out : ΓJ) : AdelicGroupPoints F G) * (map F (fam.P J) G (fam.p J) a.val * g)) := by
  obtain ⟨q, hq, m, hrep⟩ := t.exists_mul_leviRational _ (c.out : ΓJ).2
  have hm := fam.commute_positiveSplitComponent_levi J a (rational F (fam.M J) m)
  have hinv := unnormalizedAction_preserves_invariance hLJ hf a
  have hq' := t.rationalImage_inclusion_le hq
  simp only [hrep, mul_assoc, hinv q hq', hf q hq']
  unfold unnormalizedAction
  rw [← mul_assoc, hm.eq, mul_assoc]

/-- Relative summation commutes with left translation by the split component of the outer
parabolic, and such a translation preserves absolute summability. -/
theorem relativeEisensteinSeries_unnormalizedAction (hLJ : L ≤ J)
    {f : Fun} (hf : IsLeftInvariantUnder F G ΓL f) (a : fam.positiveSplitComponent J) :
    t.relativeEisensteinSeries (fam.unnormalizedAction J a f) =
      fam.unnormalizedAction J a (t.relativeEisensteinSeries f) ∧
    (t.HasSummableRelativeSeries f →
      t.HasSummableRelativeSeries (fam.unnormalizedAction J a f)) := by
  refine ⟨funext fun g => ?_, fun h g => ?_⟩
  · exact tsum_congr (t.eval_relativeCoset_unnormalizedAction hLJ hf a g)
  · exact (h (map F (fam.P J) G (fam.p J) a.val * g)).congr
      (fun c => (t.eval_relativeCoset_unnormalizedAction hLJ hf a g c).symm)

private def relativeSeriesSubmodule : Submodule ℂ Fun where
  carrier := {f | IsLeftInvariantUnder F G ΓL f ∧ t.HasSummableRelativeSeries f}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => summable_zero⟩
  add_mem' {f h} hf hh := ⟨fun a ha g => by simp only [Pi.add_apply, hf.1 a ha g, hh.1 a ha g],
    fun g => (hf.2 g).add (hh.2 g)⟩
  smul_mem' c f hf := ⟨fun a ha g => by simp only [Pi.smul_apply, hf.1 a ha g],
    fun g => (hf.2 g).mul_left c⟩

include t in
/-- Relative summation intertwines every element of the split-component group algebra on the
invariant functions with everywhere absolutely summable series. -/
theorem relativeEisensteinSeries_shiftAlgHom (hLJ : L ≤ J)
    {f : Fun} (hf : IsLeftInvariantUnder F G ΓL f) (hs : t.HasSummableRelativeSeries f)
    (D : MonoidAlgebra ℂ (fam.positiveSplitComponent J)) :
    t.relativeEisensteinSeries (fam.shiftAlgHom J D f) =
      fam.shiftAlgHom J D (t.relativeEisensteinSeries f) := by
  let S := t.relativeSeriesSubmodule
  have hstable (a : fam.positiveSplitComponent J) (v : Fun) (hv : v ∈ S) :
      fam.unnormalizedAction J a v ∈ S := by
    change IsLeftInvariantUnder F G ΓL v ∧ t.HasSummableRelativeSeries v at hv
    exact ⟨unnormalizedAction_preserves_invariance hLJ hv.1 a,
      (t.relativeEisensteinSeries_unnormalizedAction hLJ hv.1 a).2 hv.2⟩
  refine fam.shiftAlgHom_intertwine S hstable t.relativeEisensteinSeries ?_ ?_ ?_ D f ⟨hf, hs⟩
  · intro v hv w hw
    have hvs : t.HasSummableRelativeSeries v := hv.2
    have hws : t.HasSummableRelativeSeries w := hw.2
    funext g
    exact (hvs g).tsum_add (hws g)
  · intro c v _
    funext g
    exact tsum_mul_left
  · intro a v hv
    exact (t.relativeEisensteinSeries_unnormalizedAction hLJ hv.1 a).1

/-- Any affine exponent of a smaller parabolic gives a shift equation on its relative series
by evaluating the raw eigenvalue at the lift of a positive point of the containing parabolic. -/
def RelativeSeriesShiftStatement (hLJ : L ≤ J)
    (lam : ComplexCharacterParameter F (fam.P L)) (k : ℕ) (f : Fun) : Prop :=
  IsLeftInvariantUnder F G ΓL f →
  t.HasSummableRelativeSeries f →
  fam.HasPolynomialOrbit L lam k f →
  ∀ a : fam.positiveSplitComponent J,
    fam.shiftAlgHom J ((MonoidAlgebra.of ℂ (fam.positiveSplitComponent J) a -
      algebraMap ℂ _ (parameterPower F (fam.P L) lam (fam.splitLift hLJ a).val)) ^ (k + 1))
        (t.relativeEisensteinSeries f) = 0

/-- Apply the polynomial-orbit equation and transfer it through relative summation. -/
theorem relativeEisensteinSeries_shift (hLJ : L ≤ J)
    (lam : ComplexCharacterParameter F (fam.P L)) (k : ℕ) (f : Fun) :
    t.RelativeSeriesShiftStatement hLJ lam k f := by
  intro hf hs hp a
  rw [← t.relativeEisensteinSeries_shiftAlgHom hLJ hf hs, fam.shiftAlgHom_factor_eq_zero hLJ hp a]
  funext g
  change (∑' _ : t.RelativeCosets, (0 : ℂ)) = 0
  exact tsum_zero

/-- One raw split-shift factor per exponent of the integrand gives an annihilating product
for the relative series. Only the series of the full integrand is required to be summable. -/
theorem relativeEisensteinSeries_shift_finsetSum {I : Type*} (hLJ : L ≤ J)
    (s : Finset I) (lam : I → ComplexCharacterParameter F (fam.P L)) (k : I → ℕ)
    (a : I → fam.positiveSplitComponent J) (c : I → Fun)
    {f : Fun} (hf : IsLeftInvariantUnder F G ΓL f) (hs : t.HasSummableRelativeSeries f)
    (hsum : f = ∑ i ∈ s, c i) (hpol : ∀ i ∈ s, fam.HasPolynomialOrbit L (lam i) (k i) (c i)) :
    fam.shiftAlgHom J (∏ i ∈ s, (MonoidAlgebra.of ℂ (fam.positiveSplitComponent J) (a i) -
      algebraMap ℂ _ (parameterPower F (fam.P L) (lam i) (fam.splitLift hLJ (a i)).val)) ^ (k i + 1))
        (t.relativeEisensteinSeries f) = 0 := by
  classical
  let z (i : I) := parameterPower F (fam.P L) (lam i) (fam.splitLift hLJ (a i)).val
  let D : MonoidAlgebra ℂ (fam.positiveSplitComponent J) :=
    ∏ i ∈ s, (MonoidAlgebra.of ℂ _ (a i) - algebraMap ℂ _ (z i)) ^ (k i + 1)
  have hkill : fam.shiftAlgHom J D f = 0 := by
    rw [hsum, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    exact fam.shiftAlgHom_prod_eq_zero s a z (fun j => k j + 1) hi
      (fam.shiftAlgHom_factor_eq_zero hLJ (hpol i hi) (a i))
  change fam.shiftAlgHom J D (t.relativeEisensteinSeries f) = 0
  rw [← t.relativeEisensteinSeries_shiftAlgHom hLJ hf hs, hkill]
  funext g
  change (∑' _ : t.RelativeCosets, (0 : ℂ)) = 0
  exact tsum_zero

end Langlands.Global.StandardParabolicFamily.NestedLeviParabolic

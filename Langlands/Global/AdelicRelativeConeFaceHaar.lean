import Langlands.Global.AdelicRelativeConeIntegralRecombination
import Langlands.Global.AdelicCharacteristicSplitVolume

/-! # Actual relative split Haar in the complementary coroot coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "B" => relativePositiveSubgroup (fam.l Q ≫ fam.p Q) (fam.a Q)
local notation "RQ" => fam.relativeSimpleRoots Q
local notation "RI" => fam.relativeSimpleRoots I

/-- Haar on the actual relative positive split subgroup, restricted to the characteristic
split shell, is a fixed positive scalar times the complementary coroot Lebesgue measure.
The coordinate map also records the ambient minimal height of every split point. -/
def RelativeConeFaceHaarStatement {n : ℕ} (e : Fin n ≃ RI) (hIQ : I ≤ Q) : Prop :=
  ∀ da : Measure B, da.IsHaarMeasure →
    ∃ (f : B → fam.RelativeConeSplitCoordinates I e Q) (c : ℝ≥0),
      0 < c ∧
      (∀ b, fam.relativeSplitVector Q (fun α => f b ((fam.relativeConeSplitIndex I e hIQ).symm α)) =
        fam.minimalHeight hK (fam.relativeSplitPoint Q b)) ∧
      ∀ Tp S : V T, MeasurePreserving f (da.restrict (fam.characteristicSplitHeightRegion Q hK Tp S))
        ((c : ℝ≥0∞) • volume.restrict (fam.relativeConeFaceStrictBase I e hIQ Tp S))

set_option maxHeartbeats 2300000 in
/-- Transport the exact projected-coroot chart through the complementary index equivalence,
then restrict the measures to the actual split shell. -/
theorem relativeConeFaceHaar {n : ℕ} (e : Fin n ≃ RI) (hIQ : I ≤ Q) :
    fam.RelativeConeFaceHaarStatement I Q hK e hIQ := by
  intro da hda
  obtain ⟨L, hL, hHaar⟩ := fam.relativeCorootHaar Q
  obtain ⟨c, hc, hpres⟩ := hHaar da hda
  let q := fam.relativeConeSplitIndex I e hIQ
  let f (b : B) : fam.RelativeConeSplitCoordinates I e Q := fun j => (L b).toAdd (q j)
  let g (y : fam.RelativeConeSplitCoordinates I e Q) : B :=
    L.symm (Multiplicative.ofAdd (fun α => y (q.symm α)))
  have hfg : ∀ y, f (g y) = y := by
    intro y
    funext j
    have he : L (g y) = Multiplicative.ofAdd (fun α => y (q.symm α)) := L.apply_symm_apply _
    change (L (g y)).toAdd (q j) = y j
    rw [he]
    change y (q.symm (q j)) = y j
    rw [q.symm_apply_apply]
  have hg : Measurable g := by
    have h : Continuous (fun y : fam.RelativeConeSplitCoordinates I e Q =>
        (Multiplicative.ofAdd (fun α => y (q.symm α)) : Multiplicative (RQ → ℝ))) :=
      continuous_pi fun α => continuous_apply (q.symm α)
    exact (L.symm.continuous.comp h).measurable
  have hfheight (b : B) : fam.relativeSplitVector Q (fun α => f b (q.symm α)) =
      fam.minimalHeight hK (fam.relativeSplitPoint Q b) := by
    obtain ⟨t, ht, hlog⟩ := (hL b).1
    change fam.relativeSplitPoint Q b = _ at ht
    rw [ht, minimalHeight, fam.minimalHeight_eq_of_torusLog hK _ _ hlog]
    rw [fam.relativeSplitVector_apply Q]
    simp only [f, q.apply_symm_apply]
  refine ⟨f, c, hc, hfheight, fun Tp S => ?_⟩
  let H := fam.characteristicSplitHeightRegion Q hK Tp S
  let U := fam.relativeConeFaceStrictBase I e hIQ Tp S
  have hpre : f ⁻¹' U = H := by
    ext b
    change fam.relativeSplitVector Q (fun α => f b (q.symm α)) ∈
      ArthurTruncation.characteristicSplitShell fam.connectedReductive fam.maximalSplit D Q Tp S ↔ _
    rw [hfheight]
    rfl
  have hfinite := (standardLeviCentralDirections.1 F G fam.connectedReductive T fam.i
    fam.maximalSplit fam.ν fam.generic Q.val Q.property).2.1
  let : Module.Finite ℝ (V T) := hfinite
  let eT := (Module.finBasis ℝ (V T)).equivFun
  have hH : MeasurableSet H := (fam.characteristicSplitVolume Q hK eT).1 Tp S
  have hU : MeasurableSet U := by
    rw [show U = g ⁻¹' H by rw [← hpre, ← preimage_comp]; simp [Function.comp_def, hfg]]
    exact hH.preimage hg
  let r := MeasurableEquiv.piCongrLeft (fun _ : {j : Fin n // j ∉ fam.relativeConeFace I e Q} => ℝ) q.symm
  have hr := volume_measurePreserving_piCongrLeft
    (fun _ : {j : Fin n // j ∉ fam.relativeConeFace I e Q} => ℝ) q.symm
  have hf : f = r ∘ (fun b : B => (L b).toAdd) := by
    funext b j
    have he := MeasurableEquiv.piCongrLeft_apply_apply q.symm (β := fun _ => ℝ) (L b).toAdd (q j)
    rw [q.symm_apply_apply] at he
    exact he.symm
  have hmap : MeasurePreserving f da ((c : ℝ≥0∞) • volume) := by
    rw [hf]
    refine ⟨hr.measurable.comp hpres.measurable, ?_⟩
    rw [← Measure.map_map hr.measurable hpres.measurable, hpres.map_eq,
      Measure.map_smul _ hr.measurable.aemeasurable, hr.map_eq]
    rfl
  have hrest := hmap.restrict_preimage hU
  rw [hpre, Measure.restrict_smul] at hrest
  exact hrest

end Langlands.Global.StandardParabolicFamily

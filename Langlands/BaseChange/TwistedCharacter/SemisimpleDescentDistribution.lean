import Langlands.BaseChange.TwistedCharacter.SemisimpleDescentPushforward
import Langlands.HarmonicAnalysis.Distribution.HaarTensorFactorization

/-! # Invariant distributions obtained by semisimple descent -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure Set Function HarmonicAnalysis _root_.Topology
open Hecke.TestFunction (pullback)

variable {F R : Type*} [NontriviallyNormedField F] [ProperSpace F] [NormedRing R]
  [NormedAlgebra F R] [CompleteSpace R] [FiniteDimensional F R] (α : R ≃ₐ[F] R)

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α

/-- The action `x ↦ g x α(g)⁻¹` on the translated component. -/
def adjointComponentHomeomorph (g : Rˣ) : Rˣ ≃ₜ Rˣ :=
  (Homeomorph.mulLeft g).trans (Homeomorph.mulRight (Units.map α.toMonoidHom g)⁻¹)

omit [CompleteSpace R] in
private theorem mem_adjointConjugationDomain_conj_iff (u : Sˣ) (y : S) :
    y ∈ U ↔ UnitConjugation.conjugationHomeomorph u y ∈ U :=
  ⟨adjointConjugationDomain_conjugation α u, fun hy => by
    have h := adjointConjugationDomain_conjugation α u⁻¹ hy
    rwa [← UnitConjugation.conjugationHomeomorph_symm u,
      Homeomorph.symm_apply_apply] at h⟩

/-- Unit conjugation restricted to the invariant semisimple descent domain. -/
def adjointSliceHomeomorph (u : Sˣ) : U ≃ₜ U :=
  (UnitConjugation.conjugationHomeomorph u).subtype (mem_adjointConjugationDomain_conj_iff α u)

omit [CompleteSpace R] in
private theorem adjointConjugationOnUnits_left (g : Rˣ) (z : Rˣ × U) :
    adjointConjugationOnUnits α (g * z.1, z.2) =
      adjointComponentHomeomorph α g (adjointConjugationOnUnits α z) := by
  simp [adjointConjugationOnUnits, adjointComponentHomeomorph, map_mul, mul_inv_rev, mul_assoc]

omit [CompleteSpace R] in
private theorem adjointConjugationOnUnits_right (u : Sˣ) (z : Rˣ × U) :
    let v := Units.map (adjointFixedAlgebra α).val.toMonoidHom u
    adjointConjugationOnUnits α (z.1 * v⁻¹, adjointSliceHomeomorph α u z.2) =
      adjointConjugationOnUnits α z := by
  let v := Units.map (adjointFixedAlgebra α).val.toMonoidHom u
  let m (y : U) : Rˣ := Units.map (adjointFixedAlgebra α).val.toMonoidHom y.property.1.unit
  let a := Units.map α.toMonoidHom
  have hv : a v = v := Units.ext (u.val.property : α v.val = v.val)
  have hm (y : U) : m (adjointSliceHomeomorph α u y) = v * m y * v⁻¹ := by
    have hval (y : U) : (m y).val = 1 + y.val.val := by
      change ((adjointFixedAlgebra α).val (↑(y.property.1.unit : Sˣ))) = _
      rw [IsUnit.unit_spec]
      rfl
    apply Units.ext
    simp only [Units.val_mul, hval]
    change 1 + v.val * y.val.val * ((v⁻¹ : Rˣ) : R) = _
    rw [mul_add, mul_one, add_mul, Units.mul_inv]
  change (z.1 * v⁻¹) * m (adjointSliceHomeomorph α u z.2) * (a (z.1 * v⁻¹))⁻¹ =
    z.1 * m z.2 * (a z.1)⁻¹
  rw [hm, map_mul, map_inv, hv]
  group

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]
  [MeasurableSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)]

omit [MeasurableSpace Rˣ] [BorelSpace Rˣ] in
private theorem adjointSliceHomeomorph_measurePreserving (ν : Measure S) (u : Sˣ)
    (hν : MeasurePreserving (UnitConjugation.conjugationHomeomorph u) ν ν) :
    MeasurePreserving (adjointSliceHomeomorph α u) (ν.comap Subtype.val) (ν.comap Subtype.val) := by
  let e := adjointSliceHomeomorph α u
  let c := UnitConjugation.conjugationHomeomorph u
  let j : U → S := Subtype.val
  have hU := isOpen_adjointConjugationDomain α
  have hj := hU.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hrange : range j = U := Subtype.range_coe
  have hpre : c ⁻¹' U = U := Set.ext fun y => (mem_adjointConjugationDomain_conj_iff α u y).symm
  refine ⟨e.continuous.measurable, ?_⟩
  change (ν.comap j).map e = ν.comap j
  apply hj.map_injective
  rw [map_map hj.measurable e.continuous.measurable, show j ∘ e = c ∘ j from rfl,
    ← map_map hν.measurable hj.measurable, hj.map_comap, hrange, ← hpre,
    ← restrict_map hν.measurable hU.measurableSet, hν.map_eq, hpre]

/-- Pullback along the descent submersion gives the Haar distribution of the
unit group tensored with an invariant distribution on the slice. -/
def SemisimpleDescentDistributionStatement (μ : Measure Rˣ) [IsFiniteMeasureOnCompacts μ] (ν : Measure S)
    (D : Distribution Rˣ) : Prop :=
  ∀ P : SchwartzBruhat (Rˣ × U) →ₗ[ℂ] SchwartzBruhat Rˣ,
    SchwartzBruhat.IsTestPushforward (μ.prod (ν.comap Subtype.val)) μ
      (adjointConjugationOnUnits α) P →
    (∀ g : Rˣ, Distribution.pushforward (adjointComponentHomeomorph α g) D = D) →
    (∀ u : Sˣ, MeasurePreserving (UnitConjugation.conjugationHomeomorph u) ν ν) →
    ∃ T : Distribution U,
      D.comp P = Distribution.tensor (Distribution.ofMeasure μ) T ∧
      ∀ u : Sˣ, Distribution.pushforward (adjointSliceHomeomorph α u) T = T

variable [T2Space Rˣ] [LocallyCompactSpace Rˣ] [TotallyDisconnectedSpace Rˣ]
  [SecondCountableTopology Rˣ] [SecondCountableTopology (adjointFixedAlgebra α)]

/-- The unit-group left covariance factors the product distribution; right
translation paired with fixed-unit conjugation gives the invariance of the slice. -/
theorem semisimpleDescentDistribution (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (ν : Measure S) [SFinite (ν.comap (Subtype.val : U → S))] (D : Distribution Rˣ) :
    SemisimpleDescentDistributionStatement α μ ν D := by
  intro P hP hD hν
  have : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  let ρ := ν.comap (Subtype.val : U → S)
  let Q := D.comp P
  have hLeft : Distribution.IsLeftInvariantInFirstFactor Q := by
    intro a
    let e := (Homeomorph.mulLeft a).prodCongr (Homeomorph.refl U)
    let E := adjointComponentHomeomorph α a
    have he : MeasurePreserving e (μ.prod ρ) (μ.prod ρ) :=
      (measurePreserving_mul_left μ a).prod (MeasurePreserving.id ρ)
    have hE : MeasurePreserving E μ μ :=
      (measurePreserving_mul_right μ _).comp (measurePreserving_mul_left μ a)
    ext f
    change D (P (pullback e f)) = D (P f)
    rw [hP.pullback (μ.prod ρ) μ e E he hE (adjointConjugationOnUnits_left α a),
      ← Distribution.pushforward_apply, hD a]
  obtain ⟨T, hT, _⟩ := Distribution.haarTensorFactorization μ Q hLeft
  refine ⟨T, hT, fun u => ?_⟩
  let v := Units.map (adjointFixedAlgebra α).val.toMonoidHom u
  let e := (Homeomorph.mulRight v⁻¹).prodCongr (adjointSliceHomeomorph α u)
  apply Distribution.pushforward_eq_of_haarTensor_symmetry μ hT v⁻¹
  have he : MeasurePreserving e (μ.prod ρ) (μ.prod ρ) :=
    (measurePreserving_mul_right μ v⁻¹).prod (adjointSliceHomeomorph_measurePreserving α ν u (hν u))
  ext f
  change D (P (pullback e f)) = D (P f)
  rw [hP.pullback (μ.prod ρ) μ e (Homeomorph.refl Rˣ) he (MeasurePreserving.id μ)
    (adjointConjugationOnUnits_right α u)]
  congr 1

end Langlands.BaseChange

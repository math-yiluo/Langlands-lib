import Langlands.Representation.Aubert.CorrectedSupportOrbitQuotient
import Langlands.Representation.Aubert.CorrectedSupportTransitions
import Langlands.Representation.Geometric.ParabolicOrbitComparisonData
import Langlands.Representation.Geometric.TypeASolomonCoefficientProof

/-! Actual radical intersections and orbit representatives across source cuts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear

universe uR

variable {R : Type uR} [CommRing R] {n : ℕ} {B D : BlockShape n}
  (C : BlockShape n) {w : Equiv.Perm (Fin n)}

/-- On the target radical, adding source cuts does not change the actual
stabilizer intersection when the permutation increases on source blocks. -/
theorem parabolicOrbitRadicalIntersection_eq_of_sourceCuts
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w) :
    parabolicOrbitRadicalIntersection R B C w =
      parabolicOrbitRadicalIntersection R D C w := by
  ext u
  change (permutation n R w)⁻¹ * u.val.val * ((permutation n R w)⁻¹)⁻¹ ∈
      B.parabolic R ↔
    (permutation n R w)⁻¹ * u.val.val * ((permutation n R w)⁻¹)⁻¹ ∈
      D.parabolic R
  simp only [inv_inv]
  constructor
  · intro hu
    apply (mem_parabolic_iff_blockIndex R D _).mpr
    intro a b hD
    have hba : b < a := by
      by_contra hn
      exact (not_le_of_gt hD) (blockIndex_monotone D (le_of_not_gt hn))
    rcases (blockIndex_monotone B hba.le).lt_or_eq with hB | hB
    · exact (mem_parabolic_iff_blockIndex R B _).mp hu a b hB
    · have hwba := TypeASolomon.lt_of_sameBlock B hw hba hB
      have hrad : u.val.val ∈ C.unipotentSubgroup R := ⟨u.val, u.property, rfl⟩
      have hz := (Aubert.mem_unipotentSubgroup_iff_blockIndex C _).mp hrad
        (w a) (w b) (blockIndex_monotone C hwba.le)
      have hne : w a ≠ w b := fun he => hba.ne (w.injective he).symm
      have hentry :
          ((permutation n R w)⁻¹ * u.val.val * permutation n R w) a b =
            u.val.val (w a) (w b) := by
        simpa only [map_inv, inv_inv] using
          permutation_conjugate_entry n R w⁻¹ u.val.val a b
      simpa only [hentry, hne, ↓reduceIte] using hz
  · intro hu
    exact Aubert.parabolic_le_of_cuts_subset (R := R) h hu

/-- The actual radical stabilizers are canonically the same group across source
cuts. Its underlying target-radical element is unchanged. -/
def parabolicOrbitRadicalIntersectionEquiv
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w) :
    parabolicOrbitRadicalIntersection R B C w ≃*
      parabolicOrbitRadicalIntersection R D C w :=
  MulEquiv.subgroupCongr (parabolicOrbitRadicalIntersection_eq_of_sourceCuts C h hw)

@[simp]
theorem parabolicOrbitRadicalIntersectionEquiv_apply_val
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w)
    (u : parabolicOrbitRadicalIntersection R B C w) :
    (parabolicOrbitRadicalIntersectionEquiv C h hw u).val = u.val := rfl

end Langlands.Geometric

namespace Langlands.Aubert.Support

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
  {B D : BlockShape n} (C : BlockShape n)
  (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hw : w ∈ weylSupport B C θ) (h : B.cuts ⊆ D.cuts)

/-- On actual support representatives, the corrected orbit restriction square
for a cut map commutes with the actual coefficient quotient projection. -/
theorem correctedInductionOrbit_cutMap_projection_eval :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A))
      (q : C.parabolic F.Carrier),
      let fD : (correctedInductionSupport T D C θ).representation
          ((T.normalizedJacquetFunctor D).obj A) :=
        ⟨Transition.cutMap T A.representation h f.val,
          cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩
      let value := Induction.eval _ _
        (((correctedInductionOrbitIso T B C θ w hθ hLower hw).hom.app
            ((T.normalizedJacquetFunctor B).obj A)).hom
          (((correctedInductionSupport T B C (θ \ {w})).quotientProjection
            (correctedInductionSupport T B C θ)
            ((T.normalizedJacquetFunctor B).obj A)).hom f)).val q
      Induction.eval _ _
          (((correctedInductionOrbitIso T D C θ w hθ hLower
            (weylSupport_mono_source_cuts C h θ hw)).hom.app
              ((T.normalizedJacquetFunctor D).obj A)).hom
            (((correctedInductionSupport T D C (θ \ {w})).quotientProjection
              (correctedInductionSupport T D C θ)
              ((T.normalizedJacquetFunctor D).obj A)).hom fD)).val q =
        Transition.quotient A.representation
          (unipotentSubgroup_le_of_cuts_subset h) value := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro f q
  dsimp only
  rw [correctedInductionOrbitIso_hom_projection_eval,
    correctedInductionOrbitIso_hom_projection_eval]
  rfl

end Langlands.Aubert.Support

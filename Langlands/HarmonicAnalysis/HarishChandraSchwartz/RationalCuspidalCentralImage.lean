import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralProjection

/-! # Exact integral images of the actual cuspidal Schwartz spaces

The raw images are sets defined without an analytic convergence premise. Their spans
are explicitly distinguished from these sets. Convergence, or the auxiliary
`CentralWeights`, identifies each span with the exact image.
-/

noncomputable section

universe u uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Images

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
  {A : Subgroup Γ} [MeasurableSpace A] {Ξ σ : Γ → ℝ}
  (E : Submodule ℂ (Space Ξ σ)) (muA : Measure A) (χ : A →* ℂˣ)

/-- The exact image under the raw integral, with no convergence hypothesis. -/
def schwartzCentralIntegralImage : Set (Γ → ℂ) :=
  {f | ∃ φ : Space Ξ σ, φ ∈ E ∧ centralProjection muA χ φ = f}

/-- A convenient submodule; it is not identified with the raw image by definition. -/
def schwartzCentralIntegralSpan : Submodule ℂ (Γ → ℂ) :=
  Submodule.span ℂ (schwartzCentralIntegralImage E muA χ)

/-- Absolute convergence of every defining central integral on `E`. -/
def CentralIntegralConvergesOn : Prop :=
  ∀ φ : Space Ξ σ, φ ∈ E → ∀ g : Γ,
    Integrable (fun a : A => (((χ a)⁻¹ : ℂˣ) : ℂ) * φ ((a : Γ) * g)) muA

theorem schwartzCentralIntegralImage_mono {E' : Submodule ℂ (Space Ξ σ)} (h : E' ≤ E) :
    schwartzCentralIntegralImage E' muA χ ⊆ schwartzCentralIntegralImage E muA χ := by
  rintro f ⟨φ, hφ, rfl⟩
  exact ⟨φ, h hφ, rfl⟩

theorem schwartzCentralIntegralSpan_mono {E' : Submodule ℂ (Space Ξ σ)} (h : E' ≤ E) :
    schwartzCentralIntegralSpan E' muA χ ≤ schwartzCentralIntegralSpan E muA χ :=
  Submodule.span_mono (schwartzCentralIntegralImage_mono E muA χ h)

/-- The actual integral is a linear map on `E` once its convergence has been proved. -/
def centralIntegralOn (h : CentralIntegralConvergesOn E muA χ) : E →ₗ[ℂ] (Γ → ℂ) where
  toFun φ := centralProjection muA χ (φ.val : Γ → ℂ)
  map_add' φ ψ := by
    funext g
    simp only [centralProjection, Submodule.coe_add, Space.coe_add, Pi.add_apply, mul_add]
    exact integral_add (h φ.val φ.property g) (h ψ.val ψ.property g)
  map_smul' c φ := by
    funext g
    simp only [centralProjection, Submodule.coe_smul, Space.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext a
    ring

theorem range_centralIntegralOn (h : CentralIntegralConvergesOn E muA χ) :
    (LinearMap.range (centralIntegralOn E muA χ h) : Set (Γ → ℂ)) =
      schwartzCentralIntegralImage E muA χ := by
  ext f
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.val, φ.property, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨⟨φ, hφ⟩, rfl⟩

theorem schwartzCentralIntegralSpan_eq_range (h : CentralIntegralConvergesOn E muA χ) :
    schwartzCentralIntegralSpan E muA χ = LinearMap.range (centralIntegralOn E muA χ h) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro f hf
    exact (range_centralIntegralOn E muA χ h).symm ▸ hf
  · rintro f ⟨φ, rfl⟩
    exact Submodule.subset_span ⟨φ.val, φ.property, rfl⟩

theorem coe_schwartzCentralIntegralSpan_eq_image (h : CentralIntegralConvergesOn E muA χ) :
    (schwartzCentralIntegralSpan E muA χ : Set (Γ → ℂ)) =
      schwartzCentralIntegralImage E muA χ := by
  rw [schwartzCentralIntegralSpan_eq_range E muA χ h, range_centralIntegralOn]

variable [IsTopologicalGroup Γ] [OpensMeasurableSpace A] [Nonempty (CompactOpenSubgroup Γ)]

theorem CentralWeights.convergesOn (hw : CentralWeights muA Ξ σ)
    (hχ : IsUnitaryCharacter χ) : CentralIntegralConvergesOn E muA χ :=
  fun φ _ g => hw.integrable_mul_of_mem hχ (Space.coe_mem φ) g

/-- Comparison with the published linear integral map; this is an auxiliary estimate interface. -/
theorem schwartzCentralIntegralSpan_eq_map (hw : CentralWeights muA Ξ σ)
    (hχ : IsUnitaryCharacter χ) :
    schwartzCentralIntegralSpan E muA χ = E.map (Space.centralProjection hw hχ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ, rfl⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨φ, hφ, rfl⟩

end Images

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (muA : Measure (rationalPoints.map s).range) (χ : (rationalPoints.map s).range →* ℂˣ)

abbrev rationalCuspidalCentralImage : Set (rationalPoints G → ℂ) :=
  schwartzCentralIntegralImage (rationalCuspidalSubmodule hKc hPK ρ) muA χ

abbrev rationalCuspidalCentralLevelImage (H : Subgroup (rationalPoints G)) :
    Set (rationalPoints G → ℂ) :=
  schwartzCentralIntegralImage (rationalCuspidalLevel hKc hPK ρ H) muA χ

abbrev rationalCuspidalCentralLeftLevelImage (H : Subgroup (rationalPoints G)) :
    Set (rationalPoints G → ℂ) :=
  schwartzCentralIntegralImage (rationalCuspidalLeftLevel hKc hPK ρ H) muA χ

abbrev rationalCuspidalCentralSpan : Submodule ℂ (rationalPoints G → ℂ) :=
  schwartzCentralIntegralSpan (rationalCuspidalSubmodule hKc hPK ρ) muA χ

abbrev rationalCuspidalCentralLevelSpan (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (rationalPoints G → ℂ) :=
  schwartzCentralIntegralSpan (rationalCuspidalLevel hKc hPK ρ H) muA χ

abbrev rationalCuspidalCentralLeftLevelSpan (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (rationalPoints G → ℂ) :=
  schwartzCentralIntegralSpan (rationalCuspidalLeftLevel hKc hPK ρ H) muA χ

theorem rationalCuspidalCentralLevelImage_subset (H : Subgroup (rationalPoints G)) :
    rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H ⊆
      rationalCuspidalCentralImage hKc hPK ρ muA χ :=
  schwartzCentralIntegralImage_mono _ _ _ (rationalCuspidalLevel_le hKc hPK ρ H)

theorem rationalCuspidalCentralLevelImage_antitone
    {H H' : Subgroup (rationalPoints G)} (h : H' ≤ H) :
    rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H ⊆
      rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H' :=
  schwartzCentralIntegralImage_mono _ _ _ (rationalCuspidalLevel_antitone hKc hPK ρ h)

/-- Under explicit weights the exact raw image is the published `rationalCentralProjection`
image of the actual cuspidal submodule. -/
theorem rationalCuspidalCentralImage_eq_map
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hχ : IsUnitaryCharacter χ) :
    rationalCuspidalCentralImage hKc hPK ρ muA χ =
      ((rationalCuspidalSubmodule hKc hPK ρ).map
        (rationalCentralProjection K.isOpen hKc hPK ρ muA hw hχ) :
          Set (rationalPoints G → ℂ)) := by
  ext f
  rfl

theorem rationalCuspidalCentralLevelImage_eq_map (H : Subgroup (rationalPoints G))
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hχ : IsUnitaryCharacter χ) :
    rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H =
      ((rationalCuspidalLevel hKc hPK ρ H).map
        (rationalCentralProjection K.isOpen hKc hPK ρ muA hw hχ) :
          Set (rationalPoints G → ℂ)) := by
  ext f
  rfl

end Langlands.HarishChandraSchwartz

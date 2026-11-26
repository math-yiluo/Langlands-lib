import Langlands.Global.AdelicSymmetricFamilyDensity

/-! # Realization of finite smooth presentations in the spectral family space -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P M U : I → GroupScheme (Spec (CommRingCat.of F))}
  [∀ i, IsAffine (P i).X.left] [∀ i, LocallyOfFiniteType (P i).X.hom]
  [∀ i, IsAffine (M i).X.left] [∀ i, LocallyOfFiniteType (M i).X.hom] [∀ i, IsAffine (U i).X.left]
  {p : ∀ i, P i ⟶ G} [∀ i, IsClosedImmersion (p i).hom.hom.left]
  {iU : ∀ i, U i ⟶ P i} {l : ∀ i, M i ⟶ P i} {K : Subgroup (AdelicGroupPoints F G)}
  {hK : ∀ i, IsIwasawaCompact (p i) K} {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : ∀ i, Measure (AdelicGroupPoints F (M i))} {n : I → ℕ}
  {e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i)}
  {β : ∀ i, (Fin (n i) → ℝ) → ℝ} {nP : I → ℕ}

local notation "A₂" => (fun i => IsSquareIntegrableInducedForm K (IsIwasawaCompact.isCompact (hK i))
  rho hsmooth hcalc (p i) (iU i) (l i))
local notation "μₕ" => (fun i => inducedL2Measure K (IsIwasawaCompact.isCompact (hK i))
  (l i) (μM i) (e i) (β i))
local notation "Hₕ" => (fun i => inducedHilbertSpace K (IsIwasawaCompact.isCompact (hK i))
  rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i) (β i))
local notation "μₛ" => (fun i => (((nP i : ℝ≥0∞))⁻¹ • spectralMeasure (n i)))

omit [Fintype I] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [∀ i, IsAffine (U i).X.left] [∀ i, IsClosedImmersion (p i).hom.hom.left] in
set_option maxHeartbeats 1000000 in
/-- A finite family of weighted `L²` restrictions with smooth compactly supported coefficients
defines an element of the ambient spectral family space with that presentation. -/
theorem exists_smoothCompactFamily_of_finite_forms
    (hnP : ∀ i, nP i ≠ 0)
    {k : I → ℕ} {v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ}
    {c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ}
    (hv : ∀ i j, A₂ i (v i j))
    (hL : ∀ i j, MemLp (inducedRestriction K (p i) (l i) (v i j)) 2 (μₕ i))
    (hc : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j) ∧ HasCompactSupport (c i j)) :
    ∃ Φ : spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP,
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ := by
  let u (i : I) (j : Fin (k i)) : Hₕ i := ⟨(hL i j).toLp _,
    toLp_mem_inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
      (μM i) (e i) (β i) (hv i j) (hL i j)⟩
  let f (i : I) (x : Fin (n i) → ℝ) : Hₕ i := ∑ j, c i j x • u i j
  have hF (i : I) : MemLp (f i) 2 (μₛ i) := by
    let : IsFiniteMeasureOnCompacts (μₛ i) := isFiniteMeasureOnCompacts_smul_spectralMeasure _ (hnP i)
    refine memLp_finsetSum (f := fun j x => c i j x • u i j) Finset.univ fun j _ => ?_
    exact ((hc i j).1.continuous.smul continuous_const).memLp_of_hasCompactSupport (hc i j).2.smul_right
  let Φ : spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP :=
    WithLp.toLp 2 fun i => (hF i).toLp (f i)
  refine ⟨Φ, hv, hc, fun i => ?_⟩
  have hFae : ⇑(Φ i) =ᵐ[μₛ i] f i := (hF i).coeFn_toLp
  have hν : ae (μₛ i) = ae (spectralMeasure (n i)) :=
    (ae_smul_spectralMeasure_eq _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))).trans
      (ae_spectralMeasure_eq _).symm
  rw [hν] at hFae
  filter_upwards [hFae] with x hx
  rw [hx]
  change ⇑((∑ j, c i j x • u i j : Hₕ i) : Lp ℂ 2 (μₕ i)) =ᵐ[μₕ i] _
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using
    (sum_smul_toLp_mem_inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
      (μM i) (e i) (β i) (hv i) (hL i) (fun j => c i j x)).2

end Langlands.Global

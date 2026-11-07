import Langlands.LocalFactor.Abelian.ZetaContinuation

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

/-- The shell coefficient before inserting its spectral monomial. -/
def shellCoefficient (π : F.Carrierˣ) (χ : Character) (μ : LocalHaar)
    (f : F.Carrier → ℂ) (k : ℤ) : ℂ :=
  letI := T.topology
  letI := borel F.Carrier
  ∫ x in integralUnits T,
    f (((π ^ k : F.Carrierˣ) : F.Carrier) * x) * characterExtension T χ x ∂μ.measure

/-- Above the local-constancy cutoff, shell coefficients are constant. -/
theorem shellCoefficient_eq_tail (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (μ : LocalHaar)
    (f : F.Carrier → ℂ) (N k : ℤ) (hk : N ≤ k)
    (hN : ∀ v : F.Carrierˣ, N ≤ T.ord (v : F.Carrier) → f (v : F.Carrier) = f 0) :
    shellCoefficient T π χ μ f k = f 0 *
      (letI := T.topology
       letI := borel F.Carrier
       ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure) := by
  let := T.topology
  let := borel F.Carrier
  rw [shellCoefficient, ← integral_const_mul]
  apply setIntegral_congr_fun (orderShell_compact_measurable T 0).2
  intro x hx
  have ho := (mul_uniformizer_mem_orderShell_iff T π hπ k x).mpr hx
  change f _ * _ = f 0 * _
  have hf : f (((π ^ k : F.Carrierˣ) : F.Carrier) * x) = f 0 :=
    hN (Units.mk0 _ ho.1) (by simpa only [Units.val_mk0, ho.2] using hk)
  rw [hf]

/-- The actual convergent integral is the sum of its shells from any lower support cutoff. -/
theorem hasSum_zeta_shells (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (μ : LocalHaar)
    (f : TestFunction) (L : ℤ)
    (hL : ∀ v : F.Carrierˣ, T.ord (v : F.Carrier) < L → f (v : F.Carrier) = 0)
    (s : ℂ) (hs : ConvergesAt T π χ s) :
    letI := T.topology
    letI := borel F.Carrier
    HasSum (fun n : ℕ => ((χ π : ℂ) * spectralVariable T s) ^ (L + n) *
      shellCoefficient T π χ μ f (L + n)) (zeta T μ.measure f χ s) := by
  let := T.topology
  let := borel F.Carrier
  have hi := zeta_integrable T π hπ χ μ f s hs
  have hh := hasSum_integral_iUnion
    (fun n : ℕ => (orderShell_compact_measurable T (L + n)).2)
    (show Pairwise (fun m n : ℕ =>
      Disjoint (orderShell T (L + m)) (orderShell T (L + n))) from by
        intro m n hmn
        exact pairwise_disjoint_orderShell T (by omega))
    hi.integrableOn
  have he : (∫ x in ⋃ n : ℕ, orderShell T (L + n),
      zetaIntegrand T f χ s x ∂μ.measure) = zeta T μ.measure f χ s :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra hn
      exact hx (support_zetaIntegrand_subset_shells T χ f s L hL hn))
  rw [he] at hh
  simpa only [setIntegral_zeta_orderShell T π hπ, shellCoefficient] using hh

set_option maxHeartbeats 800000 in
/-- Finite shell prefix plus the geometric constant tail. -/
theorem zeta_eq_prefix_add_tail (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (μ : LocalHaar)
    (f : TestFunction) (L N : ℤ) (hLN : L ≤ N)
    (hL : ∀ v : F.Carrierˣ, T.ord (v : F.Carrier) < L → f (v : F.Carrier) = 0)
    (hN : ∀ v : F.Carrierˣ, N ≤ T.ord (v : F.Carrier) → f (v : F.Carrier) = f 0)
    (s : ℂ) (hs : ConvergesAt T π χ s) :
    letI := T.topology
    letI := borel F.Carrier
    let r := (χ π : ℂ) * spectralVariable T s
    let J := (letI := T.topology
              letI := borel F.Carrier
              ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure)
    zeta T μ.measure f χ s =
      (∑ i ∈ Finset.range (N - L).toNat, r ^ (L + i) * shellCoefficient T π χ μ f (L + i)) +
        r ^ N * (f 0 * J) * (1 - r)⁻¹ := by
  let := T.topology
  let := borel F.Carrier
  let r := (χ π : ℂ) * spectralVariable T s
  let J := (letI := T.topology
            letI := borel F.Carrier
            ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure)
  let D := (N - L).toNat
  change zeta T μ.measure f χ s =
    (∑ i ∈ Finset.range D, r ^ (L + i) * shellCoefficient T π χ μ f (L + i)) +
      r ^ N * (f 0 * J) * (1 - r)⁻¹
  have hD : L + (D : ℤ) = N := by dsimp [D]; rw [Int.toNat_of_nonneg (by omega)]; omega
  have hr : ‖r‖ < 1 := (convergesAt_iff_norm_lt_one T π χ s).mp hs
  have hr0 : r ≠ 0 := mul_ne_zero (χ π).ne_zero (spectralVariable_ne_zero T s)
  have hg := ((hasSum_geometric_of_norm_lt_one hr).mul_left (r ^ N)).mul_right (f 0 * J)
  have ht : HasSum (fun i : ℕ =>
      r ^ (L + (i + D : ℕ)) * shellCoefficient T π χ μ f (L + (i + D : ℕ)))
      (r ^ N * (f 0 * J) * (1 - r)⁻¹) := by
    convert hg using 1
    · funext i
      have hk : L + (i + D : ℕ) = N + (i : ℤ) := by push_cast; omega
      rw [shellCoefficient_eq_tail T π hπ χ μ f N _ (by omega) hN, hk,
        zpow_add₀ hr0, zpow_natCast]
    · ring
  have hfull := (hasSum_nat_add_iff
    (f := fun i : ℕ => r ^ (L + i) * shellCoefficient T π χ μ f (L + i)) D).mp ht
  have hz := hasSum_zeta_shells T π hπ χ μ f L hL s hs
  exact hz.unique hfull |>.trans (add_comm _ _)

end Langlands.LocalFactor.PadicAbelian

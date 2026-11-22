import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Integrability of polynomially bounded functions in norm-one Levi tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Pt" => AdelicGroupPoints F G
local notation "L" => fam.M J
local notation "j" => (fam.l J ≫ fam.p J)
local notation "Γ" => rationalNormOneSubgroup F L
local notation "μ" => normOneRationalQuotientHaarMeasure F L
local notation "mG" => map F L G j

/-- A continuous function of polynomial growth, invariant under the
rational Levi, is integrable against a rapid test on the norm-one quotient. -/
def WeightedLeviPairingIntegrabilityStatement {N : ℕ} (rho : MatrixRepresentation G (Fin N)) : Prop :=
  0 < N → ∀ R : Pt → ℂ, Continuous R → IsLeftInvariantUnder F G (rationalImage F j) R →
    ∀ C d : ℝ, 0 ≤ C → 0 ≤ d → (∀ g, ‖R g‖ ≤ C * adelicHeight F G rho g ^ d) →
      ∀ test : AdelicGroupPoints F L → ℂ, Continuous test →
        IsLeftInvariantUnder F L (rationalSubgroup F L) test →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x : NormOneRationalQuotient F L,
          ∃ m : normOneSubgroup F L, LeftCosetSpace.mk Γ m = x ∧
            adelicHeight F G rho (mG m.val) ^ d * ‖test m.val‖ ≤ B) →
        ∀ g : Pt, Integrable (fam.leviPairingIntegrand J R g test) μ

set_option maxHeartbeats 1200000 in
theorem weightedLeviPairingIntegrability {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    WeightedLeviPairingIntegrabilityStatement fam J rho := by
  intro hN R hRc hR C d hC hd hbound test hTestc hTest hRapid g
  let H := adelicHeight F G rho
  let f (m : normOneSubgroup F L) := R (mG m.val * g) * starRingEnd ℂ (test m.val)
  have hf : Continuous f := (hRc.comp (((mG).continuous.comp continuous_subtype_val).mul_const g)).mul
    (Complex.continuous_conj.comp (hTestc.comp continuous_subtype_val))
  have hInv (δ : Γ) (m : normOneSubgroup F L) : f (δ.val * m) = f m := by
    obtain ⟨x, hx⟩ := δ.property
    have he : δ.val.val = rational F L x := (congrArg Subtype.val hx).symm
    have hδ : mG (rational F L x) ∈ rationalImage F j := ⟨x, rfl⟩
    simp only [f, Subgroup.coe_mul, he, map_mul, mul_assoc]
    rw [hR _ hδ, hTest _ ⟨x, rfl⟩]
  let fQ := LeftCosetSpace.lift Γ f hInv
  have hQc : Continuous fQ := LeftCosetSpace.continuous_lift Γ f hInv hf
  have hEq (q : NormOneRationalQuotient F L) : fam.leviPairingIntegrand J R g test q = fQ q := by
    change fQ (LeftCosetSpace.mk Γ q.out) = fQ q
    exact congrArg fQ (Quotient.out_eq q)
  let : IsFiniteMeasure μ :=
    connectedReductiveFiniteVolume F L (fam.isCompatible J).levi.isConnectedReductive
  obtain ⟨B, _, hRep⟩ := hRapid
  have hH (x : Pt) : 0 ≤ H x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
  have hPow (m : normOneSubgroup F L) : H (mG m.val * g) ^ d ≤ H (mG m.val) ^ d * H g ^ d := by
    rw [← Real.mul_rpow (hH _) (hH _)]
    exact Real.rpow_le_rpow (hH _) (adelicHeight_mul_le F G rho hN _ _) hd
  rw [show fam.leviPairingIntegrand J R g test = fQ from funext hEq]
  refine (integrable_const (C * H g ^ d * B)).mono' hQc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨m, hm, hmBound⟩ := hRep q
  rw [← hm]
  change ‖f m‖ ≤ C * H g ^ d * B
  have hCpow : 0 ≤ C * H g ^ d := mul_nonneg hC (Real.rpow_nonneg (hH _) _)
  calc
    ‖f m‖ = ‖R (mG m.val * g)‖ * ‖test m.val‖ := by
      simp only [f, norm_mul, Complex.norm_conj]
    _ ≤ C * H (mG m.val * g) ^ d * ‖test m.val‖ :=
      mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
    _ ≤ C * (H (mG m.val) ^ d * H g ^ d) * ‖test m.val‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hPow m) hC) (norm_nonneg _)
    _ = (C * H g ^ d) * (H (mG m.val) ^ d * ‖test m.val‖) := by ring
    _ ≤ C * H g ^ d * B := mul_le_mul_of_nonneg_left hmBound hCpow

end Langlands.Global.StandardParabolicFamily

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamberHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterHeightProof
import Langlands.Geometry.Building.KPCentralizerNormKernelCompactness
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof

/-! # The actual cuspidal conjugation theorem in relative semisimple rank zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem rankZero_subgroups (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (h0 : simpleRelativeRoots i ν = ∅) :
    IsCentral i ∧ standardUnipotentPoints i ν ∅ = ⊥ := by
  have h := standardParabolicEndpoints F G hG S i hi ν hν
  have hZ : torusCentralizer i = ⊤ := h.2.1.symm.trans (by simpa only [h0] using h.2.2.2.1)
  have hU : standardUnipotent i ν ∅ = ⊥ := by simpa only [h0] using h.2.2.2.2
  refine ⟨(isCentral_iff_torusCentralizer_eq_top i).mpr hZ, ?_⟩
  change (standardUnipotent i ν ∅).carrier _ = _
  rw [hU]
  rfl

private theorem minimalModulus_eq_one_of_trivial_radical
    (hU : standardUnipotentPoints i ν ∅ = ⊥) (p : standardParabolicPoints i ν ∅) :
    rationalMinimalModulus i ν p = 1 := by
  apply closedNormalizerCharacter_eq_one_of_commute _ (isClosed_standardUnipotentPoints i ν ∅)
  intro u hu
  rw [hU, Subgroup.mem_bot] at hu
  simp [hu]

private theorem rationalXi_eq_one_of_trivial_radical
    {K : OpenSubgroup (rationalPoints G)}
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    (hU : standardUnipotentPoints i ν ∅ = ⊥) (g : rationalPoints G) :
    rationalXi hKc hPK g = 1 := by
  simp [rationalXi, xi, iwasawaWeight, minimalModulus_eq_one_of_trivial_radical hU]

local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

open SplitCenterHeight in
/-- A compact common norm kernel gives the square estimate for a uniformly
bounded weight, by summing over the lattice of rational character values. -/
theorem rationalSquareIntegrableWeight_of_compact_normKernel
    (hG : IsConnectedReductive G)
    (hker : IsCompact (rationalCommonNormKernel G : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    {Ξ : rationalPoints G → ℝ} {A : ℝ} (hΞ : ∀ g, |Ξ g| ≤ A) :
    SquareIntegrableWeight muG Ξ (rationalHeight (F := F) ρ) := by
  classical
  let := (rationalCharacterLattice F G hG).1
  let := (rationalCharacterLattice F G hG).2
  let I := Module.Free.ChooseBasisIndex ℤ (rationalCharacters G)
  let : Fintype I := Fintype.ofFinite I
  let b : Module.Basis I ℤ (rationalCharacters G) := Module.Free.chooseBasis ℤ _
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ I))
  let v : rationalPoints G →* Multiplicative (I → ℤ) :=
    { toFun := fun g => Multiplicative.ofAdd (fun j => valuation (b j) g)
      map_one' := by
        change (fun j => valuation (b j) (1 : rationalPoints G)) = fun _ => (0 : ℤ)
        funext j
        exact valuation_eq_zero_of_mem (rationalCommonNormKernel G).one_mem (b j)
      map_mul' := fun g g' => funext fun j => valuation_mul (b j) g g' }
  have hvker : v.ker = rationalCommonNormKernel G := by
    ext g
    rw [MonoidHom.mem_ker, mem_rationalCommonNormKernel_iff_valuation]
    constructor
    · intro hg χ
      have he : ((rationalCharacterValuation G g).toAdd).toIntLinearMap = 0 := by
        apply b.ext
        intro j
        exact congrArg (fun v : Multiplicative (I → ℤ) => v.toAdd j) hg
      exact LinearMap.congr_fun he χ
    · intro hg
      exact funext fun j => hg (b j)
  let cell (y : v.range) : Set (rationalPoints G) := {g | v g = y.val}
  let H (y : v.range) : L :=
    ⟨fun j => (y.val.toAdd j : ℝ), ((Pi.basisFun ℝ I).mem_span_iff_repr_mem ℤ _).mpr
      fun j => ⟨y.val.toAdd j, by simp⟩⟩
  have hH : Function.Injective H := by
    intro y z hyz
    apply Subtype.ext
    funext j
    have hcast : (y.val.toAdd j : ℝ) = (z.val.toAdd j : ℝ) :=
      congrFun (congrArg Subtype.val hyz) j
    exact_mod_cast hcast
  have hcount : Countable v.range :=
    (show Function.Injective (fun y : v.range => y.val.toAdd) from Subtype.val_injective).countable
  have hcover : ⋃ y, cell y = Set.univ := Set.eq_univ_of_forall fun g =>
    Set.mem_iUnion.mpr ⟨⟨v g, g, rfl⟩, rfl⟩
  have hmass : muG (rationalCommonNormKernel G) < ⊤ := hker.measure_lt_top
  have hcell (y : v.range) : muG (cell y) = muG (rationalCommonNormKernel G) := by
    obtain ⟨a, ha⟩ := y.property
    have he : cell y =
        (fun g => a⁻¹ * g) ⁻¹' (rationalCommonNormKernel G : Set (rationalPoints G)) := by
      ext g
      change v g = y.val ↔ a⁻¹ * g ∈ rationalCommonNormKernel G
      rw [← hvker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, ha, eq_comm]
    rw [he, measure_preimage_mul]
  choose C hC hb using fun j => exists_abs_valuation_le ρ hρ (b j)
  let B := ∑ j, C j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => (hC j).le
  have hnorm (y : v.range) (g : rationalPoints G) (hg : g ∈ cell y) :
      1 + ‖H y‖ ≤ (1 + B) * (1 + rationalHeight ρ g) := by
    have hσ := rationalHeight_nonneg ρ g
    have hbase : ‖H y‖ ≤ B * (1 + rationalHeight ρ g) := by
      change ‖fun j => (y.val.toAdd j : ℝ)‖ ≤ _
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (by linarith))).mpr
      intro j
      rw [← show v g = y.val from hg, Real.norm_eq_abs]
      exact (hb j g).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ j)) (by linarith))
    nlinarith
  refine CartanSquareBound.squareIntegrableWeight (cell := cell) (δ := fun _ => 1)
    (H := H) ⟨hcount, hcover, rationalHeight_nonneg ρ, fun _ => zero_lt_one, ?_,
      ⟨A, 0, fun _ g _ => by simpa only [Real.sqrt_one, mul_one, Real.rpow_zero] using hΞ g⟩,
      ⟨1 + B, by linarith, hnorm⟩, hH⟩
  refine ⟨(muG (rationalCommonNormKernel G)).toNNReal, fun y => ?_⟩
  rw [hcell y, inv_one, ENNReal.ofReal_one, mul_one, ENNReal.coe_toNNReal hmass.ne]

variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The complete actual local VIII.3.1 conclusion in the absence of simple roots. -/
theorem rationalCuspidalConjugationBound_of_simpleRoots_empty
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (h0 : simpleRelativeRoots i ν = ∅) (hρ : IsClosedSubgroup ρ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure] :
    RationalCuspidalConjugationBound hKc hPK ρ muG := by
  obtain ⟨hc, hU⟩ := rankZero_subgroups hG hi hν h0
  have hker := BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit
    centralQuotientReductive anisotropicCompactness_proof G hG hi hc
  have hsquare := rationalSquareIntegrableWeight_of_compact_normKernel hG hker ρ hρ muG
    (Ξ := rationalXi hKc hPK) (A := 1) (fun g => by
      rw [rationalXi_eq_one_of_trivial_radical hKc hPK hU, abs_one])
  refine ⟨rationalCuspidalConjugationConverges_of_squareIntegrableWeight hKc hPK ρ hsquare,
    fun f₁ _ f₂ r => ?_⟩
  have ht := isCompact_rationalMinimalChamberInNormKernel_of_simpleRoots_empty hG hi hν ρ hρ h0
  obtain ⟨B, hB⟩ := (ht.image (continuous_rationalHeight ρ)).bddAbove
  let D := max (1 + B) 1
  have hD : 1 ≤ D := le_max_right _ _
  let M := ‖rationalConjugationPairing hKc hPK ρ muG f₁ f₂ 1‖
  have hM : 0 ≤ M := norm_nonneg _
  have hDpow := Real.rpow_pos_of_pos (zero_lt_one.trans_le hD) |(-r)|
  refine ⟨(M + 1) * D ^ |(-r)|, mul_pos (by linarith) hDpow, fun a => ?_⟩
  obtain ⟨t, ht', _⟩ := (mem_rationalMinimalChamber_iff_order i ν _).mp a.2.1
  have ha : (a : rationalPoints G) ∈ Subgroup.center (rationalPoints G) :=
    ht' ▸ hc.map_mem_center t
  have hpair : rationalConjugationPairing hKc hPK ρ muG f₁ f₂ a =
      rationalConjugationPairing hKc hPK ρ muG f₁ f₂ 1 := by
    simpa only [mul_one] using conjugationPairing_central_mul muG
      (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ) ha 1
  have hσ := rationalHeight_nonneg ρ (a : rationalPoints G)
  have hσB : rationalHeight ρ (a : rationalPoints G) ≤ B :=
    hB ⟨a, a.2, rfl⟩
  have hpow : 1 ≤ D ^ |(-r)| * (1 + rationalHeight ρ a) ^ (-r) := by
    have h1 : 1 + rationalHeight ρ (a : rationalPoints G) ≤ D * 1 := by
      rw [mul_one]
      exact (add_le_add_right hσB 1).trans (le_max_left _ _)
    have h2 : 1 ≤ D * (1 + rationalHeight ρ (a : rationalPoints G)) := by
      nlinarith
    simpa only [Real.one_rpow] using rpow_le_rpow_abs_mul_of_le
      (by linarith : 0 < 1 + rationalHeight ρ (a : rationalPoints G))
      zero_lt_one hD h1 h2 (-r)
  rw [hpair, minimalModulus_eq_one_of_trivial_radical hU, Units.val_one, NNReal.coe_one, mul_one]
  calc M ≤ (M + 1) * 1 := by rw [mul_one]; linarith
    _ ≤ (M + 1) * (D ^ |(-r)| * (1 + rationalHeight ρ a) ^ (-r)) :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = _ := by rw [mul_assoc]

/-- The rank-zero specialization at the original universe and for arbitrary compact
open Iwasawa subgroup, closed matrix realization and group Haar measure. -/
def RationalCuspidalConjugationRankZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν → simpleRelativeRoots i ν = ∅ →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ muG : Measure (rationalPoints G), muG.IsHaarMeasure →
      RationalCuspidalConjugationBound hKc hPK ρ muG

theorem rationalCuspidalConjugationRankZero : RationalCuspidalConjugationRankZeroStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν h0 K hKc hPK N _ ρ hρ muG hmu
  let := hmu
  exact rationalCuspidalConjugationBound_of_simpleRoots_empty hKc hPK ρ hG hi hν h0 hρ muG

end Langlands.HarishChandraSchwartz

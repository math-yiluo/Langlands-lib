import Langlands.Automorphic.GroupSchemeCentralQuotientGrowth
import Langlands.Automorphic.GroupSchemeFixedProfileInteriorEstimate
import Langlands.Automorphic.GroupSchemeSmoothConstantTermSlice
import Langlands.Geometry.Manifold.SmoothGroupLocalOscillation
import Langlands.Global.AdelicNormOneCuspidalFamilyRapidDecay
import Langlands.Global.AdelicEisensteinGrowthBound
import Langlands.Global.AdelicRepresentationHeightExhaustion
import Langlands.Global.AdelicUniformDirectionalGrowth

/-! # Cuspidal finiteness for fixed level, central ideal and compact profiles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints
  Langlands.Geometry.Manifold RepresentationGrowth CompactIwasawa

section FixedGroup

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "A" => AdelicGroupPoints F G
local notation "M" => InfiniteAdelicGroupPoints F G
local notation "V" => FinitePlotSmoothRationalFunctions F G
local notation "Y" => smoothModel F d
local notation "I" => 𝓘(ℝ, Y)
local notation "Z" => AdelicEnvelopingCenter F G hsmooth
local notation "DAlg" => AdelicEnvelopingAlgebra F G hsmooth
local notation "valAt" => (fun f : V => evaluate F G (Subtype.val f))

local instance : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Differentiation by the actual enveloping action preserves the vanishing of all proper
parabolic constant terms. -/
theorem hasCuspidalConstantTerms_enveloping {f : V}
    (hf : ArthurTruncation.HasCuspidalConstantTerms (valAt f)) (D : DAlg) :
    ArthurTruncation.HasCuspidalConstantTerms (valAt (adelicEnvelopingAction F G hsmooth hcalc D f)) := by
  intro P U p j _ _ hp hj hproper
  let S (b : FiniteAdelicGroupPoints F G) := plotSmoothConstantTermSlice (j ≫ p)
    hj.1.smooth hj.1.connectedSpace hj.1.isUnipotent hsmooth b
  have hS (b : FiniteAdelicGroupPoints F G) : S b f = 0 := by
    apply Subtype.ext
    funext a
    change (plotSmoothConstantTermSlice (j ≫ p) hj.1.smooth hj.1.connectedSpace hj.1.isUnipotent hsmooth b f).val a = 0
    rw [plotSmoothConstantTermSlice_apply, hf P U p j hp hj hproper]
    rfl
  funext g
  rw [← pair_projections F G g, ← plotSmoothConstantTermSlice_apply (j ≫ p)
    hj.1.smooth hj.1.connectedSpace hj.1.isUnipotent hsmooth, plotSmoothConstantTermSlice_enveloping]
  change (plotSmoothEnvelopingAction F G hsmooth hcalc D (S (finite F G g) f)).val (infinite F G g) = _
  rw [hS, map_zero]
  rfl

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem derivative_growth_from_value_bound (hG : IsConnectedReductive G) (hN : 0 < N)
    (H : Subgroup M) (hH : IsMaximalCompact H)
    (J : Ideal Z) (hJ : Module.Finite ℂ (Z ⧸ J.restrictScalars ℂ))
    (E : Submodule ℂ (H → ℂ)) (hE : FiniteDimensional ℂ E) (R : ℝ) (hR : 0 ≤ R) (D : DAlg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : V, (∀ z ∈ J, adelicCenterAction F G hsmooth hcalc z f = 0) →
      (∀ b a, rightCompactProfile H a (finitePlotSmoothSlice F G b f).val ∈ E) →
      ∀ s : ℝ, 0 ≤ s → (∀ g, ‖valAt f g‖ ≤ s * adelicHeight F G rho g ^ R) →
      ∀ g, ‖valAt (adelicEnvelopingAction F G hsmooth hcalc D f) g‖ ≤ C * s * adelicHeight F G rho g ^ R := by
  obtain ⟨K, B, hK, hB, hInterior⟩ := fixedProfileInteriorEstimate F G hsmooth hcalc hG H hH J hJ E hE D
  obtain ⟨n, hHeight⟩ := exists_nat_adelicHeight_bound_of_isCompact F G rho hN
    (hK.image (ofInfinite F G).continuous)
  let c := (n : ℝ) ^ R
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨B * c, mul_nonneg hB hc, fun f hf hprof s hs hval g => ?_⟩
  let a := infinite F G g
  let b := finite F G g
  have hPair (k : M) : pair F G (a * k) b = g * ofInfinite F G k := by
    rw [ofInfinite_eq_pair]
    calc
      _ = pair F G a b * pair F G k 1 := by rw [pair_mul, mul_one]
      _ = _ := by rw [show pair F G a b = g from pair_projections F G g]
  have hSlice (z : Z) (hz : z ∈ J) :
      plotSmoothCenterAction F G hsmooth hcalc z (finitePlotSmoothSlice F G b f) = 0 := by
    rw [← finitePlotSmoothSlice_centerAction, show finitePlotSmoothCenterAction F G hsmooth hcalc z f = 0 from hf z hz,
      map_zero]
  have hpos (g : A) : 0 ≤ adelicHeight F G rho g := (one_le_adelicHeight F G rho hN g).trans' zero_le_one
  have hLocal (k : M) (hk : k ∈ K) :
      ‖(finitePlotSmoothSlice F G b f).val (a * k)‖ ≤ (s * c) * adelicHeight F G rho g ^ R := by
    rw [finitePlotSmoothSlice_apply, hPair]
    have hK' : adelicHeight F G rho (ofInfinite F G k) ≤ (n : ℝ) := hHeight ⟨k, hk, rfl⟩
    have hmul : adelicHeight F G rho (g * ofInfinite F G k) ≤ adelicHeight F G rho g * n :=
      (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_left hK' (hpos g))
    refine (hval _).trans ?_
    calc
      _ ≤ s * (adelicHeight F G rho g * n) ^ R :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos _) hmul hR) hs
      _ = _ := by rw [Real.mul_rpow (hpos _) (Nat.cast_nonneg _)]; dsimp [c]; ring
  have hEst := hInterior _ hSlice (hprof b) a _ hLocal
  change ‖(plotSmoothEnvelopingAction F G hsmooth hcalc D (finitePlotSmoothSlice F G b f)).val a‖ ≤ _ at hEst
  rw [← finitePlotSmoothSlice_envelopingAction, finitePlotSmoothSlice_apply, show pair F G a b = g from
    pair_projections F G g] at hEst
  exact hEst.trans_eq (by ring)

end FixedGroup

/-- The fixed-level, fixed-profile and fixed-center-ideal cuspidal space is finite-dimensional.
The hypothesis is stated for any submodule of the original smooth rational carrier. -/
def FixedProfileCuspidalFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
    IsConnectedReductive G →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (H : Subgroup (InfiniteAdelicGroupPoints F G)),
    IsMaximalCompact H → ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (E : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ E →
    letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) := Module.addCommMonoidToAddCommGroup ℂ
    ∀ W : Submodule ℂ (FinitePlotSmoothRationalFunctions F G),
      (∀ f ∈ W, f.val ∈ levelSubmodule F G L.toSubgroup) →
      (∀ f ∈ W, ∀ z ∈ J, adelicCenterAction F G hsmooth hcalc z f = 0) →
      (∀ f ∈ W, ∀ b a, rightCompactProfile H a (finitePlotSmoothSlice F G b f).val ∈ E) →
      (∀ f ∈ W, HasModerateGrowthFunction F G rho (evaluate F G f.val)) →
      (∀ f ∈ W, ArthurTruncation.HasCuspidalConstantTerms (evaluate F G f.val)) → FiniteDimensional ℂ W

set_option maxHeartbeats 1350000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Rapid decay and small oscillation on a compact height sublevel give finitely many
point evaluations of central derivatives that detect the original functions. -/
theorem fixedProfileCuspidalFiniteness : FixedProfileCuspidalFinitenessStatement.{u} := by
  classical
  intro F _ _ G _ _ _ N d rho hN hρ hG hsmooth hcalc L H hH J hJ E hE W hLevel hAnn hProfile hGrow hCusp
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let A := AdelicGroupPoints F G
  let M := InfiniteAdelicGroupPoints F G
  let Y := smoothModel F d
  let I := 𝓘(ℝ, Y)
  let V : Type u := FinitePlotSmoothRationalFunctions F G
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let DAlg := AdelicEnvelopingAlgebra F G hsmooth
  let valAt (f : V) := evaluate F G f.val
  let : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  let height := adelicHeight F G rho
  let act := adelicEnvelopingAction F G hsmooth hcalc
  let center := adelicCenterAction F G hsmooth hcalc
  have h1 (g : A) : 1 ≤ height g := one_le_adelicHeight F G rho hN g
  have h0 (g : A) : 0 ≤ height g := zero_le_one.trans (h1 g)
  obtain ⟨S, _, hRep, hDecay⟩ := adelicNormOneCuspidalFamilyRapidDecay.{u, u} rho hsmooth hG hN
  obtain ⟨m, z, C₀, k, hC₀, hGlobal⟩ := centralQuotientGrowth F G rho hN hsmooth hcalc hG hρ J hJ
  let v (f : W) (j : Fin m) : V := center (z j) f.val
  let φ (f : W) (j : Fin m) : A → ℂ := valAt (v f j)
  have hCont (f : W) (j : Fin m) : Continuous (φ f j) := (v f j).val.property
  have hSmooth (f : W) (j : Fin m) (b : FiniteAdelicGroupPoints F G) :
      ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun a => φ f j (pair F G a b)) :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (finitePlotSmoothSlice F G b (v f j)).property
  have hRat (f : W) (j : Fin m) : IsLeftInvariantUnder F G (rationalSubgroup F G) (φ f j) := by
    rintro _ ⟨q, rfl⟩ g
    exact (v f j).val.val.property q g
  have hFix (f : W) (j : Fin m) (l : FiniteAdelicGroupPoints F G) (hl : l ∈ L.toSubgroup) (g : A) :
      φ f j (g * ofFinite F G l) = φ f j g := by
    have hv : (v f j).val ∈ levelSubmodule F G L.toSubgroup :=
      finitePlotSmoothEnvelopingAction_preserves_level F G hsmooth hcalc (z j).val L.toSubgroup
        f.val (hLevel f.val f.property)
    exact congrArg (fun s : ContinuousRationalFunctions F G => evaluate F G s g) (hv ⟨l, hl⟩)
  have hCT (f : W) (j : Fin m) : ArthurTruncation.HasCuspidalConstantTerms (φ f j) :=
    hasCuspidalConstantTerms_enveloping hsmooth hcalc (hCusp f.val f.property) (z j).val
  have hBound (R : ℝ) (hR : 0 ≤ R) (D : DAlg) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : W, ∀ s : ℝ, 0 ≤ s →
        (∀ g, ‖valAt f.val g‖ ≤ s * height g ^ R) →
        ∀ g, ‖valAt (act D f.val) g‖ ≤ C * s * height g ^ R := by
    obtain ⟨C, hC, h⟩ := derivative_growth_from_value_bound rho hsmooth hcalc hG hN H hH J hJ E hE R hR D
    exact ⟨C, hC, fun f => h f.val (hAnn f.val f.property) (hProfile f.val f.property)⟩
  have hword (R : ℝ) (hR : 0 ≤ R) (w : List Y) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : W, ∀ s : ℝ, 0 ≤ s →
        (∀ g, ‖valAt f.val g‖ ≤ s * height g ^ R) →
        ∀ j g, ‖adelicIteratedDirectionalValue hsmooth w (φ f j) g‖ ≤ C * s * height g ^ R := by
    choose C hC hE using fun j : Fin m => hBound R hR (adelicDirectionalWordEnveloping hsmooth w * (z j).val)
    refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun f s hs hGrowth j g => ?_⟩
    have hb := hE j f s hs hGrowth g
    change ‖valAt (act (_ * _ ) f.val) g‖ ≤ _ at hb
    rw [map_mul, Module.End.mul_apply] at hb
    change ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc
      (adelicDirectionalWordEnveloping hsmooth w) (v f j)).val g‖ ≤ _ at hb
    rw [evaluate_adelicDirectionalWordEnveloping] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)) hs)
      (Real.rpow_nonneg (h0 g) _))
  let Values (f : W) : Set ℝ := insert 0 (Set.range fun p : Fin m × normOneSubgroup F G => ‖φ f p.1 p.2.val‖)
  have hBdd (f : W) : BddAbove (Values f) := by
    obtain ⟨R, hR, hLocal⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height
      (hGrow f.val f.property)
    obtain ⟨s, hs, hf⟩ := hLocal {1} isCompact_singleton
    have hf' (g : A) : ‖valAt f.val g‖ ≤ s * height g ^ R := by
      simpa only [mul_one, adelicHeightAtLeastOne_eq hN] using hf g 1 (Set.mem_singleton 1)
    obtain ⟨B, hB, hb⟩ := hDecay L (ULift.{u} (Fin m)) (fun j => φ f j.down) (fun _ => s)
      (fun _ => hs.le) (fun j => hCont f j.down) (fun j => hSmooth f j.down)
      (fun j => hRat f j.down) (fun j => hFix f j.down) (fun j => hCT f j.down) R hR
      (fun w => by
        obtain ⟨C, hC, hw⟩ := hword R hR w
        exact ⟨C, hC, fun j g => (hw f s hs.le hf' j.down g).trans_eq (by ring)⟩) 0
    refine ⟨B * s, ?_⟩
    rintro a (ha | ⟨⟨j, n⟩, rfl⟩)
    · rw [ha]
      exact mul_nonneg hB hs.le
    obtain ⟨q, hq⟩ := hRep n
    have hq' := hb ⟨j⟩ _ hq
    rw [pow_zero, mul_one, hRat f j _ ⟨q, rfl⟩] at hq'
    exact hq'
  let size (f : W) : ℝ := sSup (Values f)
  have hsize (f : W) : 0 ≤ size f := le_csSup (hBdd f) (Set.mem_insert _ _)
  have hvals (f : W) (j : Fin m) (n : normOneSubgroup F G) : ‖φ f j n.val‖ ≤ size f :=
    le_csSup (hBdd f) (Set.mem_insert_of_mem _ (Set.mem_range_self (j, n)))
  let amplitude (f : W) := C₀ * size f
  have hAmp (f : W) : 0 ≤ amplitude f := mul_nonneg hC₀.le (hsize f)
  have hVal (f : W) (g : A) : ‖valAt f.val g‖ ≤ amplitude f * height g ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
    exact (hGlobal f.val (hAnn f.val f.property) _ (hsize f) (hvals f) g).trans_eq (by
      dsimp [amplitude]; ring)
  obtain ⟨B, hB, hTail⟩ := hDecay L (W × Fin m) (fun a => φ a.1 a.2) (fun a => size a.1)
    (fun a => hsize a.1) (fun a => hCont a.1 a.2) (fun a => hSmooth a.1 a.2)
    (fun a => hRat a.1 a.2) (fun a => hFix a.1 a.2) (fun a => hCT a.1 a.2) (k : ℝ) (Nat.cast_nonneg _)
    (fun w => by
      obtain ⟨C, hC, hw⟩ := hword (k : ℝ) (Nat.cast_nonneg _) w
      refine ⟨C * C₀, mul_nonneg hC hC₀.le, fun q x => ?_⟩
      exact (hw q.1 _ (hAmp q.1) (hVal q.1) q.2 x).trans_eq (by dsimp [amplitude]; ring)) 1
  let Core := adelicHeightSublevel F G rho (2 * B + 1)
  have hCore : IsCompact Core := isCompact_adelicHeightSublevel F G rho hN hρ _
  have hSmall (f : W) (j : Fin m) (g : A) (hg : g ∈ S) (hg' : g ∉ Core) : ‖φ f j g‖ ≤ size f / 2 := by
    have h := hTail (f, j) g hg
    simp only [pow_one] at h
    have hBG : 2 * B ≤ height g := by
      have hh : ¬ height g ≤ 2 * B + 1 := hg'
      linarith [lt_of_not_ge hh]
    have hp : 0 < height g := zero_lt_one.trans_le (h1 g)
    apply (le_of_mul_le_mul_right _ hp)
    calc
      ‖φ f j g‖ * height g ≤ B * size f := h
      _ = (size f / 2) * (2 * B) := by ring
      _ ≤ (size f / 2) * height g := mul_le_mul_of_nonneg_left hBG (div_nonneg (hsize f) (by norm_num))
  obtain ⟨K, n, X, hK, hOsc⟩ := smoothGroupLocalOscillation Y M
  obtain ⟨D₀, hD₀⟩ := exists_nat_adelicHeight_bound_of_isCompact F G rho hN
    (hCore.mul (hK.image (ofInfinite F G).continuous))
  let gen (i : Fin n) : DAlg := UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (X i))
  choose D hD hDeriv using fun (j : Fin m) (i : Fin n) =>
    hBound (k : ℝ) (Nat.cast_nonneg _) (gen i * (z j).val)
  let dsum := ∑ j, ∑ i, D j i
  have hdsum : 0 ≤ dsum := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hD j i
  let dBound := dsum * C₀ * (D₀ : ℝ) ^ k
  have hdBound : 0 ≤ dBound := mul_nonneg (mul_nonneg hdsum hC₀.le) (pow_nonneg (Nat.cast_nonneg _) _)
  obtain ⟨U, hU, hU1, hosc⟩ := hOsc dBound (1 / 2) hdBound (by norm_num)
  have hNear (f : W) (j : Fin m) (g : A) (hg : g ∈ Core) (y : M) (hy : y ∈ U) :
      ‖φ f j (g * ofInfinite F G y) - φ f j g‖ ≤ size f / 2 := by
    let a := infinite F G g
    let b := finite F G g
    let f₀ (x : M) := φ f j (pair F G (a * x) b)
    have hf₀ : ContMDiff I 𝓘(ℝ, ℂ) ∞ f₀ := (hSmooth f j b).comp (contMDiff_const.mul contMDiff_id)
    have hPair (x : M) : pair F G (a * x) b = g * ofInfinite F G x := by
      rw [ofInfinite_eq_pair]
      calc
        _ = pair F G a b * pair F G x 1 := by rw [pair_mul, mul_one]
        _ = _ := by rw [show pair F G a b = g from pair_projections F G g]
    have hDir (x : M) (hx : x ∈ K) (i : Fin n) :
        ‖groupDirectionalValue I (X i) f₀ x‖ ≤ dBound * size f := by
      have hb := hDeriv j i f _ (hAmp f) (hVal f) (g * ofInfinite F G x)
      rw [Real.rpow_natCast] at hb
      change ‖valAt (act (gen i * (z j).val) f.val) (g * ofInfinite F G x)‖ ≤ _ at hb
      rw [map_mul, Module.End.mul_apply, ← hPair] at hb
      change ‖evaluate F G (finitePlotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (X i))) (v f j)).val
        (pair F G (a * x) b)‖ ≤ _ at hb
      rw [finitePlotSmoothEnvelopingAction_real_generator, evaluate_finitePlotSmoothDifferentialAction] at hb
      change ‖groupDirectionalValue I (X i) (fun u => φ f j (pair F G u b)) (a * x)‖ ≤ _ at hb
      have hleft : groupDirectionalValue I (X i) f₀ x =
          groupDirectionalValue I (X i) (fun u => φ f j (pair F G u b)) (a * x) :=
        groupDirectionalValue_leftTranslation I (X i) a (fun u => φ f j (pair F G u b)) x
      rw [hleft]
      have hh : height (g * ofInfinite F G x) ≤ (D₀ : ℝ) := hD₀ ⟨g, hg, _, ⟨x, hx, rfl⟩, rfl⟩
      have hDsum : D j i ≤ dsum :=
        (Finset.single_le_sum (fun i _ => hD j i) (Finset.mem_univ i)).trans
          (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => hD j i) (Finset.mem_univ j))
      rw [hPair] at hb
      refine hb.trans ?_
      calc
        _ ≤ dsum * amplitude f * (D₀ : ℝ) ^ k :=
          mul_le_mul (mul_le_mul_of_nonneg_right hDsum (hAmp f))
            (pow_le_pow_left₀ (h0 _) hh _) (pow_nonneg (h0 _) _) (mul_nonneg hdsum (hAmp f))
        _ = _ := by dsimp [dBound, amplitude]; ring
    have h := hosc f₀ hf₀ _ (hsize f) hDir y hy
    change ‖φ f j (pair F G (a * y) b) - φ f j (pair F G (a * 1) b)‖ ≤ _ at h
    rw [hPair, mul_one, show pair F G a b = g from pair_projections F G g] at h
    exact h.trans_eq (by ring)
  let Neighborhood (g : Core) : Set A :=
    (fun x => infinite F G (g.val⁻¹ * x)) ⁻¹' U ∩
      (fun x => finite F G (g.val⁻¹ * x)) ⁻¹' (L : Set (FiniteAdelicGroupPoints F G))
  have hNeighborhood (g : Core) : IsOpen (Neighborhood g) :=
    (hU.preimage ((infinite F G).continuous.comp (continuous_const.mul continuous_id))).inter
      (L.isOpen.preimage ((finite F G).continuous.comp (continuous_const.mul continuous_id)))
  have hCover : Core ⊆ ⋃ g : Core, Neighborhood g := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    change infinite F G (x⁻¹ * x) ∈ U ∧ finite F G (x⁻¹ * x) ∈ L.toSubgroup
    rw [inv_mul_cancel, map_one, map_one]
    exact ⟨hU1, L.toSubgroup.one_mem⟩
  obtain ⟨T, hT⟩ := hCore.elim_finite_subcover Neighborhood hNeighborhood hCover
  let sample : W →ₗ[ℂ] ((↥T × Fin m) → ℂ) :=
    { toFun := fun f q => φ f q.2 q.1.val.val
      map_add' f g := by funext q; exact congrArg (fun v : V => valAt v q.1.val.val) (map_add (center (z q.2)) f.val g.val)
      map_smul' a f := by funext q; exact congrArg (fun v : V => valAt v q.1.val.val) (map_smul (center (z q.2)) a f.val) }
  apply Module.Finite.of_injective sample
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hZero (g : Core) (hg : g ∈ T) (j : Fin m) : φ f j g.val = 0 :=
    congrFun (LinearMap.mem_ker.mp hf) (⟨g, hg⟩, j)
  have hSmallCore (g : A) (hg : g ∈ Core) (j : Fin m) : ‖φ f j g‖ ≤ size f / 2 := by
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hT hg)
    obtain ⟨hxT, hxN⟩ := Set.mem_iUnion.mp hx
    let y := infinite F G (x.val⁻¹ * g)
    let l := finite F G (x.val⁻¹ * g)
    have hy : y ∈ U := hxN.1
    have hl : l ∈ L.toSubgroup := hxN.2
    have hg' : g = (x.val * ofInfinite F G y) * ofFinite F G l := by
      calc
        _ = x.val * (x.val⁻¹ * g) := by rw [mul_inv_cancel_left]
        _ = x.val * pair F G y l := by rw [show pair F G y l = x.val⁻¹ * g from pair_projections F G _]
        _ = _ := by rw [mul_assoc, ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
    have h := hNear f j x.val x.property y hy
    rw [hZero x hxT, sub_zero] at h
    rw [hg', hFix f j l hl]
    exact h
  have hHalf : size f ≤ size f / 2 := by
    apply csSup_le ⟨0, Set.mem_insert _ _⟩
    rintro a (ha | ⟨⟨j, n⟩, rfl⟩)
    · rw [ha]
      exact div_nonneg (hsize f) (by norm_num)
    obtain ⟨q, hq⟩ := hRep n
    change ‖φ f j n.val‖ ≤ size f / 2
    let g := rational F G q * n.val
    rw [← hRat f j _ ⟨q, rfl⟩ n.val]
    by_cases hg : g ∈ Core
    · exact hSmallCore g hg j
    · exact hSmall f j g hq hg
  have hsf : size f = 0 := by linarith [hsize f]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h := hVal f g
  simp only [amplitude, hsf, mul_zero, zero_mul, norm_le_zero_iff] at h
  exact h

end Langlands.Automorphic.GroupSchemeFunctions

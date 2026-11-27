import Langlands.TraceFormula.GlobalizationLocalCoefficient
import Langlands.TraceFormula.GlobalizationTensor
import Langlands.TraceFormula.GlobalizationAuxiliarySupport
import Langlands.TraceFormula.GlobalizationQuotientConvolution
import Langlands.TraceFormula.PositiveAverageOrbitSupport
import Langlands.TraceFormula.GeneralLinearCuspFormLocalVanishingProof
import Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingProof
import Langlands.TraceFormula.GroupSchemeCuspidalImageProof
import Mathlib.Topology.UrysohnsLemma

/-! # A common cuspidal vector for prescribed local supercuspidals -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration

namespace Langlands.TraceFormula

open GlobalizationTensor

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

set_option hygiene false in
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)
set_option hygiene false in
local notation "A" => AdelicGroupPoints K GLG
set_option hygiene false in
local notation "N" => normOneSubgroup K GLG
set_option hygiene false in
local notation "ι" => matrixPlaceInclusion K n

local instance : IsAffine (GLG).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance : Smooth (GLG).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLG)
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLG)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i) [(Measure.haar : Measure N).IsMulRightInvariant]

set_option hygiene false in
local notation "S" => fullAEL2CuspidalSubmodule K GLG hPD hG T i hi I e hc
set_option hygiene false in
local notation "πc" => fullAEL2CuspidalBoundedRightAction K GLG hPD hG T i hi I e hc
set_option hygiene false in
local notation "ν" => positiveRationalQuotientHaarMeasure K GLG T i
set_option hygiene false in
local notation "πA" => haarQuotientL2BoundedRightAction K GLG T i hi I e hc

omit [(Measure.haar : Measure N).IsMulRightInvariant] in
private theorem exists_archimedeanBump :
    ∃ b : C_c(InfiniteAdelicGL K n, ℝ), (∀ a, 0 ≤ b a) ∧ b 1 ≠ 0 := by
  let E := GeneralLinearGroupPoints.infiniteHomeomorph K n
  let : IsTopologicalGroup (InfiniteAdelicGL K n) :=
    Topology.IsInducing.isTopologicalGroup E.symm E.symm.toHomeomorph.isInducing
  let : RegularSpace (InfiniteAdelicGL K n) := IsTopologicalGroup.regularSpace _
  let : LocallyCompactSpace (InfiniteAdelicGL K n) :=
    E.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨b, hbc, hb, hb₁⟩ := exists_continuous_nonneg_pos (1 : InfiniteAdelicGL K n)
  exact ⟨⟨b, hbc⟩, hb, hb₁⟩

omit [(Measure.haar : Measure N).IsMulRightInvariant] in
private theorem exists_finiteCutoff (v : Langlands.Global.FinitePlace K)
    [LocallyCompactSpace (FiniteLocalGL K n v)]
    (U : Set (PlaceGroupPoints K GLG (.inr v))) (hU : IsOpen U) (hU₁ : 1 ∈ U) :
    ∃ b : C(FiniteLocalGL K n v, ℂ), b 1 = 1 ∧
      ∀ k, b k ≠ 0 →
        (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
          (placeCompletion K (.inr v))).symm k ∈ U := by
  let E : PlaceGroupPoints K GLG (.inr v) ≃ₜ* FiniteLocalGL K n v :=
    GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
      (placeCompletion K (.inr v))
  let : T2Space (FiniteLocalGL K n v) := E.symm.toHomeomorph.isEmbedding.t2Space
  let : IsTopologicalGroup (FiniteLocalGL K n v) := (CompletionPadic.topologicalData v).generalLinearTopologicalGroup n
  have h₁ : ({1} : Set (FiniteLocalGL K n v)) ⊆ E.symm ⁻¹' U := by
    intro k hk
    obtain rfl := Set.mem_singleton_iff.mp hk
    exact show E.symm 1 ∈ U from by simpa only [map_one] using hU₁
  obtain ⟨ψ, hψ₁, _, hψU, _⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    isCompact_singleton (hU.preimage E.symm.continuous) h₁
  let b : C(FiniteLocalGL K n v, ℂ) := ⟨fun k => ψ k, Complex.continuous_ofReal.comp ψ.continuous⟩
  refine ⟨b, ?_, fun k hk => hψU (subset_tsupport ψ ?_)⟩
  · change (ψ 1 : ℂ) = 1
    rw [show ψ 1 = 1 from hψ₁ (Set.mem_singleton 1), Complex.ofReal_one]
  · intro h
    exact hk (show (ψ k : ℂ) = 0 from by rw [h, Complex.ofReal_zero])

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6500000 in
/-- The coefficient tests produce one nonzero cuspidal vector that belongs to the range of
an intertwiner at each prescribed place and is fixed by all the required integral subgroups. -/
theorem exists_supercuspidalCommonVector (hn : 0 < n)
    [∀ v : Langlands.Global.FinitePlace K, LocallyCompactSpace (FiniteLocalGL K n v)]
    [∀ v : Langlands.Global.FinitePlace K, TotallyDisconnectedSpace (FiniteLocalGL K n v)]
    (Sc : Finset (Langlands.Global.FinitePlace K)) (hSc : Sc.Nonempty)
    (vaux : Langlands.Global.FinitePlace K) (hvaux : vaux ∉ Sc)
    (V : Langlands.Global.FinitePlace K → Type w) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (ρ : ∀ v : Langlands.Global.FinitePlace K, Representation ℂ (FiniteLocalGL K n v) (V v))
    (hρ : ∀ v ∈ Sc, (ρ v).IsIrreducible ∧ GeneralLinear.IsSupercuspidal (ρ v)) :
    ∃ x : S, x ≠ 0 ∧
      (∀ v : Langlands.Global.FinitePlace K, v ∉ Sc → v ≠ vaux →
        ∀ k ∈ FiniteAdelicGL.localIntegral K n v, πc (ι v k) x = x) ∧
      ∀ v ∈ Sc, ∃ j : V v →ₗ[ℂ] S, (∃ y, j y = x) ∧
        ∀ k, Valued.v (GeneralLinear.determinant k : v.adicCompletion K) = 1 →
          ∀ y, j (ρ v k y) = πc (ι v k) (j y) := by
  classical
  let E := GeneralLinearGroupPoints.adelicHomeomorph K n
  let Ev := GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
    (placeCompletion K (.inr vaux))
  let μA := normalizedPositiveHaarMeasure K GLG T i hi I e hc
  let hsplit : IsSplitTorus T.toGrp := ⟨I, inferInstance, ⟨e⟩⟩
  choose z ℓ hℓ hℓz using fun v : Sc => exists_normalized_smoothCoefficient v.val (ρ v)
    (hρ v v.property).1 (hρ v v.property).2
  let c (v : Sc) := globalizationLocalCoefficient v.val hn (ρ v) (hρ v v.property).2 (ℓ v) (hℓ v)
  let l (y : ∀ v : Sc, V v) (v : Sc) := c v (y v)
  have hc₁ (v : Sc) : c v (z v) 1 = 1 := by
    dsimp only [c]
    rw [globalizationLocalCoefficient_apply _ _ _ _ _ _ _ _ (map_one _), inv_one, map_one]
    exact hℓz v
  obtain ⟨b₀, hb₀, hb₁⟩ := exists_archimedeanBump K n
  let b : C_c(InfiniteAdelicGL K n, ℂ) :=
    ⟨⟨fun a => b₀ a, Complex.continuous_ofReal.comp b₀.continuous⟩,
      b₀.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  let f₀ := (test K n Sc b (l z)).comp E.toHomeomorph.toCocompactMap
  obtain ⟨C, hC, _, hCavg⟩ := positiveAverageOrbitSupport K GLG T i hi I e
    (tsupport f₀) f₀.hasCompactSupport
  obtain ⟨U, hU, hU₁, hcut⟩ := exists_auxiliaryPeriodizationCutoff K n vaux hC
  obtain ⟨baux, hbaux₁, hbaux⟩ := exists_finiteCutoff K n vaux U hU hU₁
  let a (g : AdelicGL K n) := baux (finiteComponent K n vaux g)
  let F (y : ∀ v : Sc, V v) : C_c(AdelicGL K n, ℂ) :=
    ⟨⟨fun g => test K n Sc b (l y) g * a g,
      (test K n Sc b (l y)).continuous.mul (baux.continuous.comp (finiteComponent K n vaux).continuous)⟩,
      (test K n Sc b (l y)).hasCompactSupport.mul_right⟩
  let f (y : ∀ v : Sc, V v) : C_c(A, ℂ) := (F y).comp E.toHomeomorph.toCocompactMap
  have hF (y : ∀ v : Sc, V v) (v : Sc) (g : AdelicGL K n) :
      F y g = (complement K n Sc b (l y) v g * a g) * c v (y v) (finiteComponent K n v g) := by
    change test K n Sc b (l y) g * a g = _
    rw [test_eq_complement_mul K n Sc b (l y) v g]
    dsimp only [l]
    ring
  have ha (v : Langlands.Global.FinitePlace K) (hv : vaux ≠ v) (k : FiniteLocalGL K n v)
      (x y : AdelicGL K n) : a (x * includeFinite K n v k * y) = a (x * y) := by
    simp only [a, map_mul, finiteComponent_includeFinite_of_ne K n hv, mul_one]
  have hsupport : Function.support (f z : A → ℂ) ⊆ tsupport f₀ := by
    intro g hg
    apply subset_tsupport f₀
    intro hz
    change test K n Sc b (l z) (E g) = 0 at hz
    exact hg (show test K n Sc b (l z) (E g) * a (E g) = 0 from by rw [hz, zero_mul])
  let fOne := globalizationNormOneAverage K GLG T i hi I e hc (f z)
  have havg (g : N) (hg : fOne g ≠ 0) :
      g ∈ C ∧ atPlace K GLG (.inr vaux) g.val ∈ U := by
    obtain ⟨hgC, x, hx, hcoord⟩ := (hCavg μA (f z) hsupport).1 g hg
    refine ⟨hgC, ?_⟩
    rw [← hcoord vaux]
    have hx' : baux (finiteComponent K n vaux (E x)) ≠ 0 := by
      intro hzero
      exact hx (show test K n Sc b (l z) (E x) * a (E x) = 0 from by
        simp only [a, hzero, mul_zero])
    have hU' := hbaux _ hx'
    rw [finiteComponent_adelicHomeomorph] at hU'
    change Ev.symm (Ev (atPlace K GLG (.inr vaux) x)) ∈ U at hU'
    rwa [Ev.symm_apply_apply] at hU'
  have hfinite (p : intrinsicSubgroup K T) (v : Langlands.Global.FinitePlace K) :
      finiteComponent K n v (E (positivePointMap K GLG T i p)) = 1 := by
    have hp := atPlace_positivePointMap_mul K GLG T i hsplit v p (1 : A)
    simp only [mul_one, map_one] at hp
    rw [finiteComponent_adelicHomeomorph, hp, map_one]
  have hpositive (p : intrinsicSubgroup K T) :
      f z (positivePointMap K GLG T i p) =
        (b₀ (AdelicGL.infinite K n (E (positivePointMap K GLG T i p))) : ℂ) := by
    let g := E (positivePointMap K GLG T i p)
    have haway : awayComponent K n Sc g = 1 := by
      apply RestrictedProduct.ext
      intro v
      exact hfinite p v.val
    change test K n Sc b (l z) g * a g = _
    rw [test_apply, haway, awayCharacteristic_of_mem K n Sc (Subgroup.one_mem _)]
    simp only [a, g, hfinite, hbaux₁, l, hc₁, Finset.prod_const_one, mul_one]
    rfl
  have hone : fOne 1 ≠ 0 := by
    apply globalizationNormOneAverage_one_ne_zero
    · intro p
      rw [hpositive, Complex.ofReal_re]
      exact hb₀ _
    · have h := hpositive (1 : intrinsicSubgroup K T)
      simp only [map_one] at h
      rw [h, Complex.ofReal_re]
      exact hb₁
  have hvperiod : quotientAverage (rationalNormOneSubgroup K GLG) Measure.count fOne
      (LeftCosetSpace.mk (rationalNormOneSubgroup K GLG) 1) ≠ 0 :=
    (hcut _ havg).trans_ne hone
  obtain ⟨φ, hφ⟩ := exists_positiveQuotientCompactConvolution_ne_zero K GLG T i hi I e hc (f z) hvperiod
  let W := positiveQuotientCompactConvolution K GLG T i hi I e hc φ
  obtain ⟨v₀, hv₀⟩ := hSc
  let v₁ : Sc := ⟨v₀, hv₀⟩
  have hcuspidal (y : ∀ v : Sc, V v) : W (f y) ∈ S := by
    apply groupSchemeCuspidalImage K GLG hPD hG T i hi I e hc (f y)
      ((f y).continuous.integrable_of_hasCompactSupport (f y).hasCompactSupport) _ φ
    apply generalLinearRadicalIntegralVanishing K n hPD hG v₀ (F y) (F y).continuous (F y).hasCompactSupport
    apply generalLinearCuspFormLocalVanishing K n v₀ (F y)
    intro x b'
    have hx (k : FiniteLocalGL K n v₀) :
        F y (x * includeFinite K n v₀ k * b') =
          (complement K n Sc b (l y) v₁ (x * b') * a (x * b')) *
            c v₁ (y v₁) (finiteComponent K n v₀ x * (k * finiteComponent K n v₀ b')) := by
      rw [hF y v₁, complement_insert, ha v₀ (fun h => hvaux (h.symm ▸ hv₀))]
      simp only [v₁, map_mul, finiteComponent_includeFinite, mul_assoc]
    change BaseChange.HasVanishingConstantTerms (fun k => F y (x * includeFinite K n v₀ k * b'))
    simp_rw [hx]
    exact (((globalizationLocalCoefficient_vanishing v₀ hn (ρ v₀) (hρ v₀ hv₀).2
      (ℓ v₁) (hℓ v₁) (y v₁)).comp_mul_left (finiteComponent K n v₀ x)).comp_mul_right
        (finiteComponent K n v₀ b')).const_mul _
  have hleft (v : Langlands.Global.FinitePlace K) (k : FiniteLocalGL K n v) (g : A) :
      E ((ι v k)⁻¹ * g) = includeFinite K n v k⁻¹ * E g := by
    rw [map_mul, ← map_inv (ι v)]
    exact congrArg (· * E g) (adelicHomeomorph_matrixPlaceInclusion K n v k⁻¹)
  let x : S := ⟨W (f z), hcuspidal z⟩
  refine ⟨x, fun he => hφ (congrArg Subtype.val he), ?_, ?_⟩
  · intro v hv hv' k hk
    apply Subtype.ext
    change πA (ι v k) (W (f z)) = W (f z)
    symm
    apply positiveQuotientCompactConvolution_leftTranslate K GLG T i hi I e hc φ
    intro g
    change F z (E g) = F z (E ((ι v k)⁻¹ * g))
    rw [hleft]
    change (test K n Sc b (l z) (E g)) * a (E g) =
      test K n Sc b (l z) (includeFinite K n v k⁻¹ * E g) *
        a (includeFinite K n v k⁻¹ * E g)
    rw [test_awayIntegral_mul K n Sc b (l z) v hv k⁻¹ ((FiniteAdelicGL.localIntegral K n v).inv_mem hk)]
    congr 1
    simpa only [one_mul] using (ha v hv'.symm k⁻¹ 1 (E g)).symm
  · intro v hv
    let t : Sc := ⟨v, hv⟩
    have hcomplement (y : V v) (g : AdelicGL K n) :
        complement K n Sc b (l (Function.update z t y)) t g = complement K n Sc b (l z) t g := by
      unfold complement
      congr 1
      congr 1
      apply Finset.prod_congr rfl
      intro w hw
      change c w (Function.update z t y w) (finiteComponent K n w g) =
        c w (z w) (finiteComponent K n w g)
      rw [Function.update_of_ne (Finset.mem_erase.mp hw).1]
    have hreplace (y : V v) (g : AdelicGL K n) :
        F (Function.update z t y) g = (complement K n Sc b (l z) t g * a g) *
          c t y (finiteComponent K n v g) := by
      rw [hF, hcomplement, Function.update_self]
    let L : V v →ₗ[ℂ] C_c(A, ℂ) :=
      { toFun y := f (Function.update z t y)
        map_add' y₁ y₂ := by
          ext g
          change F (Function.update z t (y₁ + y₂)) (E g) =
            F (Function.update z t y₁) (E g) + F (Function.update z t y₂) (E g)
          simp only [hreplace, map_add, Submodule.coe_add, Pi.add_apply, mul_add]
        map_smul' r y := by
          ext g
          change F (Function.update z t (r • y)) (E g) = r • F (Function.update z t y) (E g)
          simp only [hreplace, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          ring }
    let j := (W.comp L).codRestrict S (fun y => hcuspidal (Function.update z t y))
    refine ⟨j, ⟨z t, ?_⟩, ?_⟩
    · apply Subtype.ext
      change W (f (Function.update z t (z t))) = W (f z)
      rw [Function.update_eq_self]
    · intro k hk y
      apply Subtype.ext
      change W (L (ρ v k y)) = πA (ι v k) (W (L y))
      apply positiveQuotientCompactConvolution_leftTranslate K GLG T i hi I e hc φ
      intro g
      change F (Function.update z t (ρ v k y)) (E g) =
        F (Function.update z t y) (E ((ι v k)⁻¹ * g))
      simp only [hleft, hreplace]
      have hcompl := complement_insert K n Sc b (l z) t k⁻¹ 1 (E g)
      simp only [one_mul] at hcompl
      rw [hcompl, show a (includeFinite K n v k⁻¹ * E g) = a (E g) from
        by simpa only [one_mul] using ha v (fun h => hvaux (h.symm ▸ hv)) k⁻¹ 1 (E g),
        map_mul, finiteComponent_includeFinite]
      rw [globalizationLocalCoefficient_translate _ _ _ _ _ _ y k _
        ((completion_determinantNorm_eq_one_iff v k).mpr hk)]

end Langlands.TraceFormula

import Langlands.Global.AdelicArchimedeanCharacterLog
import Langlands.Global.AdelicEisensteinDifferentialParameters

/-! # Smooth height pairings from local archimedean Iwasawa factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter TensorProduct
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

open Langlands.GroupScheme InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "I" => 𝓘(ℝ, smoothModel F d)
local notation "Inf" => InfiniteAdelicGroupPoints F G
local notation "InfP" => InfiniteAdelicGroupPoints F P
local notation "Ar" => CommAlgCat.of F (InfiniteAdeleRing F)

omit [IsClosedImmersion p.hom.hom.left] in
variable (p K) in
/-- Locally smooth infinite Iwasawa factors. Smoothness is in the ambient
infinite group, and only the parabolic component needs to be smooth. -/
def HasSmoothLocalIwasawaFactors : Prop :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  ∀ a : Inf, ∃ (q : Inf → InfP) (k : Inf → Inf),
    ContMDiffAt I I ∞ (fun x => P.affinePointsTarget p Ar (q x)) a ∧
      ∀ᶠ x in 𝓝 a, ofInfinite F G (k x) ∈ K ∧
        map F P G p (ofInfinite F P (q x)) * ofInfinite F G (k x) = ofInfinite F G x

private theorem height_pair_of_infinite_factor {x k : Inf} {q : InfP}
    (hk : ofInfinite F G k ∈ K)
    (hx : map F P G p (ofInfinite F P q) * ofInfinite F G k = ofInfinite F G x)
    (b : FiniteAdelicGroupPoints F G) :
    hK.height (pair F G x b) = characterLog F P (ofInfinite F P q) + hK.height (ofFinite F G b) := by
  have hpair : pair F G x b = ofInfinite F G x * ofFinite F G b := by
    rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
  rw [hpair, ← hx, mul_assoc, (factors_commute F G k b).eq,
    hK.height_map_mul, hK.height_mul_right _ hk]

/-- Lifting each rational-character coordinate to the ambient group, then
applying the local factorization, makes the true height pairing smooth. -/
theorem hasSmoothHeightPairings_of_localIwasawa (hloc : HasSmoothLocalIwasawaFactors p K hsmooth) :
    hK.HasSmoothHeightPairings hsmooth := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have hreal (χ : rationalCharacters P) (b : FiniteAdelicGroupPoints F G) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => hK.height (pair F G x b) χ) := by
    intro a
    obtain ⟨q, k, hq, hfac⟩ := hloc a
    obtain ⟨s, hs⟩ := exists_archimedeanLogRegular_characterExtension F p hsmooth χ
    let f (x : Inf) := archimedeanLogRegular F G s (P.affinePointsTarget p Ar (q x))
    have hsmoothLog : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (archimedeanLogRegular F G s)
        (P.affinePointsTarget p Ar (q a)) := (hs (q a)).2
    have hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f a := by
      change ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        ((archimedeanLogRegular F G s) ∘ (fun x => P.affinePointsTarget p Ar (q x))) a
      exact hsmoothLog.comp a hq
    refine (hf.add (contMDiffAt_const (c := hK.height (ofFinite F G b) χ))).congr_of_eventuallyEq ?_
    filter_upwards [hfac] with x hx
    change hK.height (pair F G x b) χ =
      archimedeanLogRegular F G s (P.affinePointsTarget p Ar (q x)) + hK.height (ofFinite F G b) χ
    rw [hK.height_pair_of_infinite_factor hx.1 hx.2, (hs (q x)).1]
    rfl
  change ∀ (lam : ComplexCharacterParameter F P) (b : FiniteAdelicGroupPoints F G),
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x => complexParameterPairing F P lam (hK.height (pair F G x b)))
  intro lam b
  refine TensorProduct.inductionOn (motive := fun t : ComplexCharacterParameter F P =>
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x => complexParameterPairing F P t (hK.height (pair F G x b)))) lam ?_ ?_
  · intro z χ
    simp only [complexParameterPairing_tmul]
    have hz : ContDiff ℝ ∞ (fun y : ℝ => z * (y : ℂ)) := contDiff_const.mul Complex.ofRealCLM.contDiff
    exact hz.contMDiff.comp (hreal χ b)
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply]
    exact (contDiff_add (𝕜 := ℝ) (F := ℂ)).contMDiff.comp (hx.prodMk_space hy)

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Geometry.Manifold.SmoothGroupConjugation

/-! # Transformation and smoothness of height differentials -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hH : hK.HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)

local notation "I" => 𝓘(ℝ, smoothModel F d)
local notation "Inf" => InfiniteAdelicGroupPoints F G
local notation "FinPts" => FiniteAdelicGroupPoints F G
local notation "Adeles" => AdelicGroupPoints F G
local notation "directional" => hK.heightPairingDirectional hsmooth hH

private def pairHeight (b : FinPts) (a : Inf) : ℂ :=
  complexParameterPairing F P lam (hK.height (pair F G a b))

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- At a fixed parameter the height differential is real-linear in the invariant direction. -/
def heightDifferentialInDirection :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    smoothModel F d →ₗ[ℝ] (Adeles → ℂ) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  exact
    { toFun := fun X => directional X lam
      map_add' := fun X Y => funext fun g =>
        groupDirectionalValue_add_direction I X Y (pairHeight hK lam (finite F G g)) (infinite F G g)
      map_smul' := fun c X => funext fun g =>
        groupDirectionalValue_smul_direction I c X (pairHeight hK lam (finite F G g)) (infinite F G g) }

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Every fixed finite slice of the height differential is smooth. -/
theorem contMDiff_heightDifferential_pair (X : smoothModel F d) (b : FinPts) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun a => directional X lam (pair F G a b)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  change ContMDiff I 𝓘(ℝ, ℂ) ∞
    (fun a => groupDirectionalValue I X (pairHeight hK lam (finite F G (pair F G a b)))
      (infinite F G (pair F G a b)))
  simp only [finite_pair, infinite_pair]
  exact contMDiff_groupDirectionalValue I X (hH lam b)

/-- The height differential is left parabolic invariant, because left
translation adds a scalar constant to each height pairing. -/
theorem heightDifferential_map_mul (X : smoothModel F d) (q : AdelicGroupPoints F P) (g : Adeles) :
    directional X lam (map F P G p q * g) = directional X lam g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let y := map F P G p q
  let u := infinite F G y
  let v := finite F G y
  let a := infinite F G g
  let b := finite F G g
  let c : ℂ := complexParameterPairing F P lam (characterLog F P q)
  have he : (fun x => pairHeight hK lam (v * b) (u * x)) = (fun _ => c) + pairHeight hK lam b := by
    funext x
    have hp : pair F G (u * x) (v * b) = y * pair F G x b := by
      conv_rhs => rw [← pair_projections F G y]
      rw [pair_mul]
    simp only [pairHeight, hp, y, hK.height_map_mul, map_add, Pi.add_apply, c]
  change groupDirectionalValue I X (pairHeight hK lam (finite F G (y * g))) (infinite F G (y * g)) =
    groupDirectionalValue I X (pairHeight hK lam b) a
  rw [map_mul, map_mul]
  change groupDirectionalValue I X (pairHeight hK lam (v * b)) (u * a) = _
  have hb : ContMDiff I 𝓘(ℝ, ℂ) ∞ (pairHeight hK lam b) := hH lam b
  rw [← groupDirectionalValue_leftTranslation I X u (pairHeight hK lam (v * b)) a, he,
    groupDirectionalValue_add I X contMDiff_const hb]
  simp [groupDirectionalValue, mvfderiv_const]

/-- The height differential is right invariant under finite elements of the compact subgroup. -/
theorem heightDifferential_mul_ofFinite (X : smoothModel F d) (b₀ : FinPts)
    (hb₀ : ofFinite F G b₀ ∈ K) (g : Adeles) :
    directional X lam (g * ofFinite F G b₀) = directional X lam g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let a := infinite F G g
  let b := finite F G g
  have he : pairHeight hK lam (b * b₀) = pairHeight hK lam b := by
    funext x
    have hp : pair F G x (b * b₀) = pair F G x b * ofFinite F G b₀ := by
      rw [ofFinite_eq_pair, pair_mul, mul_one]
    rw [pairHeight, hp, hK.height_mul_right _ hb₀]
    rfl
  change groupDirectionalValue I X (pairHeight hK lam (finite F G (g * ofFinite F G b₀)))
    (infinite F G (g * ofFinite F G b₀)) = groupDirectionalValue I X (pairHeight hK lam b) a
  simp only [map_mul, infinite_ofFinite, finite_ofFinite, mul_one]
  exact congrArg (fun f => groupDirectionalValue I X f a) he

/-- Infinite compact translation transforms the differential by actual tangent conjugation. -/
theorem heightDifferential_mul_ofInfinite (X : smoothModel F d) (k : Inf)
    (hk : ofInfinite F G k ∈ K) (g : Adeles) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    directional X lam (g * ofInfinite F G k) =
      directional (groupTangentConjugation I k X) lam g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let a := infinite F G g
  let b := finite F G g
  have he : (fun x => pairHeight hK lam b (x * k)) = pairHeight hK lam b := by
    funext x
    have hp : pair F G (x * k) b = pair F G x b * ofInfinite F G k := by
      rw [ofInfinite_eq_pair, pair_mul, mul_one]
    rw [pairHeight, hp, hK.height_mul_right _ hk]
    rfl
  change groupDirectionalValue I X (pairHeight hK lam (finite F G (g * ofInfinite F G k)))
    (infinite F G (g * ofInfinite F G k)) =
      groupDirectionalValue I (groupTangentConjugation I k X) (pairHeight hK lam b) a
  simp only [map_mul, finite_ofInfinite, infinite_ofInfinite, mul_one]
  have hb : ContMDiff I 𝓘(ℝ, ℂ) ∞ (pairHeight hK lam b) := hH lam b
  change groupDirectionalValue I X (pairHeight hK lam b) (a * k) = _
  rw [groupDirectionalValue_rightTranslation I k X hb, he]

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

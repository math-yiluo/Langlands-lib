import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Geometry.Manifold.SmoothGroupListDerivative

/-! # Invariant derivatives of infinite slices and of the Iwasawa height pairings

For a function `ψ` on the actual adelic points, `sliceDerivative hsmooth X ψ` differentiates
each infinite slice `a ↦ ψ(a, b)` in the invariant direction `X`. It is the untwisted case
`λ = 0` of `IsIwasawaCompact.parameterDirectionalSection`, and it commutes with left translations
that change `ψ` by additive constants.

For a maximal compact Iwasawa subgroup `K`, the Iwasawa height of `(a, b)` is the sum of the
heights of `a` and of `b`. When the height pairings are smooth, all nonempty iterated invariant
derivatives of their infinite slices are bounded on the whole group, uniformly in the finite
point, because the infinite height changes by constants under the parabolic and the parabolic
times a compact set covers the infinite points. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]

section Slices

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "Adeles" => AdelicGroupPoints F G

/-- The invariant derivative in direction `X` of every infinite slice of `ψ`:
`(a, b) ↦ (X · ψ(·, b))(a)`. -/
def sliceDerivative (X : smoothModel F d) (ψ : Adeles → ℂ) : Adeles → ℂ := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact fun g => groupDirectionalValue 𝓘∞ X (fun a => ψ (pair F G a (finite F G g)))
    (infinite F G g)

/-- The infinite slices of `sliceDerivative X ψ` are the invariant derivatives of the
infinite slices of `ψ`. -/
theorem sliceDerivative_pair (X : smoothModel F d) (ψ : Adeles → ℂ)
    (b : FiniteAdelicGroupPoints F G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    (fun a => sliceDerivative hsmooth X ψ (pair F G a b)) =
      groupDirectionalValue 𝓘∞ X (fun a => ψ (pair F G a b)) := by
  funext a
  simp only [sliceDerivative, infinite_pair, finite_pair]

/-- Left translation by `g₀` commutes with slice derivatives when it changes `ψ` by a constant. -/
theorem sliceDerivative_mul_of_add_const (X : smoothModel F d) {ψ : Adeles → ℂ}
    (hψ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => ψ (pair F G a b)))
    (g₀ : Adeles) (κ : ℂ) (hg₀ : ∀ g, ψ (g₀ * g) = ψ g + κ) (g : Adeles) :
    sliceDerivative hsmooth X ψ (g₀ * g) = sliceDerivative hsmooth X ψ g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  set a := infinite F G g
  set b := finite F G g
  set a₀ := infinite F G g₀
  set b₀ := finite F G g₀
  have hg : g = pair F G a b := (pair_projections F G g).symm
  have hg₀g : g₀ * g = pair F G (a₀ * a) (b₀ * b) := by
    rw [hg, ← pair_projections F G g₀, pair_mul]
  have hslice : (fun z => ψ (pair F G z (b₀ * b))) =
      fun z => ψ (pair F G (a₀⁻¹ * z) b) + κ := by
    funext z
    have h : pair F G z (b₀ * b) = g₀ * pair F G (a₀⁻¹ * z) b := by
      rw [← pair_projections F G g₀, pair_mul, mul_inv_cancel_left]
    rw [h, hg₀]
  change groupDirectionalValue 𝓘∞ X (fun z => ψ (pair F G z (finite F G (g₀ * g))))
      (infinite F G (g₀ * g)) =
    groupDirectionalValue 𝓘∞ X (fun z => ψ (pair F G z b)) a
  rw [hg₀g, infinite_pair, finite_pair, hslice]
  have hsm : ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun z => ψ (pair F G (a₀⁻¹ * z) b)) :=
    (hψ b).comp (contMDiff_const.mul contMDiff_id)
  have h1 : groupDirectionalValue 𝓘∞ X (fun z => ψ (pair F G (a₀⁻¹ * z) b) + κ) (a₀ * a) =
      groupDirectionalValue 𝓘∞ X (fun z => ψ (pair F G (a₀⁻¹ * z) b)) (a₀ * a) :=
    congrFun (listDirectionalDerivative_add_const (w := [X]) (by simp) hsm κ) (a₀ * a)
  rw [h1]
  exact (groupDirectionalValue_leftTranslation 𝓘∞ X a₀⁻¹ (fun y => ψ (pair F G y b))
    (a₀ * a)).trans (by rw [inv_mul_cancel_left])

end Slices

section Heights

variable {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "Ar" => CommAlgCat.of F (InfiniteAdeleRing F)

omit [IsClosedImmersion p.hom.hom.left] in
private theorem infinite_map_apply' (g : AdelicGroupPoints F P) :
    infinite F G (map F P G p g) = P.affinePointsTarget p Ar (infinite F P g) :=
  DFunLike.congr_fun (P.affinePointsTarget_naturality p
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) g

omit [IsClosedImmersion p.hom.hom.left] in
include hK in
/-- Every infinite point is a parabolic infinite point times the infinite component of an
element of `K`. -/
theorem IsIwasawaCompact.exists_infinite_factor (a : InfiniteAdelicGroupPoints F G) :
    ∃ x : InfiniteAdelicGroupPoints F P, ∃ k ∈ K,
      a = P.affinePointsTarget p Ar x * infinite F G k := by
  obtain ⟨q, k, hk, h⟩ := hK.exists_eq (ofInfinite F G a)
  refine ⟨infinite F P q, k, hk, ?_⟩
  have hinf := congrArg (infinite F G) h
  rw [map_mul, infinite_map_apply', infinite_ofInfinite] at hinf
  exact hinf.symm

/-- For a compact subgroup containing the infinite components of its elements, the height of
`(a, b)` is the height of `a` plus the height of `b`. -/
theorem IsIwasawaCompact.height_pair_eq_add
    (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    hK.height (pair F G a b) = hK.height (ofInfinite F G a) + hK.height (ofFinite F G b) := by
  obtain ⟨x, k, hk, ha⟩ := hK.exists_infinite_factor a
  have heq : ofInfinite F G a =
      map F P G p (ofInfinite F P x) * ofInfinite F G (infinite F G k) := by
    rw [map_ofInfinite, ← map_mul, ← ha]
  have hpair : pair F G a b = ofInfinite F G a * ofFinite F G b := by
    rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
  rw [hpair, heq, mul_assoc, (factors_commute F G (infinite F G k) b).eq, ← mul_assoc,
    hK.height_mul_right _ (hInf k hk), hK.height_map_mul, hK.height_mul_right _ (hInf k hk),
    hK.height_map]

/-- The height changes by the logarithm of the parabolic point under left translation of the
infinite argument. -/
theorem IsIwasawaCompact.height_ofInfinite_mul (x : InfiniteAdelicGroupPoints F P)
    (a : InfiniteAdelicGroupPoints F G) :
    hK.height (ofInfinite F G (P.affinePointsTarget p Ar x * a)) =
      characterLog F P (ofInfinite F P x) + hK.height (ofInfinite F G a) := by
  rw [map_mul, ← map_ofInfinite, hK.height_map_mul]

/-- All nonempty iterated invariant derivatives of the infinite slices of a height pairing are
bounded, uniformly in the finite point. -/
theorem IsIwasawaCompact.exists_bound_heightPairing_derivative
    (hH : hK.HasSmoothHeightPairings hsmooth)
    (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (lam : ComplexCharacterParameter F P)
    {w : List (smoothModel F d)} (hw : w ≠ []) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∃ M : ℝ, ∀ b a, ‖listDirectionalDerivative (G := InfiniteAdelicGroupPoints F G) w
      (fun z => complexParameterPairing F P lam (hK.height (pair F G z b))) a‖ ≤ M := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let s : InfiniteAdelicGroupPoints F G → ℂ :=
    fun z => complexParameterPairing F P lam (hK.height (ofInfinite F G z))
  have hs : ContMDiff 𝓘∞ 𝓘ℂ ∞ s := hH lam 1
  have hslice (b : FiniteAdelicGroupPoints F G) :
      (fun z => complexParameterPairing F P lam (hK.height (pair F G z b))) =
        fun z => s z + complexParameterPairing F P lam (hK.height (ofFinite F G b)) := by
    funext z
    rw [hK.height_pair_eq_add hInf, map_add]
  have hbound := exists_bound_listDirectionalDerivative_of_quasiInvariant hs
    (Set.range (P.affinePointsTarget p Ar)) (infinite F G '' (K : Set (AdelicGroupPoints F G)))
    (hK.isCompact.image (infinite F G).continuous)
    (fun a => by
      obtain ⟨x, k, hk, ha⟩ := hK.exists_infinite_factor a
      exact ⟨_, ⟨x, rfl⟩, _, ⟨k, hk, rfl⟩, ha⟩)
    (fun _ ⟨x, hx⟩ => ⟨complexParameterPairing F P lam (characterLog F P (ofInfinite F P x)),
      fun a => by
        rw [← hx]
        change complexParameterPairing F P lam
            (hK.height (ofInfinite F G (P.affinePointsTarget p Ar x * a))) = _
        rw [hK.height_ofInfinite_mul, map_add, add_comm]⟩)
    hw
  obtain ⟨M, hM⟩ := hbound
  refine ⟨M, fun b a => ?_⟩
  rw [hslice b, listDirectionalDerivative_add_const hw hs]
  exact hM a

end Heights

end Langlands.Global.AdelicGroupPoints

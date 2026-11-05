import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedCoefficientSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # Twisted coefficients on `Im X(G)` for the rational points of a connected reductive group

For `G(F)` with `G` connected reductive over a nonarchimedean local field, the Library's circle
coordinates `Im X(G) ≃ (Fin r → Circle)` write a unitary unramified character as
`χ(g) = ∏ᵢ zᵢ^{n(g)ᵢ}`, where `n(g) ∈ ℤ^r` are the coordinates of the valuation image of `g`
(`RationalValuationCoordinates`). This module transports `twistedCoefficientFamily` to the
function `χ ↦ ∫ f(g) φ(g) χ(g) dmu(g)` on `Im X(G)` (Waldspurger, proof of Proposition VII.1.3).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalTwistedCoefficient1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalTwistedCoefficient2 :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G
local instance instRationalTwistedCoefficient3 :
    Nonempty (CompactOpenSubgroup (GroupScheme.rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable (hG : GroupScheme.IsConnectedReductive G)

variable [MeasurableSpace (GroupScheme.rationalPoints G)]
  [OpensMeasurableSpace (GroupScheme.rationalPoints G)]

variable {G} (mu : Measure (GroupScheme.rationalPoints G))

/-- The twisted coefficient `χ ↦ ∫_{G(F)} f(g) φ(g) χ(g) dmu(g)` as a function on the actual
unitary unramified characters `Im X(G)`. -/
def rationalTwistedCoefficient (f φ : GroupScheme.rationalPoints G → ℂ)
    (χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) : ℂ :=
  ∫ g, f g * φ g * ((χ.val g : ℂˣ) : ℂ) ∂mu

omit [LocallyOfFiniteType G.X.hom] [OpensMeasurableSpace (GroupScheme.rationalPoints G)] in
/-- In circle coordinates, the twisted coefficient is the torus Fourier synthesis of `f φ`
along `n`. -/
theorem rationalTwistedCoefficient_comp_coordinates (f φ : GroupScheme.rationalPoints G → ℂ) :
    rationalTwistedCoefficient mu f φ ∘
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm =
      torusSynthesis mu (rationalValuationCoordinates G hG) (fun g => f g * φ g) := by
  funext z
  simp only [Function.comp_apply, rationalTwistedCoefficient, torusSynthesis,
    rationalUnitaryUnramifiedCharacter_apply G hG]

variable {Ξ σ : GroupScheme.rationalPoints G → ℝ} {C : ℝ} {φ : GroupScheme.rationalPoints G → ℂ}
  {r : ℝ}

/-- In circle coordinates, the twisted coefficient of `f ∈ C(G)` is the image of `f` under
`twistedCoefficientFamily` for the lattice coordinates `n`. -/
theorem rationalTwistedCoefficient_comp_coordinates_eq (hw : L2Weights mu Ξ σ)
    (hnσ : ∀ g, ‖rationalValuationCoordinates G hG g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) :
    rationalTwistedCoefficient mu f φ ∘
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm =
      (twistedCoefficientFamily hw (measurable_rationalValuationCoordinates G hG) hnσ hφc hφ f :
        (Fin (rationalImageRank G) → Circle) → ℂ) :=
  rationalTwistedCoefficient_comp_coordinates hG mu f φ

/-- **Smoothness on `Im X(G)`** (first assertion in the proof of Proposition VII.1.3, case
`M = G`): in circle coordinates, `χ ↦ ∫ f(g) φ(g) χ(g) dmu(g)` is smooth for `f ∈ C(G)`. -/
theorem isSmoothFiniteTorusFunction_rationalTwistedCoefficient (hw : L2Weights mu Ξ σ)
    (hnσ : ∀ g, ‖rationalValuationCoordinates G hG g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) :
    IsSmoothFiniteTorusFunction (rationalTwistedCoefficient mu f φ ∘
      (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm) := by
  rw [rationalTwistedCoefficient_comp_coordinates_eq hG mu hw hnσ hφc hφ f]
  exact (twistedCoefficientFamily hw (measurable_rationalValuationCoordinates G hG) hnσ hφc hφ
    f).2

/-- **Estimate (2) on `Im X(G)`**, in circle coordinates: every iterated angle derivative of the
twisted coefficient of `f ∈ C(G)` is bounded by `|C|^{|l|} ν_{d+r+|l|}(f) ν_{-r}(φ) c`. -/
theorem norm_torusPartialDerivList_rationalTwistedCoefficient_le (hw : L2Weights mu Ξ σ)
    (hnσ : ∀ g, ‖rationalValuationCoordinates G hG g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) (l : List (Fin (rationalImageRank G)))
    (z : Fin (rationalImageRank G) → Circle) :
    ‖torusPartialDerivList l (rationalTwistedCoefficient mu f φ ∘
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm) z‖ ≤
      ‖C‖ ^ l.length *
        (nu Ξ σ (hw.exponent + r + l.length) f * nu Ξ σ (-r) φ * hw.const).toReal := by
  rw [rationalTwistedCoefficient_comp_coordinates_eq hG mu hw hnσ hφc hφ f]
  exact norm_torusPartialDerivList_twistedCoefficientFamily_le hw
    (measurable_rationalValuationCoordinates G hG) hnσ hφc hφ f l z

end Langlands.HarishChandraSchwartz

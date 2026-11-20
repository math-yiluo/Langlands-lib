import Langlands.Automorphic.GeneralLinearTwoBlockParabolic
import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Automorphic.ConstantTerm
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.FiniteAdelicGL.LocalFactor

/-!
# Local block-unipotent vanishing at one place gives vanishing along every adelic radical

Let `F` be a number field, `v` a finite place of `F`, and `f : GL_n(𝔸_F) → ℂ` continuous with
compact support. Suppose that the integrals of `f` along the upper two-block unipotent
subgroups of `GL_n(F_v)`, inserted at `v`, vanish for every two-sided translate:

`∫ f(x · ι_v([[1, Z], [0, 1]]) · y) dZ = 0`

for every split `a + b = n` with `a, b ≥ 1`, every Haar measure `dZ` on `a × b` matrices over
`F_v` and all `x, y ∈ GL_n(𝔸_F)`. Then, for the `GL_n` group scheme over `F`, the integral of
`f` (through the Library's identification of adelic points with `GL_n(𝔸_F)`) along every
two-sided translate of the adelic points of the unipotent radical of every proper rational
parabolic vanishes.

This is the step of the proof of Getz–Hahn 2024, Lemma 16.4.2 (printed p. 430), that passes from
the local condition at one place to the adelic radicals, for `GL_n`. It is derived content.
See `GeneralLinearRadicalIntegralVanishingStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Automorphic Langlands.GeneralLinear Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions

local instance generalLinearRadicalIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearRadicalSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- If `f` is continuous with compact support on `GL_n(𝔸_F)` and its integrals over the
upper two-block unipotent subgroups of `GL_n(F_v)`, at one finite place `v`, vanish for every
two-sided translate, then for the `GL_n` group scheme over `F` the integral of `f` (through
`GeneralLinearGroupPoints.adelicHomeomorph`) over every two-sided translate of the adelic points
of the unipotent radical of every proper rational parabolic vanishes, for the Library's
normalized radical Haar measure. -/
def GeneralLinearRadicalIntegralVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (v : Langlands.Global.FinitePlace F) (f : AdelicGL F n → ℂ), Continuous f → HasCompactSupport f →
    (∀ (a b : ℕ) (h : a + b = n), 0 < a → 0 < b →
      letI : MeasurableSpace (Matrix (Fin a) (Fin b) (FiniteCompletion F v)) := borel _
      ∀ ν : Measure (Matrix (Fin a) (Fin b) (FiniteCompletion F v)), ν.IsAddHaarMeasure →
        ∀ x y : AdelicGL F n,
          ∫ Z, f (x * AdelicGL.ofFinite F n
            (FiniteAdelicGL.localInclusion F n v (blockUnipotent h Z)) * y) ∂ν = 0) →
    ∀ (P : ProperRationalParabolic
        (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
      (x y : AdelicGroupPoints F
        (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))),
      ∫ m, f (GeneralLinearGroupPoints.adelicHomeomorph F n
          (x * (m : AdelicGroupPoints F
            (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) * y))
        ∂properParabolicHaarMeasure F
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hPD hG P = 0

end Langlands.TraceFormula

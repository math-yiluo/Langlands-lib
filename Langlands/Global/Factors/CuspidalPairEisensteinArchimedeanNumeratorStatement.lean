import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # The archimedean numerator of the open-cell integral

The open-cell integrand restricted to the adelic matrices with vanishing finite components is a
function on the archimedean matrices `M_((t+1)×(r+1))(F_∞)`; its integral for a Haar measure is
the archimedean part of the open-cell integral. This module states that one finite set `S₁` of
finite places works for every point `s₀` of the imaginary axis: at `s₀` there is a section,
spherical outside `S₁`, whose archimedean open-cell integral converges absolutely on a right
half-plane and is there a meromorphic function regular and nonzero at `s₀`. This is the
archimedean part of the proof of Shahidi (1981), Theorem 5.1, pp. 351–352, with
Proposition 3.2, p. 333. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global

open MeasureTheory NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairEisenstein

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

/-- The adelic `(t + 1) × (r + 1)` matrix with archimedean component `X` and component `0` at
every finite place. -/
def archimedeanMatrix (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :
    Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) :=
  fun i j => ((X i j, 0) : Adeles F)

/-- A Haar measure on the additive group `M_((t+1)×(r+1))(F_∞)` of archimedean matrices, for its
Borel σ-algebra (which is not made an instance). -/
def archimedeanOpenCellHaar :
    @Measure (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F))
      (borel (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F))) :=
  letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := borel _
  haveI : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → InfiniteAdeles F))
  Measure.addHaar

variable {F r t}

/-- The archimedean open-cell integrand: the open-cell integrand `openCellIntegrand` at the
adelic matrix with archimedean component `X` and vanishing finite components. -/
def archimedeanOpenCellIntegrand (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ)
    (s : ℂ) (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) : ℂ :=
  openCellIntegrand ψ φ s (archimedeanMatrix F r t X)

/-- The archimedean open-cell integral: the integral of `archimedeanOpenCellIntegrand` for
`archimedeanOpenCellHaar`. -/
def archimedeanOpenCellIntegral (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ)
    (s : ℂ) : ℂ :=
  letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := borel _
  ∫ X, archimedeanOpenCellIntegrand ψ φ s X ∂(archimedeanOpenCellHaar F r t)

end CuspidalPairEisenstein

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters and a standard
additive character `ψ`, there is a finite set `S₁` of finite places such that for every `s₀`
with `Re s₀ = 0` there are a section `φ` built from cusp forms spherical outside `S₁`, a
function `c`, meromorphic on `ℂ`, analytic and nonzero at `s₀`, and a real `σ` such that for
`Re s > σ` the archimedean open-cell integrand of `φ` is integrable and its integral is
`c s`. -/
def CuspidalPairEisensteinArchimedeanNumeratorStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
  ∃ S₁ : Finset (FinitePlace F),
    ∀ s₀ : ℂ, s₀.re = 0 →
      ∃ φ : AdelicGL F (r + t + 2) → ℂ, IsSection T T' φ ∧ IsSphericalSectionOutside T T' S₁ φ ∧
        ∃ c : ℂ → ℂ, MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
            (letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :=
                borel _;
              Integrable (archimedeanOpenCellIntegrand ψ φ s) (archimedeanOpenCellHaar F r t)) ∧
            c s = archimedeanOpenCellIntegral ψ φ s

end Langlands.Global

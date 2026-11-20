import Langlands.Shimura.Unitary.FiniteModels
import Langlands.Algebra.BrauerComparison.AbsoluteComparison
import Langlands.ClassFieldTheory.Local.SeparableLocalInvariant
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.FiniteCompletionLocalField

/-! # Realization of split finite Brauer data and real unitary signatures -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local

variable (E : Type u) (K : Type v)
  [Field E] [NumberField E] [Field K] [NumberField K]

/-- The local Brauer invariant for the actual finite completion. -/
def finiteBrauerInvariant (q : Langlands.Global.FinitePlace K) :
    BrauerGroup (FiniteCompletion K q) ≃+ RationalModIntegers :=
  letI := FiniteCompletion.valuativeRel q
  letI := FiniteCompletion.isNonarchimedeanLocalField q
  (BrauerComparison.brauerEquiv _).trans (separableLocalInvariant _)

/-- Identify the actual completion with a representative to which the
same-universe Brauer group applies. -/
def HasCompletedBrauerInvariant (A : Type w) [Ring A] [Algebra K A]
    (q : Langlands.Global.FinitePlace K) (x : RationalModIntegers) : Prop :=
  ∃ B : CSA.{v, v} (FiniteCompletion K q),
    Nonempty (CompletedAlgebra K A q ≃ₐ[FiniteCompletion K q] B) ∧
      finiteBrauerInvariant K q (Brauer.classOf B) = x

/-- The only compatibility condition for profiles with maximal Witt index
at all nonsplit finite places. The real signature has `r τ` positive lines. -/
def CompatibleUnitaryLocalProfile {n : ℕ} {s : Finset (Langlands.Global.FinitePlace E)}
    (a : s → ZMod n) (r : (E →+* ℝ) → ℕ) : Prop :=
  ∀ h : 2 ∣ n,
    (∑ p : s, ZMod.castHom h (ZMod 2) (a p)) +
      ((Fintype.card (E →+* ℝ) * (n / 2) : ℕ) : ZMod 2) +
      (∑ τ : E →+* ℝ, ((n - r τ : ℕ) : ZMod 2)) = 0

variable [IsTotallyReal E] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- Global existence for prescribed signed Brauer invariants at a finite
set of split places, with arbitrary real signatures. -/
def UnitaryLocalProfileRealizationStatement : Prop := by
  classical
  exact ∀ (n : ℕ) (hn : 1 < n) (s : Finset (Langlands.Global.FinitePlace E)),
    (∀ p : s, IsSplitPlace E K p.val) →
    ∀ (positive : ∀ p : s, FinitePlacesAbove K p.val)
      (a : s → ZMod n) (r : (E →+* ℝ) → ℕ),
      (∀ τ, r τ ≤ n) →
      CompatibleUnitaryLocalProfile E a r →
      ∃ (A : Type (max u v)) (ringA : Ring A),
        letI : Ring A := ringA
        ∃ algE : Algebra E A,
          letI : Algebra E A := algE
          ∃ algK : Algebra K A,
            letI : Algebra K A := algK
            ∃ tower : IsScalarTower E K A,
              letI : IsScalarTower E K A := tower
              ∃ D : CentralSimpleUnitaryData E K A n,
                (∀ τ, HasSignature D.toSecondKindInvolution τ n (r τ)) ∧
                (∀ p : Langlands.Global.FinitePlace E, p ∉ s →
                  IsQuasiSplitAt D.toSecondKindInvolution n p) ∧
                ∀ (p : s) (q : FinitePlacesAbove K p.val),
                  HasCompletedBrauerInvariant K A q.val
                    (denominatorEquiv n (by omega) (if q = positive p then a p else -a p))

end Langlands.Shimura.FiniteUnitary

import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.FiniteTensorUnitaryForm
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Automorphic.OperatorDeterminantSliceHaar

/-! # Positive forms on the prescribed cuspidal spectral components -/

noncomputable section
universe uF uQ
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.CompletionPadic ContinuousRationalFunctions
open NumberField MeasureTheory
open scoped NNReal

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance cuspidalSpectralUnitaryFormAddCommGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalSpectralUnitaryFormAddCommGroup2 (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalSpectralUnitaryFormAddCommGroup3 (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalSpectralUnitaryFormAddCommGroup4 (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalSpectralUnitaryFormAddCommGroup5 (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance {n : ℕ} (S : FiniteRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance {n : ℕ} {v : Global.FinitePlace F} (S : LocalRealization F n v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace CuspidalOperatorRealization.FiniteSlice

variable {r : ℕ} {T : CuspidalOperatorRealization F r} (A : T.FiniteSlice)

/-- Restrict the original finite-action form to an actual finite slice. -/
def unitaryForm (b : Langlands.InvariantPositiveForm T.realization.finiteRepresentation) :
    Langlands.InvariantPositiveForm A.subspace.representation :=
  (b.ofEquiv T.realization.finiteEquiv.symm).comap A.inclusion A.inclusion_injective

@[simp] theorem unitaryForm_inner
    (b : Langlands.InvariantPositiveForm T.realization.finiteRepresentation)
    (f g : A.subspace.Space) :
    (A.unitaryForm b).inner f g =
      b.inner (T.realization.finiteEquiv.symm (A.inclusion f))
        (T.realization.finiteEquiv.symm (A.inclusion g)) := rfl

end CuspidalOperatorRealization.FiniteSlice

namespace CuspidalSpectralPresentation

variable {r : ℕ} {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{uF, uQ} T)

/-- The chosen actual tensor slice inherits the original finite-action form. -/
def localUnitaryForm
    (b : Langlands.InvariantPositiveForm T.realization.finiteRepresentation) (v : Global.FinitePlace F) :
    Langlands.InvariantPositiveForm (P.localComponent v).representation :=
  P.presentation.sliceUnitaryForm (P.finiteSlice.unitaryForm b) v
    (P.presentation.chosenTail P.finiteSlice.nonzero v)

/-- Canonical p-adic packaging keeps the identical carrier, action and form. -/
def padicUnitaryForm
    (b : Langlands.InvariantPositiveForm T.realization.finiteRepresentation)
    (v : Global.FinitePlace F) (hI : (P.localComponent v).IsIrreducible)
    (hA : (P.localComponent v).IsAdmissible) :
    letI := (padicField v).canonicalTopologicalData.topology
    Langlands.InvariantPositiveForm ((P.localComponent v).padicObject hI hA).obj.representation :=
  P.localUnitaryForm b v

/-- Band square integrability yields the form on the prescribed p-adic component. -/
def padicUnitaryFormOfHaar
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hT : T.HasCentralCharacter χ)
    (hL2 : ∀ f : T.Space, MemLp (OperatorDeterminantSlice.toQuotient F (r + 1)
      T.realization f) 2 ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))))
    (v : Global.FinitePlace F) (hI : (P.localComponent v).IsIrreducible)
    (hA : (P.localComponent v).IsAdmissible) :
    letI := (padicField v).canonicalTopologicalData.topology
    Langlands.InvariantPositiveForm ((P.localComponent v).padicObject hI hA).obj.representation :=
  P.padicUnitaryForm (OperatorDeterminantSlice.finiteInvariantPositiveFormOfHaar F (r + 1)
    T.realization (Nat.succ_ne_zero r) χ hχ hT hL2) v hI hA

variable [MeasurableSpace (AdelicGL F (r + 1))] [BorelSpace (AdelicGL F (r + 1))]

/-- An actual covering-set integral estimate yields the form on the exact local object. -/
def padicUnitaryFormOfCover
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hT : T.HasCentralCharacter χ)
    (t : Set (AdelicGL F (r + 1))) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F (r + 1),
      1 ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F (r + 1) x : ℝ≥0) : ℝ) ∧
        ((AdelicBlockDeterminantCharacter.determinantNorm F (r + 1) x : ℝ≥0) : ℝ) ≤ 2 →
        ∃ a : RationalGL F (r + 1), AdelicGL.rational F (r + 1) a * x ∈ t)
    (hfinite : ∀ f : T.Space,
      (∫⁻ x in t, ‖evaluate F (r + 1) (T.realization.toContinuous f) x‖ₑ ^ 2
        ∂OperatorDeterminantSlice.matrixHaarMeasure F (r + 1)) < ⊤)
    (v : Global.FinitePlace F) (hI : (P.localComponent v).IsIrreducible)
    (hA : (P.localComponent v).IsAdmissible) :
    letI := (padicField v).canonicalTopologicalData.topology
    Langlands.InvariantPositiveForm ((P.localComponent v).padicObject hI hA).obj.representation :=
  P.padicUnitaryForm (OperatorDeterminantSlice.finiteInvariantPositiveFormOfCover F (r + 1)
    T.realization (Nat.succ_ne_zero r) χ hχ hT t ht hcover hfinite) v hI hA

end CuspidalSpectralPresentation
end Langlands.Automorphic

import Langlands.Automorphic.ArchimedeanFixedCompactDensity
import Langlands.Automorphic.CuspidalHilbertActionCompatibility
import Langlands.Automorphic.OperatorFixedJointVectorRecovery

/-! # Fixed-level derivative density statement for actual cuspidal realizations -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic.CuspidalFixedSmoothDensity

open Langlands.Global Langlands.Archimedean Langlands.Archimedean.SmoothInvariantSubspace

universe u uV uX

section JointRecovery

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} {D : X → Module.End ℂ V}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V}
  (b : OperatorUnitaryFormCore ρ κ D)
  (U : AdelicGL F n →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion))

local notation "σ" => finiteHilbertAction F n U
local notation "π" => infiniteHilbertAction F n U

/-- Joint vector recovery and agreement with the original actions give
derivative density in the original form completion. -/
theorem dense_fixedSmoothImage_of_jointRecovery
    (hU : b.BoundedActionCompatibility U (AdelicGL.ofFinite F n)
      (fun k : standardInfiniteCompact F n => AdelicGL.ofInfinite F n k.val))
    (J : OpenSubgroup (FiniteAdelicGL F n)) (hrec : b.JointVectorRecovery) :
    Dense (OperatorUnitaryFormCore.fixedSmoothImage (A := ArchimedeanMatrix F n) b σ J π) := by
  have hk (k : standardInfiniteCompact F n) (x : b.HilbertCompletion) :
      π (compactCoordinates F n k) x = b.completedCompactRepresentation k x :=
    (infiniteHilbertAction_compactCoordinates_apply F n U k x).trans (hU.2 k x)
  exact OperatorUnitaryFormCore.dense_fixedSmoothImage_of_dense_compactFinite
    (A := ArchimedeanMatrix F n) (Garch := ArchimedeanGL F n)
    b σ J π hrec (fun d x => hU.1 d x)
    (dense_compactFinite_fixedSmooth F n (H := b.HilbertCompletion) U
      b.completedCompactRepresentation hk J.toSubgroup)

end JointRecovery

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

local instance fixedSmoothRationalGroup {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance fixedSmoothContinuousGroup {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance fixedSmoothFiniteGroup {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance fixedSmoothFormsGroup {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance fixedSmoothStableGroup {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance fixedSmoothSpaceGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)] (T : CuspidalOperatorRealization F r)
  (b : T.realization.UnitaryForm)
  (U : AdelicGL F (r + 1) →* (b.finiteForm.HilbertCompletion →L[ℂ] b.finiteForm.HilbertCompletion))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "σ" => finiteHilbertAction F (r + 1) U
local notation "π" => infiniteHilbertAction F (r + 1) U

variable (J : OpenSubgroup (FiniteAdelicGL F (r + 1)))

/-- Fixed smooth vectors in the image of the original finite-level carrier. -/
abbrev fixedSmoothImage : Set (ambientFixedSmoothSubspace σ J.toSubgroup π I) :=
  OperatorUnitaryFormCore.fixedSmoothImage (A := ArchimedeanMatrix F (r + 1)) b σ J π

/-- Derivative density of the original fixed smooth image for every compatible
full adelic action. -/
def FixedLevelDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r) (b : T.realization.UnitaryForm)
    (U : AdelicGL F (r + 1) →*
      (b.finiteForm.HilbertCompletion →L[ℂ] b.finiteForm.HilbertCompletion))
    (J : OpenSubgroup (FiniteAdelicGL F (r + 1))),
    b.BoundedActionCompatibility U (AdelicGL.ofFinite F (r + 1))
      (fun k : standardInfiniteCompact F (r + 1) => AdelicGL.ofInfinite F (r + 1) k.val) →
      Dense (fixedSmoothImage T b U J)

end Langlands.Automorphic.CuspidalFixedSmoothDensity

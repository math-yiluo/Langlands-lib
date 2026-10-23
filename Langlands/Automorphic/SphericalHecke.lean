import Langlands.Automorphic.LocalHecke
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Representation.Unramified.HeckeOperators

/-! # Standard spherical Hecke operators on actual automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions
open MeasureTheory Langlands.Hecke

variable (K : Type u) [Field K] [NumberField K]
variable (v : Langlands.Global.FinitePlace K)

local instance sphericalFormsRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance sphericalFormsContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance sphericalFormsSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance sphericalFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

local instance sphericalFormsGLTopology (n : ℕ) :
    TopologicalSpace (FiniteLocalGL K n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology n
local instance sphericalFormsGLTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (FiniteLocalGL K n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup n
local instance sphericalFormsGLT2 (n : ℕ) : T2Space (FiniteLocalGL K n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space n
local instance sphericalFormsGLMeasurable (n : ℕ) : MeasurableSpace (FiniteLocalGL K n v) :=
  borel _
local instance sphericalFormsGLBorel (n : ℕ) : BorelSpace (FiniteLocalGL K n v) := ⟨rfl⟩

local instance sphericalFormsHaar (r : ℕ) :
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r).IsHaarMeasure :=
  Unramified.sphericalHaar_isHaar (CompletionPadic.padicField v) r

/-- The existing actual local action is smooth for the canonical p-adic topology. -/
theorem automorphicLocalRightAction_isSmooth_canonical (n : ℕ) :
    Langlands.IsSmooth (automorphicLocalRightAction K n v) := by
  change @Langlands.IsSmooth ℂ (FiniteLocalGL K n v) (AutomorphicForms K n) _ _ _ _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology n)
    (automorphicLocalRightAction K n v)
  rw [← FiniteAdelicGL.localGL_topology_eq K v n]
  exact automorphicLocalRightAction_isSmooth K n v

/-- The actual automorphic vectors fixed by the canonical spherical subgroup. -/
abbrev AutomorphicSphericalVectors (r : ℕ) :=
  Langlands.fixedVectors (automorphicLocalRightAction K (r + 1) v)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

/-- The type of canonical spherical corner actions on actual automorphic fixed vectors. -/
abbrev AutomorphicSphericalHeckeAction (r : ℕ) :=
  Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField v) r →ₐ[ℂ]
    Module.End ℂ (AutomorphicSphericalVectors K v r)

/-- The canonical mass-one spherical corner acts on existing automorphic fixed vectors. -/
def automorphicSphericalHeckeAction (r : ℕ) : AutomorphicSphericalHeckeAction K v r :=
  @Hecke.cornerAction (FiniteLocalGL K (r + 1) v) _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1)) _ _ _ _ _
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r) _
    (automorphicLocalRightAction K (r + 1) v)
    (automorphicLocalRightAction_isSmooth_canonical K v (r + 1))
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)

/-- The standard diagonal double-coset operator on actual automorphic spherical vectors. -/
def automorphicStandardHeckeOperator (r : ℕ) (i : Fin (r + 2)) :
    Module.End ℂ (AutomorphicSphericalVectors K v r) :=
  automorphicSphericalHeckeAction K v r
    (Unramified.standardHeckeElement (CompletionPadic.padicField v) r i)

@[simp] theorem automorphicStandardHeckeOperator_zero (r : ℕ) :
    automorphicStandardHeckeOperator K v r 0 = 1 := by
  simp only [automorphicStandardHeckeOperator, Unramified.standardHeckeElement_zero, map_one]

/-- A genuine nonzero eigenform relation, without a classification assertion. -/
def IsSphericalHeckeEigenform (r : ℕ) (s : Unramified.Eigenvalues (r + 1))
    (f : AutomorphicSphericalVectors K v r) : Prop :=
  f ≠ 0 ∧ ∀ i : Fin (r + 2), automorphicStandardHeckeOperator K v r i f =
    Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i • f

/-- Global standard-integral invariance implies this actual local spherical invariance. -/
theorem mem_automorphicSphericalVectors_of_standardIntegral (r : ℕ)
    (f : AutomorphicForms K (r + 1))
    (hf : f ∈ Langlands.fixedVectors (automorphicFiniteRightAction K (r + 1))
      (FiniteAdelicGL.standardIntegral K (r + 1)).toSubgroup) :
    f ∈ AutomorphicSphericalVectors K v r := by
  change f ∈ Langlands.fixedVectors (automorphicLocalRightAction K (r + 1) v)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)
  rw [← FiniteAdelicGL.localIntegral_eq_sphericalSubgroup K v r]
  exact automorphicLocalIntegral_fixed_of_standardIntegral K (r + 1) v f hf

/-- Evaluation is the standard double-coset integral acting by positive right translation. -/
theorem evaluate_automorphicStandardHeckeOperator (r : ℕ) (i : Fin (r + 2))
    (f : AutomorphicSphericalVectors K v r) (x : AdelicGL K (r + 1)) :
    evaluate K (r + 1) (automorphicToContinuous K (r + 1)
      (automorphicStandardHeckeOperator K v r i f).val) x =
      ∫ g, Unramified.standardHeckeElement (CompletionPadic.padicField v) r i g *
        evaluate K (r + 1) (automorphicToContinuous K (r + 1) f.val)
          (x * AdelicGL.ofFinite K (r + 1) (FiniteAdelicGL.localInclusion K (r + 1) v g))
        ∂(Unramified.sphericalHaar (CompletionPadic.padicField v) r) := by
  exact Hecke.integratedAction_dual
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r)
    (automorphicLocalRightAction K (r + 1) v)
    (automorphicLocalRightAction_isSmooth_canonical K v (r + 1))
    (HeckeAlgebra.Corner.toHeckeAlgebra _ _ _
      (Unramified.standardHeckeElement (CompletionPadic.padicField v) r i))
    f.val (automorphicEvaluation K (r + 1) x)

end Langlands.Automorphic

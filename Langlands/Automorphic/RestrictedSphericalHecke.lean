import Langlands.Automorphic.SphericalHecke
import Langlands.Representation.Smooth.FixedVectors.LawsProof

/-! # Spherical Hecke operators on invariant restrictions of automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions
open MeasureTheory Langlands.Hecke

variable (K : Type u) [Field K] [NumberField K]
variable (v : Langlands.Global.FinitePlace K)

local instance restrictedSphericalFormsRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance restrictedSphericalFormsContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance restrictedSphericalFormsSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance restrictedSphericalFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

local instance restrictedSphericalFormsGLTopology (n : ℕ) :
    TopologicalSpace (FiniteLocalGL K n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology n
local instance restrictedSphericalFormsGLTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (FiniteLocalGL K n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup n
local instance restrictedSphericalFormsGLT2 (n : ℕ) : T2Space (FiniteLocalGL K n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space n
local instance restrictedSphericalFormsGLMeasurable (n : ℕ) : MeasurableSpace (FiniteLocalGL K n v) :=
  borel _
local instance restrictedSphericalFormsGLBorel (n : ℕ) : BorelSpace (FiniteLocalGL K n v) := ⟨rfl⟩

local instance restrictedSphericalFormsHaar (r : ℕ) :
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r).IsHaarMeasure :=
  Unramified.sphericalHaar_isHaar (CompletionPadic.padicField v) r

/-- The type of invariant ambient conditions imposed on actual automorphic forms. -/
abbrev AutomorphicInvariantCondition (n : ℕ) :=
  Subrepresentation (continuousRightAction K n)

variable (r : ℕ) (S : AutomorphicInvariantCondition K (r + 1))

local instance restrictedSphericalFormsRestrictedAddCommGroup :
    AddCommGroup (RestrictedAutomorphicForms K (r + 1) S) := Submodule.addCommGroup _

/-- Smoothness for invariant restrictions, with the same canonical local topology. -/
theorem restrictedAutomorphicLocalRightAction_isSmooth_canonical :
    Langlands.IsSmooth (restrictedAutomorphicLocalRightAction K (r + 1) S v) := by
  change @Langlands.IsSmooth ℂ (FiniteLocalGL K (r + 1) v)
    (RestrictedAutomorphicForms K (r + 1) S) _ _ _ _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
    (restrictedAutomorphicLocalRightAction K (r + 1) S v)
  rw [← FiniteAdelicGL.localGL_topology_eq K v (r + 1)]
  exact restrictedAutomorphicLocalRightAction_isSmooth K (r + 1) S v

/-- The spherical vectors in any actual invariant restriction of forms. -/
abbrev RestrictedAutomorphicSphericalVectors :=
  Langlands.fixedVectors (restrictedAutomorphicLocalRightAction K (r + 1) S v)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

/-- The type of canonical spherical corner actions on the restricted form space. -/
abbrev RestrictedAutomorphicSphericalHeckeAction :=
  Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField v) r →ₐ[ℂ]
    Module.End ℂ (RestrictedAutomorphicSphericalVectors K v r S)

/-- The same canonical spherical corner acts on the restricted fixed space. -/
def restrictedAutomorphicSphericalHeckeAction :
    RestrictedAutomorphicSphericalHeckeAction K v r S :=
  @Hecke.cornerAction (FiniteLocalGL K (r + 1) v) _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1)) _ _ _ _ _
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r) _
    (restrictedAutomorphicLocalRightAction K (r + 1) S v)
    (restrictedAutomorphicLocalRightAction_isSmooth_canonical K v r S)
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)

/-- Standard diagonal double-coset operators on restricted spherical forms. -/
def restrictedAutomorphicStandardHeckeOperator (i : Fin (r + 2)) :
    Module.End ℂ (RestrictedAutomorphicSphericalVectors K v r S) :=
  restrictedAutomorphicSphericalHeckeAction K v r S
    (Unramified.standardHeckeElement (CompletionPadic.padicField v) r i)

@[simp] theorem restrictedAutomorphicStandardHeckeOperator_zero :
    restrictedAutomorphicStandardHeckeOperator K v r S 0 = 1 := by
  simp only [restrictedAutomorphicStandardHeckeOperator,
    Unramified.standardHeckeElement_zero, map_one]

/-- Inclusion into the whole form space restricts to spherical vectors. -/
def restrictedAutomorphicSphericalInclusion :
    RestrictedAutomorphicSphericalVectors K v r S →ₗ[ℂ] AutomorphicSphericalVectors K v r :=
  Langlands.fixedVectorsMap (restrictedAutomorphicLocalInclusion K (r + 1) S v)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

theorem restrictedAutomorphicSphericalInclusion_injective :
    Function.Injective (restrictedAutomorphicSphericalInclusion K v r S) :=
  Langlands.fixedVectorsMap_injective _
    (restrictedAutomorphicLocalInclusion_injective K (r + 1) S v) _

/-- Restricting the ambient automorphic space commutes with the whole spherical corner. -/
theorem restrictedAutomorphicSphericalInclusion_heckeAction
    (h : Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField v) r)
    (f : RestrictedAutomorphicSphericalVectors K v r S) :
    restrictedAutomorphicSphericalInclusion K v r S
        (restrictedAutomorphicSphericalHeckeAction K v r S h f) =
      automorphicSphericalHeckeAction K v r h
        (restrictedAutomorphicSphericalInclusion K v r S f) := by
  exact @Hecke.cornerAction_intertwiner (FiniteLocalGL K (r + 1) v) _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1))
    _ _ _ _ _ _ _ _ (Unramified.sphericalHaar (CompletionPadic.padicField v) r) _
    (restrictedAutomorphicLocalRightAction K (r + 1) S v)
    (restrictedAutomorphicLocalRightAction_isSmooth_canonical K v r S)
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)
    (automorphicLocalRightAction K (r + 1) v)
    (automorphicLocalRightAction_isSmooth_canonical K v (r + 1))
    (restrictedAutomorphicLocalInclusion K (r + 1) S v) h f

theorem restrictedAutomorphicSphericalInclusion_standardHeckeOperator
    (i : Fin (r + 2)) (f : RestrictedAutomorphicSphericalVectors K v r S) :
    restrictedAutomorphicSphericalInclusion K v r S
        (restrictedAutomorphicStandardHeckeOperator K v r S i f) =
      automorphicStandardHeckeOperator K v r i
        (restrictedAutomorphicSphericalInclusion K v r S f) :=
  restrictedAutomorphicSphericalInclusion_heckeAction K v r S _ f

/-- The nonzero simultaneous eigenform relation on an invariant restriction. -/
def IsRestrictedSphericalHeckeEigenform (s : Unramified.Eigenvalues (r + 1))
    (f : RestrictedAutomorphicSphericalVectors K v r S) : Prop :=
  f ≠ 0 ∧ ∀ i : Fin (r + 2), restrictedAutomorphicStandardHeckeOperator K v r S i f =
    Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i • f

/-- The restricted and ambient eigenform relations agree under the actual inclusion. -/
theorem isRestrictedSphericalHeckeEigenform_iff (s : Unramified.Eigenvalues (r + 1))
    (f : RestrictedAutomorphicSphericalVectors K v r S) :
    IsRestrictedSphericalHeckeEigenform K v r S s f ↔
      IsSphericalHeckeEigenform K v r s
        (restrictedAutomorphicSphericalInclusion K v r S f) := by
  let T := restrictedAutomorphicSphericalInclusion K v r S
  have hinj := restrictedAutomorphicSphericalInclusion_injective K v r S
  constructor
  · rintro ⟨hne, hf⟩
    refine ⟨fun h => hne (hinj (h.trans T.map_zero.symm)), ?_⟩
    intro i
    exact (restrictedAutomorphicSphericalInclusion_standardHeckeOperator K v r S i f).symm.trans
      ((congrArg T (hf i)).trans (T.map_smul _ f))
  · rintro ⟨hne, hf⟩
    refine ⟨fun h => hne ((congrArg T h).trans T.map_zero), ?_⟩
    intro i
    apply hinj
    exact (restrictedAutomorphicSphericalInclusion_standardHeckeOperator K v r S i f).trans
      ((hf i).trans (T.map_smul _ f).symm)

end Langlands.Automorphic

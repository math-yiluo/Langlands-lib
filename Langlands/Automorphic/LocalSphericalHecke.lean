import Langlands.Automorphic.PadicLocalCategory
import Langlands.Automorphic.SphericalHecke
import Langlands.Representation.Smooth.FixedVectors.LawsProof

/-! # Spherical Hecke actions on actual automorphic local components -/

noncomputable section
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global
open MeasureTheory

private theorem exists_nonzero_submodule_vector {V : Type uV}
    [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) (hW : W ≠ ⊥) :
    ∃ x : W, x ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := W.ne_bot_iff.mp hW
  exact ⟨⟨x, hx⟩, fun h => hne (congrArg Subtype.val h)⟩

variable {F : Type uF} [Field F] [NumberField F]

local instance localSphericalRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localSphericalContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localSphericalSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localSphericalFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localSphericalSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ} (S : LocalRealization F (r + 1) v)

local instance localSphericalTopology (n : ℕ) : TopologicalSpace (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology n
local instance localSphericalTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup n
local instance localSphericalT2 (n : ℕ) : T2Space (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space n
local instance localSphericalMeasurable (n : ℕ) : MeasurableSpace (FiniteLocalGL F n v) :=
  borel _
local instance localSphericalBorel (n : ℕ) : BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩
local instance localSphericalHaar :
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r).IsHaarMeasure :=
  Unramified.sphericalHaar_isHaar (CompletionPadic.padicField v) r

/-- The spherical fixed submodule of the actual local form space. -/
abbrev SphericalVectors :=
  Langlands.fixedVectors S.representation
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

/-- The type of the canonical corner action on the actual local fixed space. -/
abbrev SphericalHeckeAction :=
  Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField v) r →ₐ[ℂ]
    Module.End ℂ S.SphericalVectors

/-- The genuine mass-one spherical corner acts on every actual local component. -/
def sphericalHeckeAction : S.SphericalHeckeAction :=
  @Hecke.cornerAction (FiniteLocalGL F (r + 1) v) _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1)) _ _ _ _ _
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r) _
    S.representation S.isSmooth_canonical
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)

/-- The standard diagonal double-coset operator on this fixed submodule. -/
def standardHeckeOperator (i : Fin (r + 2)) : Module.End ℂ S.SphericalVectors :=
  S.sphericalHeckeAction
    (Unramified.standardHeckeElement (CompletionPadic.padicField v) r i)

@[simp] theorem standardHeckeOperator_zero : S.standardHeckeOperator 0 = 1 := by
  simp only [standardHeckeOperator, Unramified.standardHeckeElement_zero, map_one]

/-- Inclusion of actual local fixed vectors into ambient spherical automorphic forms. -/
def sphericalInclusion : S.SphericalVectors →ₗ[ℂ] AutomorphicSphericalVectors F v r :=
  Langlands.fixedVectorsMap S.inclusion
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

theorem sphericalInclusion_injective : Function.Injective S.sphericalInclusion :=
  Langlands.fixedVectorsMap_injective _ S.inclusion_injective _

/-- The inclusion commutes with every element of the actual spherical corner. -/
theorem sphericalInclusion_heckeAction
    (h : Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField v) r)
    (f : S.SphericalVectors) :
    S.sphericalInclusion (S.sphericalHeckeAction h f) =
      automorphicSphericalHeckeAction F v r h (S.sphericalInclusion f) := by
  exact @Hecke.cornerAction_intertwiner (FiniteLocalGL F (r + 1) v) _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1))
    _ _ _ _ _ _ _ _ (Unramified.sphericalHaar (CompletionPadic.padicField v) r) _
    S.representation S.isSmooth_canonical
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)
    (automorphicLocalRightAction F (r + 1) v)
    (automorphicLocalRightAction_isSmooth_canonical F v (r + 1))
    S.inclusion h f

theorem sphericalInclusion_standardHeckeOperator
    (i : Fin (r + 2)) (f : S.SphericalVectors) :
    S.sphericalInclusion (S.standardHeckeOperator i f) =
      automorphicStandardHeckeOperator F v r i (S.sphericalInclusion f) :=
  S.sphericalInclusion_heckeAction _ f

/-- The local operator is exactly the operator on its canonical p-adic object. -/
theorem standardHeckeOperator_padicObject (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (i : Fin (r + 2)) :
    Unramified.standardHeckeOperator (CompletionPadic.padicField v) (S.padicObject hI hA) i =
      S.standardHeckeOperator i := rfl

/-- A nonzero simultaneous eigenvector in this actual local component. -/
def IsSphericalHeckeEigenvector (s : Unramified.Eigenvalues (r + 1))
    (f : S.SphericalVectors) : Prop :=
  f ≠ 0 ∧ ∀ i : Fin (r + 2), S.standardHeckeOperator i f =
    Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i • f

/-- The local and ambient eigenvector relations agree under the actual inclusion. -/
theorem isSphericalHeckeEigenvector_iff (s : Unramified.Eigenvalues (r + 1))
    (f : S.SphericalVectors) :
    S.IsSphericalHeckeEigenvector s f ↔
      IsSphericalHeckeEigenform F v r s (S.sphericalInclusion f) := by
  let T := S.sphericalInclusion
  have hinj := S.sphericalInclusion_injective
  constructor
  · rintro ⟨hne, hf⟩
    refine ⟨fun h => hne (hinj (h.trans T.map_zero.symm)), ?_⟩
    intro i
    exact (S.sphericalInclusion_standardHeckeOperator i f).symm.trans
      ((congrArg T (hf i)).trans (T.map_smul _ f))
  · rintro ⟨hne, hf⟩
    refine ⟨fun h => hne ((congrArg T h).trans T.map_zero), ?_⟩
    intro i
    apply hinj
    exact (S.sphericalInclusion_standardHeckeOperator i f).trans
      ((hf i).trans (T.map_smul _ f).symm)

/-- A conditional spectrum relation on the whole actual spherical fixed space. -/
def HasSphericalHeckeSpectrum (s : Unramified.Eigenvalues (r + 1)) : Prop :=
  S.SphericalVectors ≠ ⊥ ∧ ∀ (i : Fin (r + 2)) (f : S.SphericalVectors),
    S.standardHeckeOperator i f =
      Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i • f

/-- The actual fixed-space relation is precisely the existing correspondence-class relation. -/
theorem hasSphericalHeckeSpectrumClass_iff (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (s : Unramified.Eigenvalues (r + 1)) :
    Unramified.HasSphericalHeckeSpectrumClass (CompletionPadic.padicField v)
      (S.padicClass hI hA) s ↔ S.HasSphericalHeckeSpectrum s := by
  exact Unramified.hasSphericalHeckeSpectrumClass_classOf _ (S.padicObject hI hA) s

/-- The same whole-space scalar condition can be checked inside ambient forms. -/
theorem hasSphericalHeckeSpectrum_iff_ambient (s : Unramified.Eigenvalues (r + 1)) :
    S.HasSphericalHeckeSpectrum s ↔
      S.SphericalVectors ≠ ⊥ ∧ ∀ (i : Fin (r + 2)) (f : S.SphericalVectors),
        automorphicStandardHeckeOperator F v r i (S.sphericalInclusion f) =
          Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i •
            S.sphericalInclusion f := by
  constructor
  · rintro ⟨hne, hs⟩
    refine ⟨hne, fun i f => ?_⟩
    exact (S.sphericalInclusion_standardHeckeOperator i f).symm.trans
      ((congrArg S.sphericalInclusion (hs i f)).trans (S.sphericalInclusion.map_smul _ f))
  · rintro ⟨hne, hs⟩
    refine ⟨hne, fun i f => ?_⟩
    apply S.sphericalInclusion_injective
    exact (S.sphericalInclusion_standardHeckeOperator i f).trans
      ((hs i f).trans (S.sphericalInclusion.map_smul _ f).symm)

/-- A supplied spectrum produces a genuine nonzero ambient eigenform in this component. -/
theorem exists_sphericalHeckeEigenform_of_spectrum
    (s : Unramified.Eigenvalues (r + 1)) (hs : S.HasSphericalHeckeSpectrum s) :
    ∃ f : S.SphericalVectors, IsSphericalHeckeEigenform F v r s (S.sphericalInclusion f) :=
  (exists_nonzero_submodule_vector S.SphericalVectors hs.1).imp
    (fun f hf => (S.isSphericalHeckeEigenvector_iff s f).mp ⟨hf, fun i => hs.2 i f⟩)

end LocalRealization
end Langlands.Automorphic

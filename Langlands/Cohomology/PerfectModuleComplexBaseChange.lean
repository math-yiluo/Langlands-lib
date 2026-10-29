import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Scalar extension and finite homology of perfect module complexes -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Ordinary extension of scalars preserves finite generation. -/
lemma finite_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R)
    [Module.Finite R M] : Module.Finite S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Finite S (TensorProduct R S M)
  infer_instance

/-- Ordinary extension of scalars preserves projective modules. -/
lemma projective_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R)
    [Module.Projective R M] :
    Module.Projective S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Projective S (TensorProduct R S M)
  infer_instance

/-- Ordinary scalar extension preserves both term bounds. -/
lemma bounded_baseChange (φ : R →+* S)
    {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) :
    ∃ a b : ℤ, ((baseChange φ).obj K).IsStrictlyGE a ∧
      ((baseChange φ).obj K).IsStrictlyLE b := by
  obtain ⟨a, b, ha, hb⟩ := hK
  let := ha
  let := hb
  refine ⟨a, b, ?_, ?_⟩ <;>
    dsimp only [baseChange] <;> infer_instance

/-- Ordinary scalar extension preserves strictly perfect complexes. -/
lemma isStrictlyPerfect_baseChange (φ : R →+* S)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K) :
    IsStrictlyPerfect ((baseChange φ).obj K) := by
  refine ⟨bounded_baseChange φ hK.1, fun i ↦ ?_⟩
  let := (hK.2 i).1
  let := (hK.2 i).2
  exact ⟨finite_extendScalars φ (K.X i), projective_extendScalars φ (K.X i)⟩

/-- Scalar extension by a composite is naturally isomorphic to two successive
ordinary scalar extensions. -/
def baseChangeCompIso (φ : R →+* S) (ψ : S →+* T) :
    baseChange (ψ.comp φ) ≅ baseChange φ ⋙ baseChange ψ :=
  (Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp φ ψ).symm (ComplexShape.up ℤ)).symm

/-- A finite term of a complex over a field has finite-dimensional homology. -/
lemma finite_homology_of_finite_term {F : Type u} [Field F]
    (K : CochainComplex (ModuleCat.{u} F) ℤ) (i : ℤ)
    [Module.Finite F (K.X i)] : Module.Finite F (K.homology i) := by
  let : Module.Finite F (K.cycles i) :=
    FiniteDimensional.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The homology of a field scalar extension of a strictly perfect complex is
finite dimensional in every degree. -/
lemma finite_homology_baseChange {F : Type u} [Field F] (φ : R →+* F)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K) (i : ℤ) :
    Module.Finite F (((baseChange φ).obj K).homology i) := by
  let := (isStrictlyPerfect_baseChange φ hK).2 i |>.1
  exact finite_homology_of_finite_term _ i

end Langlands.Cohomology.ModuleComplex

import Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.GKIsotypicIrreducibility
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.PlaceComponentIsotypy
import Langlands.Representation.Archimedean.ComplexStandardCompactMultiplicityOne
import Langlands.Representation.Archimedean.RealStandardCompactMultiplicityOne

/-! # Irreducibility of archimedean standard-module components -/

noncomputable section

universe u

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem intertwines_complexifiedLie
    {L U W : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (α : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ U) (β : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ W)
    (A : U →ₗ[ℂ] W) (h : ∀ X f, A (α (1 ⊗ₜ X) f) = β (1 ⊗ₜ X) (A f))
    (Y : ℂ ⊗[ℝ] L) (f : U) : A (α Y f) = β Y (A f) := by
  induction Y using TensorProduct.inductionOn with
  | tmul c X =>
    have he : c ⊗ₜ[ℝ] X = c • (1 ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he]
    simp only [map_smul, LinearMap.smul_apply, h]
  | add Y Z hY hZ => simp only [map_add, LinearMap.add_apply, hY, hZ]

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance cuspidalArchimedeanIrreducibleRationalInvariantFunctions : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalArchimedeanIrreducibleContinuousRationalFunctions : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalArchimedeanIrreducibleFiniteSmoothRationalFunctions : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalArchimedeanIrreducibleAutomorphicForms : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalArchimedeanIrreducibleStableAutomorphicFunctions : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cuspidalArchimedeanIrreducibleOperatorSpace (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- A compact multiplicity-one witness implies irreducibility of a real place parameter. -/
theorem isIrreducibleRealStandard_of_compactWitness
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock)
    (hp : T.realization.HasRealPlaceParameter v ds)
    (x : realStandardKFinite (r + 1) ds) (hx : x ≠ 0)
    (hline : ∀ E : Module.End ℂ (realStandardKFinite (r + 1) ds),
      (∀ k y, E (realStandardRep (r + 1) ds k y) = realStandardRep (r + 1) ds k (E y)) →
      ∃ c : ℂ, E x = c • x) :
    IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds) := by
  obtain ⟨W, hW, _⟩ := T.exists_realPlaceComponent v
  obtain ⟨_, A, hA, hK, hL⟩ := hp
  exact isIrreducibleGKModule_of_injective_of_isotypic _ _ _ _ _ _
    (PlaceComponent.isIrreducibleGKModule_restrict hW) (T.isRealPlaceIsotypic_restrict v hW)
    A ⟨OperatorRealization.realPlaceParameter_compact hK,
      intertwines_complexifiedLie _ _ A (OperatorRealization.realPlaceParameter_lie hL)⟩
    hA x hx hline

/-- A compact multiplicity-one witness implies irreducibility of a complex place parameter. -/
theorem isIrreducibleComplexStandard_of_compactWitness
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (ds : List ComplexCharacterData)
    (hp : T.realization.HasComplexPlaceParameter v ds)
    (x : complexStandardKFinite (r + 1) ds) (hx : x ≠ 0)
    (hline : ∀ E : Module.End ℂ (complexStandardKFinite (r + 1) ds),
      (∀ k y, E (complexStandardRep (r + 1) ds k y) = complexStandardRep (r + 1) ds k (E y)) →
      ∃ c : ℂ, E x = c • x) :
    IsIrreducibleGKModule (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds) := by
  obtain ⟨W, hW, _⟩ := T.exists_complexPlaceComponent v
  obtain ⟨_, A, hA, hK, hL⟩ := hp
  exact isIrreducibleGKModule_of_injective_of_isotypic _ _ _ _ _ _
    (PlaceComponent.isIrreducibleGKModule_restrict hW) (T.isComplexPlaceIsotypic_restrict v hW)
    A ⟨OperatorRealization.complexPlaceParameter_compact hK,
      intertwines_complexifiedLie _ _ A (OperatorRealization.complexPlaceParameter_lie hL)⟩
    hA x hx hline

/-- The standard module of a real place parameter of a cuspidal realization is irreducible. -/
theorem isIrreducibleRealStandard
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock)
    (hp : T.realization.HasRealPlaceParameter v ds) :
    IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds) := by
  obtain ⟨x, hx, hline⟩ :=
    RealStandardCompactMultiplicityOne.realStandardExistsCompactScalarVector (r + 1) ds hp.1
  exact T.isIrreducibleRealStandard_of_compactWitness v ds hp x hx hline

/-- The standard module of a complex place parameter of a cuspidal realization is irreducible. -/
theorem isIrreducibleComplexStandard
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (ds : List ComplexCharacterData)
    (hp : T.realization.HasComplexPlaceParameter v ds) :
    IsIrreducibleGKModule (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds) := by
  obtain ⟨x, hx, hline⟩ := complexStandardExistsCompactScalarVector (r + 1) ds hp.1
  exact T.isIrreducibleComplexStandard_of_compactWitness v ds hp x hx hline

end CuspidalOperatorRealization

/-- The standard modules supplied by the real and complex place parameters are irreducible. -/
theorem cuspidalArchimedeanStandardIrreducible :
    CuspidalArchimedeanStandardIrreducibleStatement.{u} := by
  intro F _ _ _ r T
  exact ⟨T.isIrreducibleRealStandard, T.isIrreducibleComplexStandard⟩

end Langlands.Automorphic

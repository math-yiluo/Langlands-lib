import Langlands.GroupScheme.Reductive.SemisimpleRepresentationFieldExtensionStatement
import Langlands.GroupScheme.MatrixRepresentation.AbsoluteIrreducibilityFieldExtension
import Langlands.GroupScheme.MatrixRepresentation.SemisimpleFieldExtensionDescent
import Langlands.GroupScheme.MatrixRepresentation.AffineIntertwinerAlgebra
import Langlands.GroupScheme.MatrixRepresentation.ScalarExtendedOperatorAlgebra
import Langlands.Algebra.SemisimpleScalarExtensionStatement

/-! # Reduction of Milne 4.19 to semisimple algebra scalar extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.SemisimpleFieldExtensionReduction

open AffineCoefficientAlgebra AffineSemisimpleModules ScalarExtendedOperatorAlgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

local instance operatorRing : Ring (operatorAlgebra ρ) := inferInstance
local instance extendedOperatorRing :
    Ring (operatorAlgebra
      (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := inferInstance
local instance imageRing : Ring (extendedAlgebra (K := K) ρ) := inferInstance

/-- The scalar-extended operator image acts on every actual stable subspace. -/
def extendedSubmodule (W : Submodule K (n → K))
    (hW : (ρ.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W) :
    Submodule (extendedAlgebra (K := K) ρ) (n → K) where
  __ := W.toAddSubmonoid
  smul_mem' a _ hv :=
    (ScalarExtendedOperatorAlgebra.isStableSubspace_iff ρ W).mp hW a.property _ hv

/-- Every submodule for the extended operator image is an actual stable subspace. -/
theorem stable_restrictScalars
    (W : Submodule (extendedAlgebra (K := K) ρ) (n → K)) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace
      (W.restrictScalars K) := by
  apply (ScalarExtendedOperatorAlgebra.isStableSubspace_iff ρ _).mpr
  intro f hf v hv
  exact W.smul_mem (⟨f, hf⟩ : extendedAlgebra (K := K) ρ) hv

/-- A semisimple extended operator image gives semisimplicity of the actual
extended representation. -/
theorem isSemisimpleModule_of_image
    [IsSemisimpleRing (extendedAlgebra (K := K) ρ)] :
    IsSemisimpleModule
      (operatorAlgebra
        (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))))) (n → K) := by
  classical
  let ρK := ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  refine { exists_isCompl := fun S => ?_ }
  let W := S.restrictScalars K
  have hW : ρK.IsStableSubspace W := AffineCoefficientAlgebra.stable_restrictScalars ρK S
  let U := extendedSubmodule ρ W hW
  obtain ⟨T, hUT⟩ := exists_isCompl U
  let T' := operatorSubmodule ρK (T.restrictScalars K) (stable_restrictScalars ρ T)
  refine ⟨T', (Submodule.isCompl_restrictScalars_iff K).mp ?_⟩
  have hc : IsCompl (U.restrictScalars K) (T.restrictScalars K) :=
    (Submodule.isCompl_restrictScalars_iff K).mpr hUT
  exact hc

/-- The generic finite-dimensional semisimple-algebra scalar-extension theorem
implies the exact semisimplicity-ascent assertion of Milne 4.19(c). -/
theorem isSemisimple_baseChange_of_algebra
    (hAlg : Langlands.Algebra.SemisimpleScalarExtensionStatement.{u,u,u})
    (hρ : sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤)
    (hcond : Algebra.IsSeparable k K ∨
      (IsSemisimpleRing (Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C}) ∧
        Algebra.Etale k
          (Subalgebra.center k (Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C})))) :
    sSup {W : Submodule K (n → K) |
      (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W ∧
      W ≠ ⊥ ∧ ∀ U : Submodule K (n → K),
        (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace U →
        U ≤ W → U = ⊥ ∨ U = W} = ⊤ := by
  let : IsSemisimpleModule (operatorAlgebra ρ) (n → k) :=
    (AffineSemisimpleModules.isSemisimpleModule_iff ρ).mpr hρ
  let : IsSemisimpleRing (operatorAlgebra ρ) :=
    Langlands.Algebra.SemisimpleOperatorAlgebra.isSemisimpleRing (operatorAlgebra ρ)
  have hc : Algebra.IsSeparable k K ∨
      Algebra.Etale k (Subalgebra.center k (operatorAlgebra ρ)) := by
    rcases hcond with h | ⟨_, h⟩
    · exact Or.inl h
    · let := h
      exact Or.inr (AffineIntertwinerAlgebra.etale_operatorCenter ρ)
  let : IsSemisimpleRing (K ⊗[k] operatorAlgebra ρ) :=
    hAlg k K (operatorAlgebra ρ) inferInstance hc
  let : IsSemisimpleRing (extendedAlgebra (K := K) ρ) :=
    RingHom.isSemisimpleRing_of_surjective
      (scalarExtensionHom (K := K) ρ).rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  apply (AffineSemisimpleModules.isSemisimpleModule_iff _).mp
  exact isSemisimpleModule_of_image ρ

end Langlands.GroupScheme.MatrixRepresentation.SemisimpleFieldExtensionReduction

namespace Langlands.GroupScheme

/-- The unchanged full Milne 4.19 target follows from one generic algebra
scalar-extension prerequisite. -/
theorem semisimpleRepresentationFieldExtension_of_algebra
    (hAlg : Langlands.Algebra.SemisimpleScalarExtensionStatement.{u,u,u}) :
    SemisimpleRepresentationFieldExtensionStatement.{u} := by
  intro k K _ _ _ G _ _ n _ _ ρ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact fun h => h.of_baseChange
  · exact MatrixRepresentation.FieldExtensionDescent.isSemisimple_of_baseChange ρ
  · exact fun h hscalar => h.baseChange_of_scalar_intertwiners hscalar
  · exact MatrixRepresentation.SemisimpleFieldExtensionReduction.isSemisimple_baseChange_of_algebra
      ρ hAlg

end Langlands.GroupScheme

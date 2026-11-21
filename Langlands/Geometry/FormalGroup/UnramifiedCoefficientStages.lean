import Langlands.CommutativeAlgebra.DirectedEtaleCoefficientLift
import Langlands.Geometry.FormalGroup.CompletedUnramifiedCoefficients
import Langlands.Galois.Local.SeparableUnramifiedProof
import Langlands.GroupScheme.Descent.FiniteUnramifiedIntegers
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Finite étale stages of the actual unramified coefficient algebra -/

noncomputable section

set_option maxHeartbeats 1200000

universe u

open IsLocalRing ValuativeRel

namespace Langlands.LocalGalois.Separable

open Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance unramifiedStagesNormedField : NontriviallyNormedField F := localNormedField F
local instance unramifiedStagesUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance unramifiedStagesComplete : CompleteSpace F := localNormedField_complete F

/-- The integers of a finite unramified intermediate field form a finite étale
algebra over the norm-defined base integers. -/
theorem finiteUnramifiedSpectralIntegers_etale (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] (hE : E ≤ inertiaFixedField F) :
    Algebra.Etale (baseIntegers F) (extensionIntegers F E) := by
  obtain ⟨hmap, hsep⟩ := (finiteUnramifiedMaximality F E).mp hE
  let : Algebra.IsSeparable (ResidueField (baseIntegers F))
      (ResidueField (extensionIntegers F E)) := hsep
  let : Algebra.FormallyUnramified (baseIntegers F) (extensionIntegers F E) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  let : Algebra.FinitePresentation (baseIntegers F) (extensionIntegers F E) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- The algebra of actual unramified integers of a finite stage is formally étale
for the original base integer ring. -/
theorem integerCoefficients_formallyEtale (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] (hE : E ≤ inertiaFixedField F) :
    Algebra.FormallyEtale 𝒪[F] (integerCoefficients F E) := by
  let e : baseIntegers F ≃+* 𝒪[F] := RingEquiv.subringCongr (localNormedField_integer F)
  let : Algebra (baseIntegers F) 𝒪[F] := e.toRingHom.toAlgebra
  let : Algebra (baseIntegers F) (integerCoefficients F E) :=
    Algebra.compHom _ e.toRingHom
  let : IsScalarTower (baseIntegers F) 𝒪[F] (integerCoefficients F E) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let e' : integerCoefficients F E ≃ₐ[baseIntegers F] extensionIntegers F E :=
    { __ := integerCoefficientsEquiv F E hE
      commutes' := fun _ => Subtype.ext (Subtype.ext rfl) }
  let : Algebra.Etale (baseIntegers F) (extensionIntegers F E) :=
    finiteUnramifiedSpectralIntegers_etale F E hE
  let : Algebra.FormallyEtale (baseIntegers F) (integerCoefficients F E) :=
    Algebra.FormallyEtale.of_equiv e'.symm
  let : Algebra.FormallyUnramified (baseIntegers F) 𝒪[F] :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId _ _) e.surjective
  exact Algebra.FormallyEtale.of_restrictScalars (R := baseIntegers F)

/-- The finite intermediate fields of the actual maximal unramified extension. -/
abbrev FiniteUnramifiedField :=
  {E : IntermediateField F (SeparableClosure F) // FiniteDimensional F E ∧ E ≤ inertiaFixedField F}

/-- The actual finite coefficient stages as subalgebras of the uncompleted integers. -/
def unramifiedIntegerStages (i : FiniteUnramifiedField F) :
    Subalgebra 𝒪[F] (fixedFieldIntegers F) :=
  integerCoefficients F i.1

theorem unramifiedIntegerStages_directed : Directed (· ≤ ·) (unramifiedIntegerStages F) := by
  intro i j
  let : FiniteDimensional F i.1 := i.2.1
  let : FiniteDimensional F j.1 := j.2.1
  refine ⟨⟨i.1 ⊔ j.1, inferInstance, sup_le i.2.2 j.2.2⟩, ?_, ?_⟩
  · exact fun _ h => (show i.1 ≤ i.1 ⊔ j.1 from le_sup_left) h
  · exact fun _ h => (show j.1 ≤ i.1 ⊔ j.1 from le_sup_right) h

theorem exists_unramifiedIntegerStage (x : fixedFieldIntegers F) :
    ∃ i : FiniteUnramifiedField F, x ∈ unramifiedIntegerStages F i := by
  classical
  obtain ⟨E, hE, -, hLE, -, hmem⟩ := (separableUnramified F).2 {x.1}
  exact ⟨⟨E, hE, hLE⟩, hmem x.1 (Finset.mem_singleton_self _)⟩

/-- The actual uncompleted unramified integers are formally étale over the
base integers by their directed finite étale exhaustion. -/
instance fixedFieldIntegers_formallyEtale : Algebra.FormallyEtale 𝒪[F] (fixedFieldIntegers F) :=
  Langlands.CommutativeAlgebra.formallyEtale_of_directed_subalgebras
    (unramifiedIntegerStages F) (unramifiedIntegerStages_directed F)
    (exists_unramifiedIntegerStage F) (fun i =>
      letI : FiniteDimensional F i.1 := i.2.1
      integerCoefficients_formallyEtale F i.1 i.2.2)

end Langlands.LocalGalois.Separable

import Langlands.Geometry.FormalGroup.DeligneCompletedAction
import Langlands.Geometry.FormalGroup.DrinfeldCompletedCoefficientFunctor
import Langlands.Geometry.FormalGroup.DrinfeldFramedAction
import Langlands.Geometry.FormalGroup.RelativeFrobeniusIsogenyProof
import Langlands.Geometry.FormalGroup.SpecialFrameFrobenius

/-! # Drinfeld's equivariant comparison over the actual completed unramified base -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 80000

universe u

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory IsLocalRing ValuativeRel CentralSimple DeligneFormalSpace ModuleLaw
open Langlands.LocalGalois.Separable

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] {ι : L →ₐ[K] D} {π : 𝒪[K]}

local notation "κ" => ResidueField (fixedFieldIntegers K)
local notation "degD" => reducedDegree K D

/-- Drinfeld's framed functor is the completed unramified base change of the actual
Deligne point functor. The comparison recovers the actual completed coefficient
map and intertwines the literal transformation of every framed representative. -/
def DrinfeldDeligneCompletedComparisonStatement
    (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
    (c : Φ.val.MatrixCoordinates) : Prop :=
  letI : NeZero degD := ⟨(reducedDegree_pos K D).ne'⟩
  let hπ := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp Φ.property.1
  HasDrinfeldCyclicRelations ι π →
    ∃ e : DrinfeldFramedAtlas.comparisonClassFunctor (R := 𝒪[K]) Φ ≅
        nilpDeligneCompletedCoefficientFunctor (d := degD) Φ.property.1,
      (∀ (B : Nilp.{u, u} 𝒪[K] π) (x : DrinfeldFramedAtlas.ComparisonClass Φ B),
        (e.hom.app B x).2 = (B.completedUnramifiedResidueMapEquiv hπ).symm x.residueMap) ∧
      ∀ (B : Nilp.{u, u} 𝒪[K] π) (X : DrinfeldFramedAtlas Φ B)
        (g : GL (Fin degD) K × Dˣ),
        e.hom.app B (DrinfeldFramedAtlas.comparisonClassOf
          (X.act g p hcard (fun j => SpecialModule.relativeFrobeniusQuasiIsogeny Φ p (f * j))
            (fun j => relativeFrobeniusIsogeny Φ.val.formalModule p (f * j)) c)) =
          (nilpDeligneCompletedResidueDivisionAction Φ.property.1 g).hom.app B
            (e.hom.app B (DrinfeldFramedAtlas.comparisonClassOf X))

end Langlands.FormalGroup.LocalDivision

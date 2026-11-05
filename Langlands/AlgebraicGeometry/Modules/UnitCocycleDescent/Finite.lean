import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Affine
import Langlands.Algebra.UnitCocycleLocalUnitsProof

/-! # Common local frames for finite families of unit cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Scheme.UnitCocycleDescent

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  {I : Type u} [Finite I]
  (c : I → ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ)

/-- A single neighbourhood with an invertible cocycle section in every coordinate. -/
structure FiniteLocalFrame (y : Y) where
  openSet : Y.Opens
  mem_openSet : y ∈ openSet
  unitSection : I → Γ(X, p ⁻¹ᵁ openSet)ˣ
  isCocycleSection : ∀ i, IsCocycleSection p (c i) openSet (unitSection i).val

/-- Finitely many natural unit cocycles admit unit sections on one common neighbourhood. -/
theorem nonempty_finiteLocalFrame [IsAffineHom p] [Flat p] [Surjective p]
    (hnat : ∀ i, IsNatural p (c i)) (hmul : ∀ i, IsMultiplicative p (c i)) (y : Y) :
    Nonempty (FiniteLocalFrame p c y) := by
  classical
  choose W σ hy hσ hu using fun i =>
    exists_unit_cocycleSection Langlands.Algebra.unitCocycleLocalUnits (hnat i) (hmul i) y
  let V : Y.Opens := ⨅ i, W i
  have hV (i : I) : V ≤ W i := iInf_le _ i
  refine ⟨{
    openSet := V
    mem_openSet := ?_
    unitSection := fun i =>
      Units.map (X.presheaf.map (homOfLE (p.preimage_mono (hV i))).op).hom.toMonoidHom
        (hu i).unit
    isCocycleSection := ?_ }⟩
  · change y ∈ (↑(⨅ i, W i) : Set Y)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hy
  · intro i
    change IsCocycleSection p (c i) V
      (X.presheaf.map (homOfLE (p.preimage_mono (hV i))).op (hu i).unit.val)
    rw [IsUnit.unit_spec]
    exact (hσ i).map (hV i)

/-- Choose a common local frame from the established affine faithfully flat descent theorem. -/
def finiteLocalFrame [IsAffineHom p] [Flat p] [Surjective p]
    (hnat : ∀ i, IsNatural p (c i)) (hmul : ∀ i, IsMultiplicative p (c i)) (y : Y) :
    FiniteLocalFrame p c y :=
  Classical.choice (nonempty_finiteLocalFrame p c hnat hmul y)

end Langlands.Scheme.UnitCocycleDescent

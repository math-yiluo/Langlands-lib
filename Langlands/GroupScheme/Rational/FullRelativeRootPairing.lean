import Langlands.GroupScheme.Rational.InvariantRootPartition
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Mathlib.LinearAlgebra.RootSystem.Basic

/-! # Full actual-root pairings on the rational root span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G)
  {J W : Type*} [AddCommGroup W] [Module ℚ W]
  (P : RootPairing J ℚ (relativeRootSpan i) W)
  (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots i)

include hP

/-- The full actual-root image spans the actual rational root span. -/
theorem rootSpan_eq_top_of_full_relativeRoot_image : P.rootSpan ℚ = ⊤ := by
  apply (Submodule.span_val_image_eq_iff (relativeRootSpan i) (Set.range P.root)).mp
  rw [hP]
  rfl

/-- A finite enumeration of the indices of a full actual-root pairing.
Finiteness comes from the actual split-torus Lie weights. -/
@[instance_reducible]
def fullRelativeRootImageFintype [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) : Fintype J := by
  have hf : (Subtype.val '' Set.range P.root).Finite := by
    rw [hP]
    exact (hS.finite_relativeRoots i).image toRat
  have hr : (Set.range P.root).Finite :=
    (Set.finite_image_iff Subtype.val_injective.injOn).mp hf
  let : Finite J := (Set.finite_range_iff P.root.injective).mp hr
  exact Fintype.ofFinite J

/-- A full actual-root pairing on the rational root span is a root system. -/
theorem isRootSystem_of_full_relativeRoot_image [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) : P.IsRootSystem := by
  let := fullRelativeRootImageFintype i P hP hS
  have hspan := rootSpan_eq_top_of_full_relativeRoot_image i P hP
  exact ⟨hspan, (P.rootSpan_eq_top_iff).mp hspan⟩

/-- Almost-simplicity makes every full actual-root pairing irreducible.
No root-system, crystallographic, reducedness or coroot-evaluation premise
is needed. -/
theorem isIrreducible_fullRelativeRootPairing
    (hG : IsAlmostSimple G) (hi : IsMaximalSplitTorus i)
    (hne : (relativeRoots i).Nonempty) : P.IsIrreducible := by
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let := isRootSystem_of_full_relativeRoot_image i P hP hi.1.1
  exact isIrreducible_of_full_relativeRoot_image i P hP hG hi hne

end Langlands.GroupScheme

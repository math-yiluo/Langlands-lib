import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Mathlib.Algebra.Module.Submodule.Union

/-! # Existence of generic integral cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Finitely many nonzero characters of a split torus admit simultaneous
nonzero integral cocharacter pairings. -/
theorem IsSplitTorus.exists_pairings_ne_zero (hT : IsSplitTorus T.toGrp)
    (s : Set (characterLattice T)) (hs : s.Finite)
    (hs0 : ∀ α ∈ s, α ≠ 0) :
    ∃ ν : cocharacterLattice T, ∀ α ∈ s, latticePairing T α ν ≠ 0 := by
  classical
  let := hs.fintype
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ)
    (fun α : s => toRat (α : characterLattice T)) (fun α h => by
      apply hs0 α α.property
      apply hT.character_toRat_injective
      simpa using h)
  obtain ⟨d, hd, ν, hν⟩ := hT.exists_positive_multiple_pairing f
  refine ⟨ν, fun α hα hzero => ?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have h := hν α
  rw [hzero, Int.cast_zero] at h
  exact (mul_ne_zero hd0 (hf ⟨α, hα⟩)) h.symm

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Generic integral cocharacters exist for every split-torus homomorphism
into an affine group scheme locally of finite type over a field. -/
theorem IsSplitTorus.exists_genericCocharacter (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) : ∃ ν : cocharacterLattice T, IsGenericCocharacter i ν :=
  hT.exists_pairings_ne_zero (relativeRoots i) (hT.finite_relativeRoots i)
    (fun _ hα => hα.1)

/-- A choice of a generic integral cocharacter, using the actual relative roots. -/
def genericCocharacterOfIsSplitTorus (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) :
    cocharacterLattice T :=
  (hT.exists_genericCocharacter i).choose

theorem genericCocharacterOfIsSplitTorus_spec (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) :
    IsGenericCocharacter i (genericCocharacterOfIsSplitTorus hT i) :=
  (hT.exists_genericCocharacter i).choose_spec

end Langlands.GroupScheme

namespace Langlands.GroupScheme

/-- The generic-minimality statement suffices for existence of an actual
minimal rational parabolic containing any given maximal split torus. -/
theorem IsMaximalSplitTorus.exists_minimalParabolic_containing
    (hminimal : GenericMinimalParabolicStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsMinimalParabolicSubgroup j ∧ ∃ f : T.toGrp ⟶ P, f ≫ j = i := by
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  exact exists_minimalParabolic_containing_of_genericMinimal hminimal k G hG T i hi ν hν

end Langlands.GroupScheme

import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The character lattice of a split torus is finitely generated as an
integer module. -/
theorem IsSplitTorus.finite_characterLattice (hT : IsSplitTorus T.toGrp) :
    Module.Finite ℤ (characterLattice T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have := hI
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let eL : characterLattice T ≃+ (I → ℤ) :=
    (characterLattice.congr eC).trans (splitTorus.characterLatticeEquiv k I)
  exact Module.Finite.equiv eL.toIntLinearEquiv.symm

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Existence of a standard cocharacter for every face separates all the
simple roots by integer linear functionals and makes them linearly independent. -/
theorem linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists
    (hexists : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      ∃ zeta, IsStandardCocharacter i ν J zeta) :
    LinearIndependent ℤ (fun α : simpleRelativeRoots i ν => (α : characterLattice T)) := by
  classical
  refine linearIndependent_iff'.mpr ?_
  intro s c hrel α hα
  obtain ⟨zeta, hzeta⟩ :=
    hexists (simpleRelativeRoots i ν \ {(α : characterLattice T)}) Set.sdiff_subset
  have hself : 0 < latticePairing T α zeta :=
    hzeta.2.2 α α.property (by simp)
  have hoff (β : simpleRelativeRoots i ν) (hβα : β ≠ α) :
      latticePairing T β zeta = 0 := by
    apply hzeta.2.1 β
    refine ⟨β.property, ?_⟩
    intro heq
    exact hβα (Subtype.ext (Set.mem_singleton_iff.mp heq))
  have h := congrArg ((latticePairing T).flip zeta) hrel
  simp only [map_sum, map_smul, map_zero, LinearMap.flip_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single α] at h
  · exact (mul_eq_zero.mp h).resolve_right (ne_of_gt hself)
  · intro β _ hβα
    rw [hoff β hβα, mul_zero]
  · exact fun hnot => False.elim (hnot hα)

/-- Splitness and existence of standard cocharacters for every face already
imply finiteness of the actual simple-root set, without a root-system premise. -/
theorem finite_simpleRelativeRoots_of_standardCocharacter_exists
    (hT : IsSplitTorus T.toGrp)
    (hexists : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      ∃ zeta, IsStandardCocharacter i ν J zeta) :
    (simpleRelativeRoots i ν).Finite := by
  have := hT.finite_characterLattice
  exact (linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists i ν hexists).setFinite

/-- A finite enumeration of the actual simple roots, obtained from splitness
and existence of standard cocharacters for all faces. -/
@[instance_reducible]
def simpleRelativeRootsFintypeOfStandardCocharacterExists
    (hT : IsSplitTorus T.toGrp)
    (hexists : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      ∃ zeta, IsStandardCocharacter i ν J zeta) :
    Fintype (simpleRelativeRoots i ν) :=
  (finite_simpleRelativeRoots_of_standardCocharacter_exists i ν hT hexists).fintype

end Langlands.GroupScheme

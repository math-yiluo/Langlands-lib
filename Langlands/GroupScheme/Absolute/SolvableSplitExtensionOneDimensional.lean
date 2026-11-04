import Langlands.GroupScheme.Absolute.TriangularSplitExtension
import Langlands.GroupScheme.Unipotent.AlgebraicallyClosedSplitReduction
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Unipotent.OneDimensional.Proof

/-! # Split torus extensions from the one-dimensional unipotent classification -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Milne 2017, Theorem 16.26(a), conditional on the one-dimensional classification.** The
splitness of the smooth connected unipotent kernel over the algebraically closed field comes
from `Unipotent.algebraicallyClosedSplit_of_oneDimensional` with the proved closed-subgroup
input `unipotentClosedSubgroup`. -/
theorem solvableSplitExtension_of_oneDimensional
    (hone : PerfectFieldOneDimensionalUnipotentStatement.{u}) :
    SolvableSplitExtensionStatement.{u} := by
  intro k _ _ H _ _ _ hH U D i q hi hUs hUc hU hn hq hD
  obtain ⟨N, j, hj⟩ := solvableTriangularEmbeddingStatement k H hH
  have : IsAffineHom U.X.hom := HomogeneousQuotient.affine_subgroup_of_closed H U i hi
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : Smooth U.X.hom := hUs
  have hUsplit := Unipotent.algebraicallyClosedSplit_of_oneDimensional unipotentClosedSubgroup
    hone k U hUc hU
  obtain ⟨s, hs⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors H U i
    splitUnipotentAffineTorsorStatement hi hUsplit D q hq
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1 := by
    intro T g
    rw [← hq.2.2.2, mem_range_kernelι_iff]
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact IsSplitTorus.exists_section_of_triangular i q j hD hU hn hker s hs

end Langlands.GroupScheme

import Langlands.Cohomology.HyperextDegeneration.Statement
import Langlands.Cohomology.HyperextGradedVanishing
import Langlands.Cohomology.HyperextEdgeMapSurjective

/-!
# Proof of the degeneration of the hyperext spectral sequence

This module proves `Langlands.Cohomology.HyperextDegenerationStatement`: if the cohomology of
`K` vanishes above some degree `b` and `Ext^i(H^k K, W)` vanishes for every `k` and every
`i > 0`, then the edge map `Hom(K, W⟦n⟧) → Hom(H^{-n} K, W)` is bijective for every `n`.

The two halves are published results with exactly the hypotheses of the statement:
injectivity is `HyperextAbutment.edgeMap_injective_of_ext` (the kernel `F^1` of the edge map
vanishes) and surjectivity is `HyperextAbutment.edgeMap_surjective_of_ext`.
-/

open CategoryTheory

namespace Langlands.Cohomology

universe w w' v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

/-- The hyperext edge map `Hom(K, W⟦n⟧) → Hom(H^{-n} K, W)` is bijective when `K` has
bounded-above cohomology and `Ext^i(H^k K, W)` vanishes for every `k` and every `i > 0`. -/
theorem hyperextDegenerationStatement_proof : HyperextDegenerationStatement.{w, w'} C :=
  fun K b hK W hW n =>
    ⟨HyperextAbutment.edgeMap_injective_of_ext K b hK W hW n,
      HyperextAbutment.edgeMap_surjective_of_ext K b hK W hW n⟩

end Langlands.Cohomology

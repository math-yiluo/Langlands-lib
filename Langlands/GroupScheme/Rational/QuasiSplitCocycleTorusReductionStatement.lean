import Langlands.GroupScheme.Rational.CocycleTorusReduction
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Torus reduction for cocycles of quasi-split semisimple groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every finite-Galois cocycle of a quasi-split semisimple field group admits an
actual torus reduction after finite-Galois refinement of its cover. -/
def QuasiSplitCocycleTorusReductionStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSemisimple G → IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L]
      (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      Nonempty ξ.TorusReduction

end Langlands.GroupScheme

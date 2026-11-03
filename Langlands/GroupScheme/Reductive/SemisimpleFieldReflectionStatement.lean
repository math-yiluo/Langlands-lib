import Langlands.GroupScheme.Reductive.Semisimple

/-! # Reflection of semisimplicity under arbitrary field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Semisimplicity of an actual group scheme is reflected by base change along every
field extension `k → K`, with no additional hypothesis on the original group. -/
def SemisimpleFieldReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) →
      IsSemisimple G

end Langlands.GroupScheme

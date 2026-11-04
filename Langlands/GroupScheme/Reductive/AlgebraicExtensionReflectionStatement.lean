import Langlands.GroupScheme.Reductive.Semisimple

/-! # Reflection of connected reductivity and semisimplicity along algebraic extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Connected reductivity of an actual group scheme is reflected by base change along every
algebraic extension of fields `k → K`, with no additional hypothesis on the original group. -/
def ConnectedReductiveAlgebraicExtensionReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) →
      IsConnectedReductive G

/-- Semisimplicity of an actual group scheme is reflected by base change along every
algebraic extension of fields `k → K`, with no additional hypothesis on the original group. -/
def SemisimpleAlgebraicExtensionReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) →
      IsSemisimple G

/-- Both reflections along algebraic field extensions, packaged as one proposition. -/
def AlgebraicExtensionReflectionStatement : Prop :=
  ConnectedReductiveAlgebraicExtensionReflectionStatement.{u} ∧
    SemisimpleAlgebraicExtensionReflectionStatement.{u}

end Langlands.GroupScheme

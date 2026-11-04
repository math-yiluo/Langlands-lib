import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Ascent of connected reductivity and semisimplicity along algebraic field extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Base change along an arbitrary algebraic field extension `k → K` preserves the existing
connected-reductivity predicate, with its geometric unipotent radical, of an actual group
scheme over `Spec k`. -/
def ConnectedReductiveAlgebraicExtensionAscentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      IsConnectedReductive
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

/-- Base change along an arbitrary algebraic field extension `k → K` preserves the existing
semisimplicity predicate, including finiteness of the full scheme-theoretic centre, of an
actual group scheme over `Spec k`. -/
def SemisimpleAlgebraicExtensionAscentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
      IsSemisimple
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

/-- The package of both algebraic-extension ascent statements at universe `u`. -/
def AlgebraicExtensionAscentStatement : Prop :=
  ConnectedReductiveAlgebraicExtensionAscentStatement.{u} ∧
    SemisimpleAlgebraicExtensionAscentStatement.{u}

end Langlands.GroupScheme

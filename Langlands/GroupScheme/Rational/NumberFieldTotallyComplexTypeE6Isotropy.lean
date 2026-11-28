import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Isotropy of type E6 over totally complex number fields -/

universe u

open AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- A simply connected absolutely almost-simple E6 group over a totally
complex number field has positive split rank. -/
def NumberFieldTotallyComplexTypeE6IsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
      IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) → ¬ IsAnisotropic G

end Langlands.GroupScheme

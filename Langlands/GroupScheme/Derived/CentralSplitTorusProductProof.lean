import Langlands.GroupScheme.Derived.CentralSplitTorusProductStatement
import Langlands.GroupScheme.Derived.CentralSplitTorusProductReduction
import Langlands.GroupScheme.Derived.CentralSplitTorusProductSurjectivity
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Proof of the derived and central split-torus product isogeny -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Multiplication of the supplied derived maximal split torus and central split component is
a central isogeny onto the ambient maximal split torus, over every field. -/
theorem derivedCentralSplitTorusProduct : DerivedCentralSplitTorusProductStatement.{u} := by
  intro k _ G D d hG hd S S_D A i j e a c hi hj he hcomp ha hc
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  exact (derivedCentralSplitTorusProductReduction k G D d hG hd S S_D A i j e a c hi hj he
    hcomp ha hc).mp
    (splitProduct_surjective_of_relative_reflections hG hd hi hj hcomp ha hc
      (fun _ hα => (relativeRootSystem k G hG S i hi).exists_isRelativeReflection hα))

end Langlands.GroupScheme

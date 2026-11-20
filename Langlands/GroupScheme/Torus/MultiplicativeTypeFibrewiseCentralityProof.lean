import Langlands.GroupScheme.Torus.MultiplicativeTypeFibrewiseCentralityStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralityPropagation
import Langlands.GroupScheme.Torus.NormalMultiplicativeTypeCentrality

/-! # Fibrewise centrality for homomorphisms from groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- SGA 3, IX, Théorème 5.6 and Corollaire 5.5. -/
theorem multiplicativeTypeFibrewiseCentrality :
    MultiplicativeTypeFibrewiseCentralityStatement.{u} := by
  have hRig := multiplicativeTypeCentralRigidity.{u}
  intro S
  constructor
  · intro H G hH hlfp hqc hqs i
    let := hlfp
    let := hqc
    let := hqs
    exact ⟨MultiplicativeTypeCentralityPropagation.exists_open_isCentral hRig hH i,
      MultiplicativeTypeFibrewiseCentralityReduction.isCentral_of_fibres_of_centralRigidity
        hRig hH i⟩
  · intro K H h _ hconn hi hH hn
    exact RelativeMultiplicativeType.isCentral_of_isNormal_of_connectedFibres
      h hconn hi hH hn

end Langlands.GroupScheme

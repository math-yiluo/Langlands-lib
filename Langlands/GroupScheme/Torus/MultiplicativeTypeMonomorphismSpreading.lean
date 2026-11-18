import Langlands.GroupScheme.FiberwiseMonomorphism
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonomorphismSpreadingReduction
import Langlands.GroupScheme.Torus.FiniteSubgroupSpreadingReduction

/-! # Assembly of multiplicative-type monomorphism spreading -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- An actual monomorphism neighbourhood, with source geometry supplied by
relative multiplicative type and finite-subgroup spreading kept explicit. -/
def multiplicativeTypeMonomorphismNeighbourhoodOfFiniteSubgroupSpreading
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom)
    (f : H ⟶ G) [IsSeparated G.X.hom] (s : S)
    (hs : Mono ((baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    MonomorphismNeighbourhood f s := by
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : LocallyOfFinitePresentation H.X.hom := hH.locallyOfFinitePresentation
  exact monomorphismNeighbourhoodOfFiniteSubgroupSpreading hspread hH hbase f s hs

/-- The exact global assertion, for a target that need not be separated. -/
theorem multiplicativeType_mono_of_residueField_fibres
    (f : H ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom)
    (hf : ∀ s : S, Mono ((baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    Mono f.hom.hom := by
  have : LocallyOfFinitePresentation H.X.hom := hH.locallyOfFinitePresentation
  apply mono_of_residueField_fibres f _ hf
  exact hbase.imp_right fun h => by
    let := h
    infer_instance

/-- Finite-subgroup spreading gives the unchanged full monomorphism-spreading
statement, using the independent residue-field criterion for its global clause. -/
theorem multiplicativeType_monomorphismSpreading_of_finiteSubgroupSpreading
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u}) :
    MultiplicativeTypeMonomorphismSpreadingStatement.{u} := by
  intro S H G hH hbase f
  constructor
  · intro hsep s hs
    let := hsep
    let N := multiplicativeTypeMonomorphismNeighbourhoodOfFiniteSubgroupSpreading
      hspread hH hbase f s hs
    exact ⟨N.openSet, N.mem, N.monomorphism⟩
  · exact multiplicativeType_mono_of_residueField_fibres f hH hbase

/-- The quasi-finite commutative uniform-exponent theorem suffices for the
unchanged full monomorphism-spreading statement. -/
theorem multiplicativeType_monomorphismSpreading_of_uniformExponent
    (hexp : QuasiFiniteCommutativeUniformExponentStatement.{u}) :
    MultiplicativeTypeMonomorphismSpreadingStatement.{u} :=
  multiplicativeType_monomorphismSpreading_of_finiteSubgroupSpreading
    (FiniteSubgroupSpreadingReduction.finiteSubgroupSpreading_of_uniformExponent hexp)

end Langlands.GroupScheme

import Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityStatement
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.CompactCoefficient.CentralCharacterProjectivity
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.RationalCentralQuotient
import Langlands.Representation.Plancherel.RenardLatticeComparisonStatement
import Langlands.Global.AdelicRestrictionSplitCentreCanonical

/-! # Renard VI.3.6 from the structural statements

The proposition `RepresentedSupercuspidalCentralProjectivityStatement` follows
from the generic theorem
`CentralCharacterProjectivity.projective_and_injective_of_compactRestriction`,
applied to the open normal common norm kernel `⁰G`, once two structural facts
are available:

* compact coefficients of a represented supercuspidal on `⁰G`
  (`compactRestriction_of_isSupercuspidal`, Renard VI.2.1), which keeps four
  structural existence statements as premises;
* finiteness of `G(F) ⧸ ⁰G A_G(F)` (`Plancherel.finite_rationalCentralQuotient`),
  which needs the finite-index conjunct of `SplitComponentLatticeStatement`.

All five structural statements are explicit premises here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.BruhatTits.SpecialCompact

/-- `⁰G ⊔ Z(G)` has finite index in `G(F)` for a connected reductive `G`, given
the split-component lattice statement. -/
theorem finiteIndex_rationalCommonNormKernel_sup_center
    (hLattice : Plancherel.RenardCartan.SplitComponentLatticeStatement.{u})
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    (Plancherel.rationalCommonNormKernel G ⊔ Subgroup.center (rationalPoints G)).FiniteIndex := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨A, i, hi⟩ := GroupScheme.exists_isSplitComponent G
  have := Plancherel.finite_rationalCentralQuotient i hi.1.2 (hLattice k G hG A i hi).1
  have : (Plancherel.rationalCommonNormKernel G ⊔ (rationalPoints.map i).range).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le (sup_le_sup_left hi.1.range_le_center _)

/-- Renard VI.3.6 for every represented group, from the four structural
statements behind VI.2.1 and the split-component lattice statement. -/
theorem representedSupercuspidalCentralProjectivity_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hLattice : Plancherel.RenardCartan.SplitComponentLatticeStatement.{u}) :
    RepresentedSupercuspidalCentralProjectivityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ χ τ hχ hirr hsc
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have hc : HasCompactNormKernelRestriction τ :=
    compactRestriction_of_isSupercuspidal hPD hStandard hRoot hJoint hG τ hsc
  let H := Plancherel.rationalCommonNormOpenSubgroup G
  have : H.toSubgroup.Normal := Plancherel.rationalCommonNormKernel_normal G
  have : (H.toSubgroup ⊔ Subgroup.center (rationalPoints G)).FiniteIndex :=
    finiteIndex_rationalCommonNormKernel_sup_center hLattice G hG
  exact CentralCharacterProjectivity.projective_and_injective_of_compactRestriction
    H χ τ hχ hirr hc

end Langlands.Aubert.General.RepresentedParabolic

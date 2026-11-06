import Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationStatement
import Langlands.Representation.CuspidalSupport.CompactRestrictionRealization
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # Reduction of Renard VI.3.6 to the two structural inputs

For a connected reductive group, the realization of an irreducible actual
subquotient of an admissible representation as a subrepresentation and a
quotient follows from the generic theorem
`Langlands.CuspidalSupport.constituent_of_compactRestriction`, applied to the
open normal common norm kernel `⁰G`, once
`⁰G ⊔ Z(G)` has finite index and the restriction of the subquotient to `⁰G` has
compactly supported smooth-dual coefficients.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.3.6 for every represented group, under two explicit premises:
`⁰G ⊔ Z(G)` has finite index, and the restriction of the subquotient to the
common norm kernel `⁰G` has compactly supported smooth-dual coefficients. -/
def RepresentedSupercuspidalSubquotientRealizationReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      (Plancherel.rationalCommonNormKernel G ⊔
        Subgroup.center (rationalPoints G)).FiniteIndex →
      π.IsAdmissible →
      τ.IsIrreducible →
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) τ).representation →
      SmoothRep.IsSubquotient τ π →
      SmoothRep.IsSubrepresentation τ π ∧ SmoothRep.IsQuotient τ π

/-- The reduction holds: the generic realization theorem applies to the open
normal common norm kernel. -/
theorem representedSupercuspidalSubquotientRealizationReduction :
    RepresentedSupercuspidalSubquotientRealizationReductionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π τ hfin hπ hτ hc hτπ
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  let H := Plancherel.rationalCommonNormOpenSubgroup G
  have : H.toSubgroup.Normal := Plancherel.rationalCommonNormKernel_normal G
  have : (H.toSubgroup ⊔ Subgroup.center (rationalPoints G)).FiniteIndex := hfin
  exact CuspidalSupport.constituent_of_compactRestriction H π τ hπ hτ hc hτπ

end Langlands.Aubert.General.RepresentedParabolic

import Langlands.GroupScheme.Reductive.TorusLiftingOpenConstruction

/-! # Actual good opens and conditional openness from structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

local instance conditionalOpen_smooth_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : U ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance conditionalOpen_affine_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : U ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- Construct the initial torus after a finite Galois residue extension,
then lift it and descend an actual good open to the original point. -/
def identityComponentReductiveNeighbourhood_of_lifting_and_fieldStatements
    (hLift : RelativeSplitTorusLiftingStatement.{u})
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : S) (hs : s ∈ identityComponentReductiveLocus G) :
    IdentityComponentReductiveOpenNeighbourhood G s :=
  Classical.choice <| by
    obtain ⟨K, hK, aK, hfin, hgal, T, i, hT, hmax⟩ :=
      exists_finiteGalois_hasSplitMaximalTorus torusFiniteGaloisSplitting
        maximalTorusBaseChange ((baseChange (S.fromSpecResidueField s)).obj G)
    let : Field K := hK
    let : Algebra (S.residueField s) K := aK
    let : FiniteDimensional (S.residueField s) K := hfin
    let : IsGalois (S.residueField s) K := hgal
    let d := Langlands.AlgebraicGeometry.etaleResidueExtension S s K
    let : Etale d.projection := d.etale
    let q := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))
    let ε := baseChangeCompIso (S.fromSpecResidueField s) q G
    let j : T.toGrp ⟶ (baseChange d.extensionPoint).obj G := i ≫ ε.inv
    have hm : IsMaximalTorus (T := T) j := hmax.comp_iso ε.symm
    let TC := (CommGroupScheme.baseChange d.inverseResiduePoint).obj T
    let jC := d.torusFibreInclusion G T.toGrp j
    have hTC : IsSplitTorus TC.toGrp := d.torusFibre_isSplit T.toGrp hT
    have hmC : IsMaximalTorus (T := TC) jC :=
      d.torusFibreInclusion_isMaximal G T j hm
    have hsU : d.point ∈ identityComponentReductiveLocus ((baseChange d.projection).obj G) := by
      rw [identityComponentReductiveLocus_baseChange]
      change d.projection d.point ∈ identityComponentReductiveLocus G
      rwa [d.point_over]
    let good := identityComponentReductiveNeighbourhood_of_splitMaximalResidueTorus
      hLift hCentralizer hReflection hReduced hLine ((baseChange d.projection).obj G)
      d.point hsU TC hTC jC hmC
    have result := identityComponentReductiveOpenNeighbourhood_of_openMap G
      d.projection d.projection.isOpenMap d.point good.neighbourhood.isOpen
      good.mem_neighbourhood good.subset_locus
    exact ⟨by simpa only [d.point_over] using result⟩

/-- Actual pointwise good opens give the exact arbitrary-base openness
conclusion, with the five structural statements retained as inputs. -/
theorem identityComponentReductiveLocusOpen_of_lifting_and_fieldStatements
    (hLift : RelativeSplitTorusLiftingStatement.{u})
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u}) :
    IdentityComponentReductiveLocusOpenStatement.{u} := by
  intro S G _ _
  apply isOpen_iff_forall_mem_open.mpr
  intro s hs
  let good := identityComponentReductiveNeighbourhood_of_lifting_and_fieldStatements
    hLift hCentralizer hReflection hReduced hLine G s hs
  exact ⟨good.neighbourhood, good.subset_locus,
    good.neighbourhood.isOpen, good.mem_neighbourhood⟩

end Langlands.GroupScheme

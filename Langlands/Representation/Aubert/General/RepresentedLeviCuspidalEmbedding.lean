import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.Representation.Aubert.General.RepresentedDynamicTransport
import Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingCarrier

/-! # Cuspidal embeddings for the actual points of a represented dynamic Levi -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RepresentedLeviCuspidalEmbedding

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G L : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine L.X.left]
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (j : L ⟶ G) (hj : (Dynamic.centralizer χ).IsRepresentedBy j)
    (hc : IsClosedSubgroup j)

local instance ambientPointTopology :
    TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

local instance sourcePointTopology :
    TopologicalSpace (RationalPoint F L.X) := rationalPointTopology F L.X

variable [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)]

omit [NonarchimedeanGroup (RationalPoint F G.X)] in
include χ j hj hc in
private theorem sourceLocallyCompactSpace :
    LocallyCompactSpace (RationalPoint F L.X) := by
  let : T2Space F := BruhatTits.localField_t2Space F
  exact RepresentedDynamicTransport.representative_locallyCompactSpace
    F (Dynamic.centralizer χ) j hj hc
    (isClosed_rationalPoint_subgroup F (Dynamic.centralizer χ) j hj hc)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [LocallyCompactSpace (RationalPoint F G.X)] in
include χ j hj hc in
private theorem sourceNonarchimedeanGroup :
    NonarchimedeanGroup (RationalPoint F L.X) :=
  RepresentedDynamicTransport.representative_nonarchimedeanGroup
    F (Dynamic.centralizer χ) j hj hc

local instance sourceT2Space : T2Space (RationalPoint F L.X) := by
  let : T2Space F := BruhatTits.localField_t2Space F
  exact rationalPoint_t2Space F L

/-- An irreducible representation of the literal outer Levi embeds into source
standard cuspidal induction, transported back along the represented-point map.
The source's connected reductivity and point-group topology are derived. -/
def cuspidalEmbedding
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ L)
    (hi : IsMaximalSplitTorus i) :
    let hL := dynamicCentralizerReductive F G hG χ L j hc hj
    haveI := hL.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : LocallyCompactSpace (RationalPoint F L.X) :=
      sourceLocallyCompactSpace F χ j hj hc
    letI : NonarchimedeanGroup (RationalPoint F L.X) :=
      sourceNonarchimedeanGroup F χ j hj hc
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (_hEndpoints : StandardParabolicEndpointsStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (RationalPointFamily.unipotent i ν I :
        Set (RationalPoint F L.X)))
      (hM : ∀ I, IsClosed (RationalPointFamily.levi i ν I :
        Set (RationalPoint F L.X)))
      (_hCompact : ∀ I, CompactSpace
        (Induction.LeftQuotient (RationalPointFamily.parabolic i ν I)))
      (_hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups
        (RationalPointFamily.unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hL hi hν
      let hInner := RationalPointFamily.isSemidirectDecomposition_in_levi
        i ν hInter hL hi hν
      let Ind : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν),
          SmoothRep.{0, u, max (u + 1) uV} ℂ (RationalPointFamily.levi i ν I) ⥤
            SmoothRep.{0, u, max (u + 1) uV} ℂ (RationalPoint F L.X) :=
        fun I => normalizedInductionFunctor.{u, max (u + 1) uV} (h I) (hU I)
      let e := RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer χ) j hj hc
      ∀ (A : SmoothRep.{0, u, uV} ℂ
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))),
        A.IsIrreducible →
        Σ I : Finset (RationalPointFamily.SimpleRoot i ν),
          Σ σ : SmoothRep.{0, u, max (u + 1) uV} ℂ (RationalPointFamily.levi i ν I),
            {f : A.representation.IntertwiningMap
                (SmoothRep.pullback.{u, u, max (u + 1) uV} e.symm
                  ((Ind I).obj σ)).representation //
              σ.IsIrreducible ∧
              IsLeviCuspidal (RationalPointFamily.parabolic i ν)
                (RationalPointFamily.levi i ν) (RationalPointFamily.unipotent i ν)
                hU I (hM I) (hInner I) σ ∧
              Function.Injective f} := by
  let hL := dynamicCentralizerReductive F G hG χ L j hc hj
  haveI := hL.isAffineHom
  haveI := hi.isSplitSubtorus.mono
  letI : LocallyCompactSpace (RationalPoint F L.X) :=
    sourceLocallyCompactSpace F χ j hj hc
  letI : NonarchimedeanGroup (RationalPoint F L.X) :=
    sourceNonarchimedeanGroup F χ j hj hc
  dsimp only
  intro ν hν hStandard hInter hEndpoints hRoots hU hM hCompact hUc A hA
  let e := RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer χ) j hj hc
  let A' := SmoothRep.pullback e A
  have hA' : A'.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation e).mpr hA
  obtain ⟨I, σ, f, hσ, hcusp, hf⟩ :=
    RationalPointFamily.cuspidalEmbeddingIndependentCarrier
      F L hL T i hi ν hν hStandard hInter hEndpoints hRoots hU hM hCompact hUc A' hA'
  let f' : A.representation.IntertwiningMap
      (SmoothRep.pullback e.symm
        ((normalizedInductionFunctor
          (RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hL hi hν I) (hU I)).obj σ)).representation :=
    { toLinearMap := f.toLinearMap
      isIntertwining' z := by
        have hz := f.isIntertwining' (e.symm z)
        change f.toLinearMap ∘ₗ A.representation (e (e.symm z)) = _ at hz
        change f.toLinearMap ∘ₗ A.representation z =
          ((normalizedInductionFunctor
            (RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hL hi hν I) (hU I)).obj σ).representation
                (e.symm z) ∘ₗ f.toLinearMap
        simpa only [e.apply_symm_apply] using hz }
  exact ⟨I, σ, ⟨f', hσ, hcusp, hf⟩⟩

end Langlands.Aubert.General.RepresentedLeviCuspidalEmbedding

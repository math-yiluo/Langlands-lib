import Langlands.Representation.Jacquet.StandardGeneralizedJacquetLift
import Langlands.Representation.Jacquet.NormalizedFixedVectorBridge
import Langlands.Representation.Smooth.FixedVectors.RationalLeviJacquetDetectionStatement
import Langlands.Representation.Smooth.FixedVectors.RationalNormKernelDetectionProof
import Langlands.Representation.Smooth.FixedVectors.GroupEquivalenceGenerationProof
import Langlands.Representation.Tensor.SmoothSubquotients

/-! # Normalized standard Jacquet lifting and rational-Levi detection -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Jacquet

section StandardLift

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}

/-- A chosen lift of actual normalized standard Jacquet fixed vectors to
ambient fixed vectors, conditional on the generalized Jacquet lemma. -/
def standardNormalizedFixedJacquetLift
    (hJacquet : GeneralizedJacquetLemmaStatement.{uF, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hN : IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)))
    (hM : IsClosed (standardLeviPoints i ν J : Set (rationalPoints G)))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    fixedVectors
        ((Aubert.General.normalizedJacquetFunctor
          (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) hN
          (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)).obj V).representation
        (K.toSubgroup.comap (standardLeviPoints i ν J).subtype) →ₗ[ℂ]
      fixedVectors V.representation K.toSubgroup :=
  (standardFixedJacquetLift i ν hJacquet hG hi hν hzeta hA K hK hBasis
    V.representation V.isSmooth).comp
      (NormalizedJacquetBridge.normalizedFixedVectorsEquiv
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) hN
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
        hM K hK V).toLinearMap

/-- The chosen normalized lift maps back to the exact unnormalized comparison
of the original normalized fixed vector. -/
theorem fixedJacquetMap_comp_standardNormalizedFixedJacquetLift
    (hJacquet : GeneralizedJacquetLemmaStatement.{uF, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hN : IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)))
    (hM : IsClosed (standardLeviPoints i ν J : Set (rationalPoints G)))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    (fixedJacquetMap V.representation
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) K.toSubgroup).comp
      (standardNormalizedFixedJacquetLift i ν hJacquet hG hi hν hzeta hA hN hM K hK
        hBasis V) =
      (NormalizedJacquetBridge.normalizedFixedVectorsEquiv
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) hN
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
        hM K hK V).toLinearMap := by
  dsimp only [standardNormalizedFixedJacquetLift]
  rw [← LinearMap.comp_assoc, fixedJacquetMap_comp_standardFixedJacquetLift]
  ext x
  rfl

end StandardLift

end Langlands.Jacquet

namespace Langlands

/-- Rational-Levi fixed-vector detection from explicit fixed-Jacquet-map
surjectivity, with no finite fixed dimension or admissibility premise. -/
theorem rationalLeviJacquetFixedVectorDetection_of_surjective
    (hfinite : CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν)),
        let L := Standard.leviScheme i ν (rootSet i ν I)
        ∀ (hL : IsConnectedReductive L),
          haveI := hL.isAffineHom
          haveI : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
          letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
          letI : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
          ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
            [T2Space (rationalPoints G)]
            [LocallyCompactSpace (rationalPoints L)] [NonarchimedeanGroup (rationalPoints L)]
            [T2Space (rationalPoints L)]
            (hN : IsClosed (unipotent i ν I : Set (rationalPoints G)))
            (hMN : levi i ν I ≤ Subgroup.normalizer (unipotent i ν I))
            (_hM : IsClosed (levi i ν I : Set (rationalPoints G)))
            (_hcompact : ∀ s : Finset (unipotent i ν I),
              ∃ J : OpenSubgroup (unipotent i ν I),
                IsCompact (J : Set (unipotent i ν I)) ∧ ∀ n ∈ s, n ∈ J)
            (K : OpenSubgroup (rationalPoints G)) (K0 : Subgroup (rationalPoints G))
            (_hK : IsCompact (K : Set (rationalPoints G)))
            (_hK0 : K0 ≤ Subgroup.normalizer K.toSubgroup)
            (_hfactor : ∀ x : rationalPoints G, ∃ m ∈ levi i ν I, ∃ n ∈ unipotent i ν I,
              ∃ k ∈ K0, x = m * n * k)
            (A D : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
            (_hsurj : Function.Surjective (Jacquet.fixedJacquetMap D.representation
              (unipotent i ν I) (levi i ν I) hMN K.toSubgroup))
            (_hgen : ∀ S : Subrepresentation A.representation,
              fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
            (_hDA : SmoothRep.IsSubquotient D A)
            (E : SmoothRep.{0, uF, uV} ℂ (levi i ν I))
            (_hEirr : E.IsIrreducible)
            (_hEsub : SmoothRep.IsSubquotient E
              ((Aubert.General.normalizedJacquetFunctor
                (unipotent i ν I) (levi i ν I) hN hMN).obj D))
            (_hcoeff : HasCompactSmoothDualCoefficients
              (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel L)
                (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) E)).representation),
            ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0 := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro T i ν I L hL
  let := hL.isAffineHom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  intro _ _ _ _ _ _ hN hMN hM hcompact K K0 hK hK0 hfactor
    A D hsurj hgen hDA E hEirr hEsub hcoeff
  let M := levi i ν I
  let J := Aubert.General.normalizedJacquetFunctor (unipotent i ν I) M hN hMN
  let JA := J.obj A
  let JD := J.obj D
  let e := leviRationalPointHomeomorph i ν I
  let KL : Subgroup (rationalPoints L) :=
    (K.toSubgroup.comap M.subtype).comap e.toMonoidHom
  have hKback : KL.comap e.symm.toMonoidHom = K.toSubgroup.comap M.subtype := by
    ext m
    change e (e.symm m) ∈ K.toSubgroup.comap M.subtype ↔
      m ∈ K.toSubgroup.comap M.subtype
    rw [e.apply_symm_apply]
  obtain ⟨hgenJA, hJDA, hlift⟩ := NormalizedJacquetBridge.bridge_of_surjective
    (unipotent i ν I) M hN hMN hM hcompact K K0 hK hK0 hfactor
    A D hsurj hgen hDA
  have hEJA : SmoothRep.IsSubquotient E JA :=
    smoothSubquotientTransitivity ℂ M JA JD E hEsub hJDA
  have hgenL : ∀ S : Subrepresentation (SmoothRep.pullback e JA).representation,
      fixedVectors (SmoothRep.pullback e JA).representation KL ≤ S.toSubmodule →
        S = ⊤ := by
    apply (fixedVectors_generate_comp_mulEquiv_iff JA.representation e.toMulEquiv KL).mpr
    change ∀ S : Subrepresentation JA.representation,
      fixedVectors JA.representation (KL.comap e.symm.toMonoidHom) ≤ S.toSubmodule → S = ⊤
    rwa [hKback]
  have hELirr : (SmoothRep.pullback e E).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff E.representation e).mpr hEirr
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hKL : IsCompact (KL : Set (rationalPoints L)) :=
    e.toHomeomorph.isCompact_preimage.mpr hKM
  obtain ⟨v, hv, hv0⟩ := rationalNormKernelFixedVectorDetection hfinite F L hL
    (SmoothRep.pullback e JA) (SmoothRep.pullback e E) KL hKL hELirr hgenL hcoeff
    (hEJA.pullback e)
  have hvM : v ∈ fixedVectors E.representation (K.toSubgroup.comap M.subtype) := by
    change v ∈ fixedVectors (E.representation.comp e.toMonoidHom) KL at hv
    rw [fixedVectors_comp_mulEquiv E.representation e.toMulEquiv KL] at hv
    change v ∈ fixedVectors E.representation (KL.comap e.symm.toMonoidHom) at hv
    rwa [hKback] at hv
  exact hlift (NormalizedJacquetBridge.nonzero_fixed_subquotient KM hKM hEsub
    ⟨v, hvM, hv0⟩)

end Langlands

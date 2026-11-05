import Langlands.Representation.Aubert.General.RationalCuspidalCartanBound
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction
import Langlands.Representation.Aubert.General.RationalCartanJointDetection
import Langlands.Representation.Plancherel.RationalNormKernelSmoothDual

/-! # Compact restriction of cuspidal representations to the actual norm kernel -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General

open RationalPointFamily

section Assembly

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice S)

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]

/-- Assemble actual compact coefficients from joint detection and the proved
proper-Jacquet coefficient bound. -/
theorem compactSmoothDualCoefficients_normKernel_of_jointDetection
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hRoots : HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (K0 : Subgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : FiniteCartanCovering F i ν K0)
    (hdet : JointCartanDetection (fun β x => simpleRootPairing i ν β x)
      (fun x => Plancherel.rationalCharacterValuation G (uniformizerPowers i (.ofAdd x)))) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    let h := isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν
    ∀ (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A →
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation := by
  have := hG.smooth
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  dsimp only
  intro A hA w ℓ hℓ
  have hℓambient : IsSmoothVector A.representation.dual ℓ :=
    (Plancherel.isSmoothVector_dual_rationalNormKernel_iff G A.representation ℓ).mp hℓ
  have hsupport := hasCompactSupport_normKernel_of_finiteCartanCovering i ν K0 hK0 hcover hdet
    (matrixCoefficient A.representation ℓ w) (fun F₀ => ?_)
  · exact hsupport
  · let Fset : Set (rationalPoints G) := Subtype.val '' (F₀ : Set (centralizerPoints i))
    have hfinite : Fset.Finite := F₀.finite_toSet.image _
    have hcentral : Fset ⊆ centralizerPoints i := by
      rintro _ ⟨f, _, rfl⟩
      exact f.property
    obtain ⟨B, hB⟩ := exists_rational_compact_translate_pairing_bound i ν hG hi hν hStandard
      hRoots hU hbasis hfinite hcentral (K0 : Set (rationalPoints G)) hK0 A hA ℓ hℓambient w
    exact ⟨B, fun k₁ k₂ f x hk₁ hk₂ hf hx hnonzero =>
      hB k₁ hk₁ k₂ hk₂ x hx f ⟨f, hf, rfl⟩ hnonzero⟩

end Assembly

/-- Renard VI.2.1, (a) implies (c), for the exact published actual-group target. -/
theorem rationalCuspidalCompactRestriction : RationalCuspidalCompactRestrictionStatement.{u,v} := by
  intro F _ _ _ _ G hG S i hi
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  dsimp only
  intro _ _ _ ν hν hStandard hRoots hU D x hx hprops hbasis hcover
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro A hA
  exact compactSmoothDualCoefficients_normKernel_of_jointDetection i ν hG hi hν hStandard
    hRoots hU (D.specialCompactSubgroup x) hprops.2.1.1 hbasis hcover
    (rationalCartanJointDetection i ν hG hi hν hRoots) A hA

end Langlands.Aubert.General

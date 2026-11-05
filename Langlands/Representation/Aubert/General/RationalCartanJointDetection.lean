import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction
import Langlands.GroupScheme.Rational.RelativeReflectionPairing
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # Actual joint detection of Cartan parameters -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Joint detection by the actual simple roots and actual ambient valuation. -/
def RationalCartanJointDetection : Prop :=
  JointCartanDetection (fun β x => simpleRootPairing i ν β x)
    (fun x => Plancherel.rationalCharacterValuation G (uniformizerPowers i (.ofAdd x)))

variable [Mono i.hom.hom.left]

/-- The published joint spanning theorem, simple-root generation and the actual
uniformizer valuation prove joint detection at the host theorem's hypotheses. -/
theorem rationalCartanJointDetection (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hRoots : HasRelativeRootSystem i) : RationalCartanJointDetection i ν := by
  intro x y hxy
  have hpair := congrArg Prod.fst hxy
  have hval := congrArg Prod.snd hxy
  have hroot : Set.EqOn (rationalCocharacterEvaluation x)
      (rationalCocharacterEvaluation y) (relativeRootSpan i : Set _) := by
    rw [← ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
      (fun _ hα => hRoots.neg_mem_relativeRoots i hi.isSplitSubtorus.1 hα)]
    apply LinearMap.eqOn_span'
    rintro _ ⟨β, hβ, rfl⟩
    simp only [rationalCocharacterEvaluation_toRat]
    exact_mod_cast congrFun hpair (⟨β, hβ⟩ : SimpleRoot i ν)
  have hrestrict (χ : rationalCharacters G) :
      rationalCocharacterEvaluation x (toRat (torusCharacterRestrict i χ)) =
        rationalCocharacterEvaluation y (toRat (torusCharacterRestrict i χ)) := by
    simp only [rationalCocharacterEvaluation_toRat]
    have hv := congrArg (fun a => a.toAdd χ) hval
    simp only [uniformizerPowers, MonoidHom.comp_apply,
      Plancherel.RenardCartan.rationalCharacterValuation_map_uniformizerSection] at hv
    exact_mod_cast hv
  have heval : rationalCocharacterEvaluation x = rationalCocharacterEvaluation y := by
    apply LinearMap.ext_on (relativeRootsRestrictedCharactersSpan F G hG S i hi)
    rintro _ ⟨β, hβ, rfl⟩
    rcases hβ with hβ | ⟨χ, rfl⟩
    · exact hroot (toRat_mem_ratSpan hβ)
    · exact hrestrict χ
  have := CocharacterUniformizer.latticePairing_isPerfPair F S hi.isSplitSubtorus.1
  apply (LinearMap.IsPerfPair.bijective_right (latticePairing S)).injective
  apply LinearMap.ext
  intro χ
  have h := LinearMap.congr_fun heval (toRat χ)
  simp only [rationalCocharacterEvaluation_toRat] at h
  exact_mod_cast h

end Langlands.Aubert.General

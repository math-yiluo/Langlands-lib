import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.Representation.Exponents.PresentationConeContractionProof
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # Uniform contraction on the prescribed standard component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.Dynamic
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S A : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

/-- A root presentation on the original torus, chamber, face and component,
using the supplied actual standard-Levi representative. -/
def componentRootPresentation
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {M : GroupScheme (Spec (CommRingCat.of F))} (j : M ⟶ G)
    (hj : (standardLevi i ν J).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (a : A.toGrp ⟶ M) (ha : IsSplitComponent a) (hcomp : a ≫ j = q ≫ i) :
    ParabolicRootPresentation (Standard.parabolicHom i ν J)
      (hj.inclusionHom (Standard.isRepresentedBy_parabolicHom i ν J)
        (standardLevi_le_standardParabolic i ν J)) a := by
  let : Smooth G.X.hom := hG.smooth
  let : IsSeparated G.X.hom := hG.isSeparated
  let hstd := standardCocharacter F G hG S i hi ν hν J hJ
  let ζ := hstd.1.choose
  have hζ : IsStandardCocharacter i ν J ζ := hstd.1.choose_spec
  have hcompare := hstd.2 ζ hζ
  let χ := CommGroupScheme.groupHom ζ ≫ i
  let p := Standard.parabolicHom i ν J
  let l := hj.inclusionHom (Standard.isRepresentedBy_parabolicHom i ν J)
    (standardLevi_le_standardParabolic i ν J)
  have hlcomp : l ≫ p = j := SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
  have hp : (parabolic χ).IsRepresentedBy p := by
    rw [← hcompare.1]
    exact Standard.isRepresentedBy_parabolicHom i ν J
  have hm : (centralizer χ).IsRepresentedBy j := by
    rw [← hcompare.2.1]
    exact hj
  have hu : (unipotent χ).IsRepresentedBy (Standard.unipotentHom i ν J) := by
    rw [← hcompare.2.2]
    exact Standard.isRepresentedBy_unipotentHom i ν J
  have hpc : IsClosedSubgroup p := Standard.isClosedSubgroup_parabolicHom i ν J
  have hM := dynamicCentralizerReductive F G hG χ M j hjc hm
  let : IsAffineHom (Standard.parabolicScheme i ν J).X.hom := hpc.isAffineHom
  have hrad : LeviSubgroup.IsGeometricUnipotentRadical
      (Standard.unipotentToParabolic i ν J) := by
    have hUcomp : (unipotent χ).IsRepresentedBy
        (Standard.unipotentToParabolic i ν J ≫ p) := by
      rw [Standard.unipotentToParabolic_comp]
      exact hu
    exact (Dynamic.isGeometricUnipotentRadical_of_centralizer
      χ j p (Standard.unipotentToParabolic i ν J) hp hUcomp hm hM).leviSubgroup
  have hmul : IsIso (subgroupMultiplication l (Standard.unipotentToParabolic i ν J)) :=
    Dynamic.isIso_subgroupMultiplication hp hm hu l
      (Standard.unipotentToParabolic i ν J) hlcomp (Standard.unipotentToParabolic_comp i ν J)
  have hl : IsRationalLeviSubgroup l :=
    ⟨hpc.isAffineHom, IsClosedSubgroup.of_comp hpc (hlcomp ▸ hjc), hM,
      ⟨_, Standard.unipotentToParabolic i ν J, hrad, hmul⟩⟩
  refine
    { data := { T := S, i := i, ν := ν, J := J, f := Additive.ofMul q }
      isCompatible :=
        { parabolic := isParabolicSubgroup_of_range_eq_dynamicParabolic hG p hpc χ hp.2
          levi := hl
          splitComponent := ha
          maximalSplit := hi
          generic := hν
          subset_simpleRoots := hJ
          parabolic_eq := (Standard.isRepresentedBy_parabolicHom i ν J).2
          levi_eq := ?_
          factor_comp := ?_
          minimal := genericMinimalParabolic F G hG S i hi ν hν
          minimal_le := ?_
          realization := ?_ } }
  · rw [hlcomp]
    exact hj.2
  · change q ≫ i = a ≫ l ≫ p
    rw [hlcomp]
    exact hcomp.symm
  · rw [(Standard.isRepresentedBy_parabolicHom i ν J).2, hcompare.1]
    apply ((relativeRootSignInclusions F G hG S i hi ν ζ).1).mpr
    intro α hα hnonneg
    apply hζ.pairing_nonneg_of_positive i ν
    exact ⟨hα, lt_of_le_of_ne hnonneg (Ne.symm (hν α hα))⟩
  · refine ⟨ζ, hζ, hp.2, ?_⟩
    rw [hlcomp]
    exact hm.2

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local instance componentUniformContractionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance componentUniformContractionTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Every compact subset of the literal standard radical is contracted into
any ambient identity neighborhood, uniformly on a whole epsilon chamber. -/
theorem IsCompatibleStandardSplitComponent.uniform_contraction
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (C : Set (rationalPoints G)) (hC : IsCompact C)
    (hCU : C ⊆ standardUnipotentPoints i ν J)
    (W : Set (rationalPoints G)) (hW : W ∈ 𝓝 (1 : rationalPoints G)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ m ∈ standardComponentCAepsilon i ν J q ε,
        ∀ x ∈ C, m * x * m⁻¹ ∈ W := by
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Langlands.Plancherel.rationalPoints_nonarchimedeanGroup G
  obtain ⟨_, M, j, a, hj, hjc, _, ha, hcomp⟩ := hA
  let l := hj.inclusionHom (Standard.isRepresentedBy_parabolicHom i ν J)
    (standardLevi_le_standardParabolic i ν J)
  let r := componentRootPresentation i ν hG hi hν hJ j hj hjc a ha hcomp
  have hlcomp : l ≫ Standard.parabolicHom i ν J = j :=
    SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
  have hr := r.leviSubgroup_isGeometricUnipotentRadical_radicalHom
  have hUrange : SubgroupFunctor.range
      (r.radicalHom ≫ Standard.parabolicHom i ν J) = standardUnipotent i ν J := by
    obtain ⟨ζ, hζ, hP, hM⟩ := r.isCompatible.realization
    have hPd : (parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
        (Standard.parabolicHom i ν J) :=
      ⟨(Standard.isRepresentedBy_parabolicHom i ν J).1, hP⟩
    have hMd : (centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
        (l ≫ Standard.parabolicHom i ν J) := by
      have hrep : (standardLevi i ν J).IsRepresentedBy
          (l ≫ Standard.parabolicHom i ν J) := by
        rw [hlcomp]
        exact hj
      exact ⟨hrep.1, hM⟩
    have h := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
      (CommGroupScheme.groupHom ζ ≫ i) hPd hMd
      r.isCompatible.levi.isConnectedReductive hr
    exact h.trans ((standardCocharacter F G hG S i hi ν hν J hJ).2 ζ hζ).2.2.symm
  have hCimage : C ⊆ pointImage (r.radicalHom ≫ Standard.parabolicHom i ν J) := by
    rw [pointImage_eq_range_carrier, hUrange]
    exact hCU
  obtain ⟨ε, hε, heps⟩ := presentationConeContraction F G hG
    (Standard.parabolicScheme i ν J) M _ (Standard.parabolicHom i ν J) l r.radicalHom
    r.isCompatible.parabolic r.isCompatible.levi hr
    r.isIso_subgroupMultiplication_radicalHom A a r C hC hCimage W hW
  refine ⟨ε, hε, ?_⟩
  rintro m ⟨t, ht, rfl⟩ x hx
  have heq : a ≫ l ≫ Standard.parabolicHom i ν J = q ≫ i := by
    rw [hlcomp]
    exact hcomp
  have hpoint := heps t ht x hx
  rwa [heq] at hpoint

end Langlands.BruhatTits.SpecialCompact

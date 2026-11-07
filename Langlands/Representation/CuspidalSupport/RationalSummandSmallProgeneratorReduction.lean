import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.CuspidalSupport.RationalUniversalMembership
import Langlands.Representation.CuspidalSupport.RationalUniversalGeneration
import Langlands.Representation.CuspidalSupport.RationalUniversalSmallness
import Langlands.Representation.CompactCoefficient.Subquotients
import Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceReduction

/-! Renard VI.4.1, Proposition, for the compact induction of one irreducible
subrepresentation of the norm-kernel restriction, from the same restriction
inputs as the published full-restriction reduction. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.CategoryTheory.Renard
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uΓ uF uV

/-- In a locally compact nonarchimedean group, compact open subgroups of an
open subgroup are cofinal among its open subgroups. -/
theorem compactOpen_cofinal_of_isOpen {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]
    [NonarchimedeanGroup Γ] [LocallyCompactSpace Γ]
    (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) :
    ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ K := by
  intro K
  have hopen : IsOpen ((Subtype.val : H → Γ) '' (K : Set H)) :=
    hH.isOpenMap_subtype_val _ K.isOpen
  obtain ⟨V, hVc, hVK⟩ := Langlands.Jacquet.exists_isCompact_openSubgroup_subset
    (hopen.mem_nhds ⟨1, K.one_mem, rfl⟩)
  refine ⟨V.comap H.subtype continuous_subtype_val, ?_, ?_⟩
  · have hsub : (V : Set Γ) ⊆ Set.range (Subtype.val : H → Γ) := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := hVK hx
      exact ⟨y, rfl⟩
    exact Topology.IsInducing.subtypeVal.isCompact_preimage' hVc hsub
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hVK (OpenSubgroup.mem_comap.mp hx)
    rwa [Subtype.val_injective hyx] at hy

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandReductionTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalSummandReductionTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
  (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G))
  (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)

/-- Compact induction of `j`, from Π = ind ρ to the full-restriction
induction Π₁ = ind (Res π). -/
def rationalSummandInductionToUniversal :
    rationalNormKernelSummandInduction G ρ ⟶ rationalNormKernelCompactInduction G π :=
  (Induction.compactInductionFunctor (rationalCommonNormKernel G)).map (SmoothRep.toRep.map j)

/-- Compact induction of an injective map is injective. -/
theorem rationalSummandInductionToUniversal_injective
    (hj : Function.Injective (SmoothRep.hom j)) :
    Function.Injective (SmoothRep.hom (rationalSummandInductionToUniversal G π ρ j)) := by
  intro f f' h
  apply Induction.compactFunctions_ext
  intro x
  apply hj
  exact congrArg (fun φ => Induction.eval (rationalCommonNormKernel G)
    (π.representation.comp (rationalCommonNormKernel G).subtype) φ.1 x) h

/-- Π lies in the inertia block whenever Π₁ does: it is a subrepresentation. -/
theorem rationalNormKernelSummandInduction_mem
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hj : Function.Injective (SmoothRep.hom j)) :
    rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelSummandInduction G ρ) :=
  rationalInertiaBlockProperty_of_isSubquotient hmem
    (SmoothRep.IsSubrepresentation.isSubquotient
      ⟨_, rationalSummandInductionToUniversal_injective G π ρ j hj⟩)

/-- Frobenius reciprocity applied to `j`: Π maps nontrivially to every object
in the unramified orbit of the lifted base. -/
theorem exists_nonzero_rationalNormKernelSummandInduction
    (hρ : ρ.IsIrreducible) (hj : Function.Injective (SmoothRep.hom j))
    (D : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (h : IsRationalInertiaRelated G (rationalInertiaBaseLift G π) D) :
    ∃ q : rationalNormKernelSummandInduction G ρ ⟶ D, q ≠ 0 := by
  obtain ⟨χ, ⟨e⟩⟩ := h
  let E := (rationalNormKernelTwistRestrictionEquiv G π χ).trans
    (Induction.restrictAlongEquiv (rationalCommonNormKernel G).subtype
      (SmoothRep.equivOfIso e.symm))
  let φ : ρ.representation.IntertwiningMap
      (D.representation.comp (rationalCommonNormKernel G).subtype) :=
    E.toIntertwiningMap.comp (SmoothRep.hom j)
  let q : rationalNormKernelSummandInduction G ρ ⟶ D := SmoothRep.ofHom
    (Induction.cosetSum (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G)
      D.representation ρ.representation φ)
  let := hρ
  have : Nontrivial ρ := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (rationalCommonNormKernel G)) ρ.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ)
  refine ⟨q, fun hq => hv ?_⟩
  have h1 := Induction.cosetSum_comp_unitMap (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G) D.representation ρ.representation ρ.isSmooth φ v
  have h2 : SmoothRep.hom q (Induction.unitMap (rationalCommonNormKernel G)
      (isOpen_rationalCommonNormKernel G) ρ.representation ρ.isSmooth v) = 0 := by
    rw [hq]
    rfl
  have h3 : E (SmoothRep.hom j v) = E 0 := (h1.symm.trans h2).trans (map_zero E).symm
  exact hj ((E.toLinearEquiv.injective h3).trans (map_zero (SmoothRep.hom j)).symm)

/-- An irreducible ρ is cyclic, so Π is finitely generated. -/
theorem finite_rationalNormKernelSummandInduction (hρ : ρ.IsIrreducible) :
    Module.Finite (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      (rationalNormKernelSummandInduction G ρ).representation.asModule := by
  let := hρ
  have : Nontrivial ρ.representation.asModule := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (rationalCommonNormKernel G)) ρ.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.representation.asModule)
  have : Module.Finite (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      ρ.representation.asModule :=
    ⟨⟨{v}, by
      rw [Finset.coe_singleton]
      exact IsSimpleModule.span_singleton_eq_top _ hv⟩⟩
  exact Induction.finite_compactInduced_of_finite (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G) ρ

variable [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]

/-- Compact coefficients of the whole restriction pass to ρ along the
injection `j`, so Π is projective among smooth representations. -/
theorem rationalNormKernelSummandInduction_projective
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    (hj : Function.Injective (SmoothRep.hom j)) :
    Projective (rationalNormKernelSummandInduction G ρ) := by
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TotallyDisconnectedSpace F := BruhatTits.localField_totallyDisconnectedSpace F
  let : T2Space (GroupScheme.rationalPoints G) := rationalPoint_t2Space F G
  let : TotallyDisconnectedSpace (GroupScheme.rationalPoints G) :=
    BruhatTits.rationalPoint_totallyDisconnectedSpace F G
  have hρc : HasCompactSmoothDualCoefficients ρ.representation :=
    HasCompactSmoothDualCoefficients.of_injective hc
      (compactOpen_cofinal_of_isOpen (rationalCommonNormKernel G)
        (isOpen_rationalCommonNormKernel G))
      ρ.isSmooth (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).isSmooth
      (SmoothRep.hom j) hj
  exact Induction.projective_compactInduced_of_compactCoefficients
    (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G) ρ hρc

/-- Renard VI.4.1, Proposition, for Π = ind ρ, from compact coefficients of
the whole restriction, VI.3.2(ii) and VI.3.2(iii). -/
theorem isRationalInertiaSmallProgenerator_rationalNormKernelSummandInduction
    (hG : GroupScheme.IsConnectedReductive G) (hπ : π.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV})
    (hρ : ρ.IsIrreducible) (hj : Function.Injective (SmoothRep.hom j)) :
    IsRationalInertiaSmallProgenerator G π (rationalNormKernelSummandInduction G ρ) := by
  have hmem := rationalNormKernelSummandInduction_mem G π ρ j
    (rationalNormKernelCompactInduction_mem_of_restriction G hG π hπ hc hfin htw) hj
  have hproj := rationalNormKernelSummandInduction_projective G π ρ j hc hj
  refine ⟨hmem, ?_, ?_, ?_, ?_⟩
  · intro Y Z q hq f
    have := rationalInertiaBlock_projective_of_projective G (rationalInertiaBaseLift G π)
      ⟨_, hmem⟩ hproj
    exact ⟨Projective.factorThru f q, Projective.factorThru_comp f q⟩
  · apply SmoothRep.faithful_preadditiveCoyonedaInt_of_projective_subquotients
    intro Y D hD hDY
    exact exists_nonzero_rationalNormKernelSummandInduction G π ρ j hρ hj D
      (Y.property D hD hDY)
  · intro I
    exact rationalInertiaBlock_hasColimitsOfShape G (rationalInertiaBaseLift G π) (I := I)
  · intro I
    have := finite_rationalNormKernelSummandInduction G ρ hρ
    exact rationalInertiaBlockHom_preservesCoproducts_of_finite G π ⟨_, hmem⟩ I

open Aubert.General Aubert.General.RationalPointFamily GroupScheme
open Langlands.BruhatTits.SpecialCompact

/-- Renard VI.4.1, Proposition, from three structural inputs: special-vertex
data carrying the inputs of the published VI.2.1 implication (a) ⇒ (c),
VI.3.2(ii) and VI.3.2(iii). -/
theorem rationalSummandSmallProgenerator_of_specialVertexInputs
    (hInputs : RationalSpecialVertexCompactInputsStatement.{uF})
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}) :
    RationalSummandSmallProgeneratorStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  obtain ⟨D, x, hspecial, hprops, hbasis, hcover⟩ := hInputs F G hG T i hi ν hν
  have hc := rationalCuspidalCompactRestriction F G hG T i hi ν hν hStandard hRoots hU
    D x hspecial hprops hbasis hcover π hcusp
  exact isRationalInertiaSmallProgenerator_rationalNormKernelSummandInduction G π ρ j hG hπ
    hc hfin htw hρ hj

/-- Renard VI.4.1, Proposition, from the joint special-compact basis existence
target, VI.3.2(ii) and VI.3.2(iii). -/
theorem rationalSummandSmallProgenerator_of_jointBasis
    (hJoint : JointSpecialCompactBasisExistenceStatement.{uF})
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}) :
    RationalSummandSmallProgeneratorStatement.{uF, uV} :=
  rationalSummandSmallProgenerator_of_specialVertexInputs
    (rationalSpecialVertexCompactInputs_of_jointBasis hJoint) hfin htw

/-- Renard VI.4.1, Theorem, from the same three structural inputs. -/
theorem rationalSummandHomEquivalence_of_jointBasis
    (hJoint : JointSpecialCompactBasisExistenceStatement.{uF})
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}) :
    RationalSummandHomEquivalenceStatement.{uF, uV} :=
  rationalSummandHomEquivalence_of_smallProgenerator
    (rationalSummandSmallProgenerator_of_jointBasis hJoint hfin htw)

end Langlands.CuspidalSupport

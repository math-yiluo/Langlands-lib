import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-!
# Reducing Renard VI.3.3.1 to compact restriction and VI.2.1

The proper-standard-cuspidal form of VI.3.3.1 follows from three separately
owned propositions: its compact-restriction intermediate form, the implication
(a) ⇒ (c) of VI.2.1, and the existence of one geometric special vertex carrying
the structural inputs of that implication. The last input follows from the joint
special-compact basis existence target and the proved finite positive Cartan
cover. None of the three propositions is proved here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme
open Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact

/-- The structural antecedents of the published VI.2.1 implication at one
geometric special vertex: for every actual maximal split torus and generic
cocharacter there are an apartment datum and a special vertex whose special
compact subgroup has the special compact properties, the simultaneous standard
basis and the finite Cartan covering. -/
def RationalSpecialVertexCompactInputsStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment),
        D.IsSpecialApartmentVertex x ∧
          SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
          SimultaneousStandardBasisAt i ν (D.specialCompactSubgroup x) ∧
          FiniteCartanCovering F i ν (D.specialCompactSubgroup x)

/-- The joint special-compact witness supplies the special-vertex inputs: its
Renard comparison gives the finite Cartan covering of the same subgroup. -/
theorem rationalSpecialVertexCompactInputs_of_jointBasis
    (hJoint : JointSpecialCompactBasisExistenceStatement.{uF}) :
    RationalSpecialVertexCompactInputsStatement.{uF} := by
  intro F _ _ _ _ G hG S i hi ν hν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  obtain ⟨D, x, Z, j, s, -, hrep, hcomp, h, hspecial, hprops, -, -, hcartan,
    -, -, hbasis⟩ := hJoint F G hG S i hi ν hν
  exact ⟨D, x, hspecial, hprops, hbasis,
    rationalPositiveCartanCover F G S i ν D x Z j s h hrep hcomp hcartan⟩

/-- VI.3.3.1 for proper-standard cuspidal representations from its
compact-restriction form, VI.2.1 (a) ⇒ (c) and the special-vertex inputs. -/
theorem rationalCuspidalInertiaDecomposition_of_specialVertexInputs
    (hDecomp : RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV})
    (hCompact : RationalCuspidalCompactRestrictionStatement.{uF, uV})
    (hInputs : RationalSpecialVertexCompactInputsStatement.{uF}) :
    RationalCuspidalInertiaDecompositionStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hRoots hU h π hirr hcusp
  obtain ⟨D, x, hspecial, hprops, hbasis, hcover⟩ := hInputs F G hG T i hi ν hν
  exact hDecomp F G hG π hirr
    (hCompact F G hG T i hi ν hν hStandard hRoots hU D x hspecial hprops hbasis
      hcover π hcusp)

/-- VI.3.3.1 for proper-standard cuspidal representations from its
compact-restriction form, VI.2.1 (a) ⇒ (c) and the joint special-compact
basis existence target. -/
theorem rationalCuspidalInertiaDecomposition_of_jointBasis
    (hDecomp : RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV})
    (hCompact : RationalCuspidalCompactRestrictionStatement.{uF, uV})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{uF}) :
    RationalCuspidalInertiaDecompositionStatement.{uF, uV} :=
  rationalCuspidalInertiaDecomposition_of_specialVertexInputs hDecomp hCompact
    (rationalSpecialVertexCompactInputs_of_jointBasis hJoint)

end Langlands.CuspidalSupport

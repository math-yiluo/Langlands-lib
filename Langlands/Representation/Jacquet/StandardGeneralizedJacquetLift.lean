import Langlands.Representation.Jacquet.StandardFixedVectorGeneration
import Langlands.Representation.Jacquet.StandardCentralContraction
import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-! # The standard fixed-vector Jacquet map from the generalized Jacquet lemma -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Jacquet

variable {F : Type uF} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- The opposite standard radical agrees with the inverse-cocharacter dynamic
radical for a supplied standard cocharacter, with no global standard-existence premise. -/
theorem standardOppositeUnipotentPoints_eq_dynamic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    {zeta : cocharacterLattice S} (hzeta : IsStandardCocharacter i ν J zeta) :
    standardOppositeUnipotentPoints i ν J =
      (Dynamic.unipotent (Dynamic.inverseCocharacter
        (CommGroupScheme.groupHom zeta ≫ i))).carrier (Over.mk (𝟙 _)) := by
  have hrev := (standard_eq_dynamic_of_relativeRootNegation relativeRootNegation
    F G hG S i hi (-ν) (hν.neg i ν) (Neg.neg '' J) (-zeta)
      (hzeta.neg i ν (relativeRootNegation F G hG S i hi))).2.2
  rw [groupHom_neg_comp_eq_oppositeCocharacter] at hrev
  exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hrev

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}

/-- The published generalized Jacquet lemma gives the exact standard
fixed-vector surjectivity from the local compatible component and pointwise basis data.
The generalized lemma remains an explicit prerequisite. -/
theorem standardFixedJacquetMap_surjective_of_generalizedJacquet
    (hJacquet : GeneralizedJacquetLemmaStatement.{uF, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ) :
    Function.Surjective (fixedJacquetMap ρ
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) K.toSubgroup) := by
  let : T2Space F := BruhatTits.localField_t2Space F
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) := Plancherel.rationalPoints_nonarchimedeanGroup G
  have hstd := standard_eq_dynamic_of_relativeRootNegation relativeRootNegation
    F G hG S i hi ν hν J zeta hzeta
  have hM : standardLeviPoints i ν J =
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hstd.2.1
  have hN : standardUnipotentPoints i ν J =
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hstd.2.2
  have hNbar := standardOppositeUnipotentPoints_eq_dynamic i ν hG hi hν hzeta
  let g := hA.strictElement i ν hi hzeta
  have hcentral : ∀ m ∈ (Dynamic.centralizer
      (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)), m * g = g * m := by
    intro m hm
    have hm' : m ∈ standardLeviPoints i ν J := by rwa [hM]
    exact congrArg (fun z : standardLeviPoints i ν J => (z : rationalPoints G))
      (Subgroup.mem_center_iff.mp (hA.centralStrictElement i ν hi hzeta).property ⟨m, hm'⟩)
  have hcon := hA.centralStrictElement_isIwahoriContraction i ν hi hzeta K hBasis
  change IsIwahoriContraction K (standardUnipotentPoints i ν J)
    (standardLeviPoints i ν J) (standardOppositeUnipotentPoints i ν J) g at hcon
  rw [hN, hM, hNbar] at hcon
  have hs := hJacquet F G hG (CommGroupScheme.groupHom zeta ≫ i)
    K hK g hcentral hcon V ρ hρ
  have htransport (N M : Subgroup (rationalPoints G))
      (hle : M ≤ Subgroup.normalizer (N : Set (rationalPoints G)))
      (eN : N = standardUnipotentPoints i ν J)
      (eM : M = standardLeviPoints i ν J)
      (hsurj : Function.Surjective (fixedJacquetMap ρ N M hle K.toSubgroup)) :
      Function.Surjective (fixedJacquetMap ρ
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) K.toSubgroup) := by
    subst N
    subst M
    exact hsurj
  exact htransport _ _ _ hN.symm hM.symm hs

/-- A chosen complex-linear section of the standard fixed-vector Jacquet map,
conditional on the generalized Jacquet lemma. No canonical choice is asserted. -/
def standardFixedJacquetLift
    (hJacquet : GeneralizedJacquetLemmaStatement.{uF, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ) :
    fixedVectors (standardJacquetAction i ν ρ J)
      (K.toSubgroup.comap (standardLeviPoints i ν J).subtype) →ₗ[ℂ]
      fixedVectors ρ K.toSubgroup :=
  ((fixedJacquetMap ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
      K.toSubgroup).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr
        (standardFixedJacquetMap_surjective_of_generalizedJacquet i ν hJacquet
          hG hi hν hzeta hA K hK hBasis ρ hρ))).choose

/-- The chosen section is a right inverse to the exact standard fixed-vector map. -/
theorem fixedJacquetMap_comp_standardFixedJacquetLift
    (hJacquet : GeneralizedJacquetLemmaStatement.{uF, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ) :
    (fixedJacquetMap ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) K.toSubgroup).comp
      (standardFixedJacquetLift i ν hJacquet hG hi hν hzeta hA K hK hBasis ρ hρ) =
      LinearMap.id :=
  ((fixedJacquetMap ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
      K.toSubgroup).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr
        (standardFixedJacquetMap_surjective_of_generalizedJacquet i ν hJacquet
          hG hi hν hzeta hA K hK hBasis ρ hρ))).choose_spec

end Langlands.Jacquet

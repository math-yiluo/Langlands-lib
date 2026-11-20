import Langlands.Representation.Category.FixedVectorConstituent
import Langlands.Representation.Jacquet.IrreducibleFixedVectorGeneration
import Langlands.Representation.CuspidalSupport.StandardLeviInductionFixedVectors
import Langlands.Representation.CuspidalSupport.StandardLeviFixedVectorSupportStatements
import Langlands.Representation.CuspidalSupport.StandardRepresentativeFixedVectorCriterionProof

/-! # Standard Levi fixed-vector support -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open Langlands.Jacquet

namespace Langlands.CuspidalSupport

/-- The standard Levi scheme is a closed subgroup (the local instance of `BernsteinData`). -/
local instance supportProofLeviClosedImmersion {F : Type uF} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)} :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)

/-- The standard Levi scheme is affine (the local instance of `BernsteinData`). -/
local instance supportProofLeviAffine {F : Type uF} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)} :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left

/-- The standard Levi scheme is locally of finite type (the local instance of
`BernsteinData`). -/
local instance supportProofLeviFiniteType {F : Type uF} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)} :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- Renard VI.10.6, Corollary, for the prescribed level on a standard Levi. -/
theorem standardLeviFixedVectorSupport : StandardLeviFixedVectorSupportStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  intro family J b hb
  have hrepresentative := standardRepresentativeFixedVectorCriterion.{uF, uV}
    F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  have hinner := fun J I A => nontrivial_standardLeviInduction_fixedVectors_iff
      i ν family J I K hK K₀ hnormal hIwasawa
      (fun L => hIwahori (rootSet i ν L) (rootSet_subset i ν L)) A
  classical
  let KM : OpenSubgroup (levi i ν J) :=
    K.comap (levi i ν J).subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set (levi i ν J)) :=
    (family.closedLevi J).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hinner' (I : Finset J) (R : Finset (SimpleRoot i ν)) (h : leviIndex J I = R)
      (A : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν R)) :
      Nontrivial (fixedVectors
        ((leviNormalizedInductionFunctor (family.closedLevi J)
          (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
            family.maximalSplitTorus family.genericCocharacter R J
            (h ▸ leviIndex_subset J I))
          (h ▸ family.leviDecomposition J I) (family.closedUnipotent R)).obj A).representation
        (K.toSubgroup.comap (levi i ν J).subtype)) ↔
      Nontrivial (fixedVectors A.representation
        (K.toSubgroup.comap (levi i ν R).subtype)) := by
    subst R
    exact hinner J I A
  constructor
  · rintro ⟨τ, _hτ, hfix, I, b', h, ⟨c, _hcM, hc⟩, hsub⟩
    have hfixInd := SmoothRep.nontrivial_fixedVectors_of_isSubquotient KM hKM hsub hfix
    have hcoef := (hinner' I b'.roots h
      (bernsteinLiteralLeviRep i ν b'.roots b'.representation)).mp hfixInd
    obtain ⟨π, hπ, hfixπ⟩ := (hrepresentative b').mpr hcoef
    have heq : bernsteinInertialClass i ν family b =
        bernsteinInertialClass i ν family b' :=
      (bernsteinInertialClass_eq_iff i ν family b b').mpr ⟨c, hc⟩
    refine ⟨π, ?_, hfixπ⟩
    rw [heq]
    exact hπ
  · intro hvisible
    have hcoef := (hrepresentative b).mp hvisible
    let I : Finset J := b.roots.subtype (· ∈ J)
    have hI : leviIndex J I = b.roots := Finset.subtype_map_of_mem hb
    have hfixInd := (hinner' I b.roots hI
      (bernsteinLiteralLeviRep i ν b.roots b.representation)).mpr hcoef
    obtain ⟨τ, hτ, hsub, hfixτ⟩ :=
      SmoothRep.hasFixedVectorConstituent_of_nontrivial _ _ hfixInd
    refine ⟨τ, hτ, hfixτ, I, b, hI, ?_, hsub⟩
    exact ⟨RationalLeviConjugacy.refl _, (levi i ν J).one_mem,
      IsRationalInertiaRelated.of_iso (rationalIsoPullbackReflIso b.representation).symm⟩

end Langlands.CuspidalSupport

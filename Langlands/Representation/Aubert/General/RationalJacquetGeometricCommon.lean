import Langlands.Representation.Aubert.General.RationalJacquetTermCommon
import Langlands.Representation.Aubert.General.JacquetK0Assembly

/-! # Actual geometric Jacquet terms from point-source intersection identities -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)

/-- The three structural source identities on actual points, for every
minimum representative and every normalizer lift. This predicate contains
no representation comparison or scheme Coxeter realization. -/
def PointSourceIntersectionIdentities : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i), IsMinimal cs I J w →
    ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i)), QuotientGroup.mk n = w →
      let K := simpleImage cs w⁻¹ I ∩ J
      geometricSourceIntersection (levi i ν I) (levi i ν J)
          (n : RationalPoint k G.X) = levi i ν K ∧
        (geometricSourceIntersection (parabolic i ν I) (levi i ν J)
          (n : RationalPoint k G.X)).subgroupOf (levi i ν J) =
            (parabolic i ν K).subgroupOf (levi i ν J) ∧
        (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
          (n : RationalPoint k G.X)).subgroupOf (levi i ν J) =
            (unipotent i ν K).subgroupOf (levi i ν J)

variable (hSource : PointSourceIntersectionIdentities i ν cs)

include hSource in
omit [Mono i.hom.hom.left] in
/-- The same three source identities at the inverse minimum give all the
target identities, with the original lift and inverse-conjugation direction. -/
theorem pointTargetIntersectionIdentities
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w) :
    let K := simpleImage cs w J ∩ I
    geometricTargetIntersection (levi i ν I) (levi i ν J)
        (n : RationalPoint k G.X) = levi i ν K ∧
      (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
        (n : RationalPoint k G.X)).subgroupOf (levi i ν I) =
          (parabolic i ν K).subgroupOf (levi i ν I) ∧
      (geometricTargetIntersection (levi i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X)).subgroupOf (levi i ν I) =
          (unipotent i ν K).subgroupOf (levi i ν I) := by
  have hn' : QuotientGroup.mk n⁻¹ = w⁻¹ := by
    rw [QuotientGroup.mk_inv, hn]
  simpa only [geometricTargetIntersection, geometricSourceIntersection,
    inv_inv, Subgroup.coe_inv] using
      hSource J I w⁻¹ (isMinimal_inv cs hw) n⁻¹ hn'

section Topology

variable [TopologicalSpace k]

local instance rationalGeometricCommonPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))

omit [Mono i.hom.hom.left] [TopologicalSpace k]
  [LocallyCompactSpace (RationalPoint k G.X)] [NonarchimedeanGroup (RationalPoint k G.X)] in
private theorem subtypeIntersectionIndex (I J : Finset (SimpleRoot i ν)) (w : Weyl i) :
    leviIndex J ((simpleImage cs w⁻¹ I ∩ J).subtype (· ∈ J)) =
      simpleImage cs w⁻¹ I ∩ J :=
  Finset.subtype_map_of_mem fun _ ha => (Finset.mem_inter.mp ha).2

include hSource hInter hG hi hν in
omit [Mono i.hom.hom.left] [TopologicalSpace k] [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] in
/-- The actual geometric source and target decompositions follow from
the source identities and the literal standard decompositions inside Levis. -/
theorem geometricIntersectionDecompositions_of_pointSource :
    GeometricIntersectionDecompositions
      (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs := by
  intro I J w hw n hn
  let S := (simpleImage cs w⁻¹ I ∩ J).subtype (· ∈ J)
  let K := (simpleImage cs w J ∩ I).subtype (· ∈ I)
  have hS := subtypeIntersectionIndex i ν cs I J w
  have hK := subtypeIntersectionIndex i ν cs J I w⁻¹
  simp only [inv_inv] at hK
  obtain ⟨hSL, hSP, hSU⟩ := hSource I J w hw n hn
  obtain ⟨hTL, hTP, hTU⟩ :=
    pointTargetIntersectionIdentities i ν cs hSource I J w hw n hn
  rw [← hS] at hSL hSP hSU
  rw [← hK] at hTL hTP hTU
  exact ⟨geometricSourceDecompositionOfEq
      (parabolic i ν) (levi i ν) (unipotent i ν) I J (leviIndex J S) n
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J S) hSP hSL hSU,
    geometricTargetDecompositionOfEq
      (parabolic i ν) (levi i ν) (unipotent i ν) I J (leviIndex I K) n
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K) hTL hTP hTU⟩

include hSource hLfl in
omit [Mono i.hom.hom.left] in
/-- The structural source identities also derive preservation for the two
actual factors. The supplied actual decomposition witnesses are arbitrary. -/
theorem geometricTermFiniteLength_of_pointSource
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n) :
    GeometricTermFiniteLength.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht := by
  let S := (simpleImage cs w⁻¹ I ∩ J).subtype (· ∈ J)
  let K := (simpleImage cs w J ∩ I).subtype (· ∈ I)
  have hS := subtypeIntersectionIndex i ν cs I J w
  have hK := subtypeIntersectionIndex i ν cs J I w⁻¹
  simp only [inv_inv] at hK
  obtain ⟨hSL, -, hSU⟩ := hSource I J w hw n hn
  obtain ⟨hTL, hTP, hTU⟩ :=
    pointTargetIntersectionIdentities i ν cs hSource I J w hw n hn
  rw [← hS] at hSL hSU
  rw [← hK] at hTL hTP hTU
  exact geometricTermFiniteLengthOfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    I J (leviIndex J S) (leviIndex I K) n
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J S))
    (levi_le_of_subset i ν hInter hG hi hν _ I (leviIndex_subset I K))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J S)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
    ⟨(hLfl J S).2.2.1, (hLfl J S).2.2.2⟩
    ⟨(hLfl I K).1, (hLfl I K).2.1⟩
    hs ht hSL hSU hTL hTP hTU

variable (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hConj : StandardLeviConjugationStatement.{u})

include hSource in
/-- Every actual geometric term for `r_J i_I` is the standard intersection
term. No representation equality is included in the source identities. -/
theorem geometricTermK0_eq_intersection_of_pointSource
    (J I : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
    (hfl : GeometricTermFiniteLength.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht) :
    geometricTermK0.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht hfl =
      rationalRestrictedJacquetTerm.{u, v}
        i ν hInter hG hi hν hU hM hLfl J I
        ((simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I))
        ((simpleImage cs w I ∩ J).subtype (· ∈ J)) n
        (intersectionJacquetConjugationMembership
          i ν hN hZ cs hLength hSimple hG hi hν hConj I J w hw n hn) := by
  let S := (simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I)
  let K := (simpleImage cs w I ∩ J).subtype (· ∈ J)
  have hS := subtypeIntersectionIndex i ν cs J I w
  have hK := subtypeIntersectionIndex i ν cs I J w⁻¹
  simp only [inv_inv] at hK
  obtain ⟨hSL, -, hSU⟩ := hSource J I w hw n hn
  obtain ⟨hTL, hTP, hTU⟩ :=
    pointTargetIntersectionIdentities i ν cs hSource J I w hw n hn
  rw [← hS] at hSL hSU
  rw [← hK] at hTL hTP hTU
  rw [rationalRestrictedJacquetTerm_eq_standard]
  exact geometricTermK0_eq_standardOfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    J I (leviIndex I S) (leviIndex J K) n
    (levi_le_of_subset i ν hInter hG hi hν _ I (leviIndex_subset I S))
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J K))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I S)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
    (intersectionJacquetConjugationMembership
      i ν hN hZ cs hLength hSimple hG hi hν hConj I J w hw n hn)
    ⟨(hLfl I S).2.2.1, (hLfl I S).2.2.2⟩
    ⟨(hLfl J K).1, (hLfl J K).2.1⟩
    hs ht hSL hSU hTL hTP hTU hfl

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hStandard : StandardCocharacterStatement.{u})
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (B : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A B)).subgroupOf (levi i ν A)))
  (J : Finset (SimpleRoot i ν))
  (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
  (hlift : ∀ w, QuotientGroup.mk (lift w) = w)

include hSource hproj hLUc in
/-- The actual geometric term after ambient source restriction is the common
term, under the three structural source identities alone. -/
theorem geometricTermK0_comp_ambient_eq_common_of_pointSource
    (I : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J I (lift w))
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J I (lift w))
    (hTermFl : GeometricTermFiniteLength.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I (lift w) hs ht) :
    (geometricTermK0.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I (lift w) hs ht hTermFl).comp
        (standardAmbientJacquetK0.{u, v}
          i ν hG hi hν hStandard hU hfl I) =
      rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift w (simpleImage cs w I ∩ J) := by
  rw [geometricTermK0_eq_intersection_of_pointSource
    i ν cs hSource hInter hG hi hν hU hM hLfl hN hZ hLength hSimple hConj
    J I w hw (lift w) (hlift w) hs ht hTermFl]
  exact rationalRestrictedJacquetTerm_comp_ambient_eq_common
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    hInter hStandard hU hM hfl hLfl hproj hLUc J lift hlift I w hw _

variable [Fintype (Weyl i)]

include hSource hproj hLUc in
/-- Discharge the common-term premise of the finite Jacquet assembly from
the structural point-source identities and the proved stages comparison. -/
theorem jacquetGeometricTermReduction_of_pointSource
    (hGeom : GeometricIntersectionDecompositions
      (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs)
    (hTermFl : ∀ (A B : Finset (SimpleRoot i ν)) (w : Weyl i)
      (hw : IsMinimal cs A B w)
      (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w),
      GeometricTermFiniteLength.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU A B n
        (hGeom A B w hw n hn).1 (hGeom A B w hw n hn).2) :
    JacquetGeometricTermReduction.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU hfl hM (torusPoints i) cs hGeom hTermFl J lift hlift
      (rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift) := by
  intro I w
  have hr := geometricTermK0_comp_ambient_eq_common_of_pointSource
    i ν cs hSource hInter hG hi hν hU hM hLfl hN hZ hLength hSimple hConj
    hStandard hfl hproj hLUc J lift hlift I w
    ((mem_minimalReps cs J I w).mp w.property)
    (hGeom J I w ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w)).1
    (hGeom J I w ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w)).2
    (hTermFl J I w ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w))
  unfold jacquetGeometricTerm
  unfold standardAmbientJacquetK0 at hr
  refine hr.trans ?_
  apply congrArg (rationalCommonJacquetTerm.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    hInter hStandard hU hM hfl hLfl J lift hlift w)
  ext a
  simp only [Finset.mem_inter]

end Topology

end Langlands.Aubert.General.RationalPointFamily

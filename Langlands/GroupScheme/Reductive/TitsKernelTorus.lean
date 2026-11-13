import Langlands.GroupScheme.Reductive.TitsIndexAnisotropicKernelStatement
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionProof
import Langlands.GroupScheme.CommutativeSubgroupIntersectionBaseChange
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedGeometricReduction

/-! # The maximal torus `T ∩ 𝒟𝒵(S)` of the semisimple anisotropic kernel -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The full pullback of a commutative subgroup along a monomorphism centralizes
every subgroup of the source that maps into the commutative subgroup. -/
theorem range_subgroupIntersectionFst_le_torusCentralizer_of_commTarget
    {S : Scheme.{u}} {D H : GroupScheme S} {A T : CommGroupScheme S}
    (d : D ⟶ H) (i : T.toGrp ⟶ H) (j : A.toGrp ⟶ D) (f : A.toGrp ⟶ T.toGrp)
    [Mono d.hom.hom] (hcomm : j ≫ d = f ≫ i) :
    SubgroupFunctor.range (subgroupIntersectionFst d i) ≤ torusCentralizer j := by
  intro U x hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  have hxy : x ≫ d.hom.hom =
      (y ≫ (subgroupIntersectionSnd d i).hom.hom) ≫ i.hom.hom := by
    rw [← hy, Category.assoc, ← Grp.comp_hom_hom,
      subgroupIntersection_condition, Grp.comp_hom_hom, ← Category.assoc]
  intro V a t
  apply (commute_iff_eq _ _).mpr
  apply (cancel_mono d.hom.hom).mp
  have hc : Commute
      (a ≫ (y ≫ (subgroupIntersectionSnd d i).hom.hom))
      (t ≫ f.hom.hom) := Commute.all _ _
  have hh := congrArg (fun z : V ⟶ T.X => z ≫ i.hom.hom) hc.eq
  simpa only [MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, hcomm, hxy] using hh

/-- The full scheme-theoretic intersection of a maximal torus of a connected
reductive group with its actual derived subgroup is a maximal torus of the
derived subgroup. -/
theorem isMaximalTorus_commutativeSubgroupIntersectionSnd_derived
    {M D : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hM : IsConnectedReductive M) (i : D ⟶ M) (hi : IsDerivedSubgroup i)
    [Mono i.hom.hom] (t : T.toGrp ⟶ M) (ht : IsMaximalTorus t) :
    IsMaximalTorus (commutativeSubgroupIntersectionSnd t i) := by
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  have hM' : IsConnectedReductive (B.obj M) :=
    connectedReductiveFieldExtensionStatement k K M hM
  have hi' : IsDerivedSubgroup (B.map i) :=
    hi.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b M)
  have ht' : IsMaximalTorus (T := T') (B.map t) :=
    (maximalTorusBaseChange k K M T t ht.1 ht.2.1).mp ht
  let : Smooth (B.obj M).X.hom := hM'.smooth
  let : IsAffineHom (B.obj M).X.hom := hM'.isAffineHom
  let : ConnectedSpace (B.obj M).X.left := hM'.connectedSpace
  obtain ⟨A, j, e, _, hjmax, _, hcomm⟩ :=
    hi'.exists_compatible_maximalTorus_of_isAlgClosed (T := T') (B.map t) ht'
  have hD' : IsConnectedReductive (B.obj D) := hi'.isConnectedReductive hM'
  have hjself := algClosedMaximalTorusCentralizer_fromQuotient
    dynamicCentralizerReductive solvableTorusQuotient K (B.obj D) hD' A j hjmax
  have : Mono (B.map i).hom.hom := inferInstance
  have hcent := range_subgroupIntersectionFst_le_torusCentralizer_of_commTarget
    (T := T') (A := A) (B.map i) (B.map t) j (CommGroupScheme.groupHom e) hcomm.symm
  let I := selfCentralizingSubgroupIntersectionIso (T := T') (A := A) (B.map i) (B.map t) j
    (CommGroupScheme.groupHom e) hcomm.symm hjself hcent ht'.2.1 hjmax.2.1
  let E : (commutativeSubgroupIntersection (T := T') (B.map t) (B.map i)).toGrp ≅ A.toGrp :=
    pullbackSymmetry (B.map t) (B.map i) ≪≫ I
  have hE : E.hom ≫ j =
      commutativeSubgroupIntersectionSnd (T := T') (B.map t) (B.map i) := by
    change (pullbackSymmetry (B.map t) (B.map i)).hom ≫ I.hom ≫ j = _
    rw [selfCentralizingSubgroupIntersectionIso_hom_comp]
    exact pullbackSymmetry_hom_comp_fst (B.map t) (B.map i)
  apply isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange (K := K) t i ht.2.1
  rw [← hE]
  exact hjmax.iso_comp E

namespace TitsIndexData

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) {M : GroupScheme (Spec (CommRingCat.of k))} {j : M ⟶ G}
  (hj : (torusCentralizer d.splitInclusion).IsRepresentedBy j)

include hj in
/-- Every actual representative of the centralizer of the maximal split torus is
connected reductive. -/
theorem centralizer_isConnectedReductive : IsConnectedReductive M :=
  splitTorusCentralizerReductive k G d.isSemisimple.isConnectedReductive d.splitTorus
    d.splitInclusion d.maximalSplit.1.1 M j hj

include hj in
/-- The centralizer representative is a closed subgroup. -/
theorem centralizer_isClosedSubgroup : IsClosedSubgroup j :=
  d.maximalSplit.1.1.isClosedSubgroup_torusCentralizer d.splitInclusion hj

/-- The maximal torus of the index data centralizes the maximal split torus. -/
theorem range_inclusion_le_torusCentralizer :
    SubgroupFunctor.range d.pinning.inclusion ≤ torusCentralizer d.splitInclusion :=
  range_le_torusCentralizer_of_factor d.splitInclusion d.pinning.inclusion
    (CommGroupScheme.groupHom d.torusMap) d.square

/-- The maximal torus of the index data, as a subgroup of the centralizer. -/
def centralizerTorus : d.pinning.torus.toGrp ⟶ M :=
  hj.liftOfLE d.pinning.inclusion d.range_inclusion_le_torusCentralizer

/-- The lift of the maximal torus composes with `j` to the original inclusion. -/
@[reassoc]
theorem centralizerTorus_comp : d.centralizerTorus hj ≫ j = d.pinning.inclusion :=
  hj.liftOfLE_comp _ _

/-- The torus of the index data is a maximal torus of the centralizer. -/
theorem isMaximalTorus_centralizerTorus : IsMaximalTorus (d.centralizerTorus hj) :=
  IsMaximalTorus.of_comp (d.centralizer_isClosedSubgroup hj)
    (by rw [d.centralizerTorus_comp hj]; exact d.maximalTorus)

variable {D : GroupScheme (Spec (CommRingCat.of k))} {i : D ⟶ M}

include hj in
/-- The actual derived subgroup of the centralizer is semisimple. -/
theorem kernel_isSemisimple (hi : IsDerivedSubgroup i) : IsSemisimple D :=
  derivedSubgroupSemisimple k M D i (d.centralizer_isConnectedReductive hj) hi

variable [Mono i.hom.hom]

/-- The maximal torus `T ∩ D` of the actual derived subgroup. -/
abbrev kernelTorus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  commutativeSubgroupIntersection (d.centralizerTorus hj) i

/-- The inclusion of `T ∩ D` into `D`. -/
abbrev kernelInclusion : (d.kernelTorus hj (i := i)).toGrp ⟶ D :=
  commutativeSubgroupIntersectionSnd (d.centralizerTorus hj) i

/-- The inclusion of `T ∩ D` into `T`, as a map of commutative group schemes. -/
def kernelTorusMap : d.kernelTorus hj (i := i) ⟶ d.pinning.torus :=
  Additive.ofMul (commutativeSubgroupIntersectionFst (d.centralizerTorus hj) i)

/-- The underlying group homomorphism of `kernelTorusMap` is the first projection. -/
theorem groupHom_kernelTorusMap :
    CommGroupScheme.groupHom (d.kernelTorusMap hj (i := i)) =
      commutativeSubgroupIntersectionFst (d.centralizerTorus hj) i := rfl

/-- The square `T ∩ D ⟶ T ⟶ M` and `T ∩ D ⟶ D ⟶ M` commutes. -/
theorem kernelInclusion_comp :
    d.kernelInclusion hj ≫ i =
      CommGroupScheme.groupHom (d.kernelTorusMap hj (i := i)) ≫ d.centralizerTorus hj :=
  (commutativeSubgroupIntersection_condition (d.centralizerTorus hj) i).symm

/-- The square of the comparison: `T ∩ D ⟶ T ⟶ G` and `T ∩ D ⟶ D ⟶ G`. -/
theorem kernelTorusMap_comp_inclusion :
    CommGroupScheme.groupHom (d.kernelTorusMap hj (i := i)) ≫ d.pinning.inclusion =
      d.kernelInclusion hj ≫ i ≫ j := by
  rw [← d.centralizerTorus_comp hj, ← Category.assoc, ← d.kernelInclusion_comp hj,
    Category.assoc]

/-- `T ∩ D` is a maximal torus of the actual derived subgroup. -/
theorem isMaximalTorus_kernelInclusion (hi : IsDerivedSubgroup i) :
    IsMaximalTorus (d.kernelInclusion hj (i := i)) :=
  isMaximalTorus_commutativeSubgroupIntersectionSnd_derived
    (d.centralizer_isConnectedReductive hj) i hi (d.centralizerTorus hj)
    (d.isMaximalTorus_centralizerTorus hj)

/-- The map `T ∩ D ⟶ T` is a closed subgroup. -/
theorem isClosedSubgroup_kernelTorusMap (hi : IsDerivedSubgroup i) :
    IsClosedSubgroup (CommGroupScheme.groupHom (d.kernelTorusMap hj (i := i))) :=
  isClosedSubgroup_commutativeSubgroupIntersectionFst (d.centralizerTorus hj) i hi.1

end TitsIndexData

end Langlands.GroupScheme

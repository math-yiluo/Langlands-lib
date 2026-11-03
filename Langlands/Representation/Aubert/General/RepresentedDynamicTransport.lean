import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Dynamic normalized functors in a closed represented subgroup -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

universe u uV

namespace GroupTransport

/-- Transport the actual semidirect decomposition along a group equivalence. -/
theorem semidirectDecomposition
    {G H : Type u} [Group G] [Group H]
    {P M U : Subgroup G} {P' M' U' : Subgroup H}
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃* G)
    (hP : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hM : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hU : ∀ x : H, x ∈ U' ↔ e x ∈ U) :
    IsSemidirectDecomposition P M U := by
  have hMP : M ≤ P := by
    intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    exact (hP y).mp (h'.levi_le ((hM y).mpr hx))
  have hUP : U ≤ P := by
    intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    exact (hP y).mp (h'.unipotent_le ((hU y).mpr hx))
  refine ⟨hMP, hUP, ?_, ?_⟩
  · intro p hp x
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨y, rfl⟩ := e.surjective x
    have hn := h'.le_normalizer ((hP q).mpr hp) y
    rw [← map_mul, ← map_inv, ← map_mul]
    exact (hU y).symm.trans (hn.trans (hU (q * y * q⁻¹)))
  · apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
    intro p
    let q : P' := ⟨e.symm p, (hP _).mpr (by simp)⟩
    let m : M.subgroupOf P :=
      ⟨⟨e (h'.projection q), hMP ((hM _).mp (h'.projection q).property)⟩,
        (hM _).mp (h'.projection q).property⟩
    refine ⟨m, ?_, ?_⟩
    · change (e (h'.projection q))⁻¹ * (p : G) ∈ U
      have hm := (hU _).mp (h'.projection_inv_mul_mem q)
      simpa only [map_mul, map_inv, q, e.apply_symm_apply] using hm
    · intro n hn
      change ((n : P) : G)⁻¹ * (p : G) ∈ U at hn
      have hn' : (e.symm ((n : P) : G))⁻¹ * (q : H) ∈ U' := by
        apply (hU _).mpr
        simpa only [map_mul, map_inv, q, e.apply_symm_apply] using hn
      have hnM : ((n : P) : G) ∈ M := n.property
      have heq := (h'.projection_eq_iff q
        ⟨e.symm ((n : P) : G), (hM _).mpr (by simpa only [e.apply_symm_apply] using hnM)⟩).mpr hn'
      apply Subtype.ext
      apply Subtype.ext
      exact (e.apply_symm_apply _).symm.trans
        (congrArg (fun x : M' => e (x : H)) heq).symm

end GroupTransport

namespace RepresentedDynamicTransport

variable (R : Type u) [CommRing R] [TopologicalSpace R]
    {G L : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffine G.X.left] [IsAffine L.X.left]
    (S : SubgroupFunctor G) (j : L ⟶ G)
    (hrep : S.IsRepresentedBy j) (hc : IsClosedSubgroup j)

local instance ambientPointTopology :
    TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X

local instance representativePointTopology :
    TopologicalSpace (RationalPoint R L.X) := rationalPointTopology R L.X

local notation "test" => Over.mk (𝟙 (Spec (CommRingCat.of R)))
local notation "SP" => S.carrier test

/-- The representative's pinned point topology identifies it with the actual
subgroup of ambient identity-test points. -/
def pointEquiv : RationalPoint R L.X ≃ₜ* SP :=
  rationalPointSubgroupHomeomorph R S j hrep hc

@[simp] theorem pointEquiv_apply_coe (x : RationalPoint R L.X) :
    (pointEquiv R S j hrep hc x : RationalPoint R G.X) = x ≫ j.hom.hom := rfl

variable (ν : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ L)

/-- Actual parabolic membership is preserved, with the target read inside
the literal represented subgroup. -/
theorem parabolic_mem (x : RationalPoint R L.X) :
    x ∈ (Dynamic.parabolic ν).carrier test ↔
      pointEquiv R S j hrep hc x ∈
        ((Dynamic.parabolic (ν ≫ j)).carrier test).subgroupOf SP := by
  rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup ν j hc]
  rfl

/-- Actual Levi membership is preserved in the same subgroup topology. -/
theorem centralizer_mem (x : RationalPoint R L.X) :
    x ∈ (Dynamic.centralizer ν).carrier test ↔
      pointEquiv R S j hrep hc x ∈
        ((Dynamic.centralizer (ν ≫ j)).carrier test).subgroupOf SP := by
  rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup ν j hc]
  rfl

/-- Actual radical membership is preserved in the same subgroup topology. -/
theorem unipotent_mem (x : RationalPoint R L.X) :
    x ∈ (Dynamic.unipotent ν).carrier test ↔
      pointEquiv R S j hrep hc x ∈
        ((Dynamic.unipotent (ν ≫ j)).carrier test).subgroupOf SP := by
  rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup ν j hc]
  rfl

include hrep hc in
/-- The actual ambient dynamic subgroups, intersected with the represented
subgroup, inherit the representative's dynamic semidirect decomposition. -/
theorem insideDecomposition [IsSeparated L.X.hom] :
    IsSemidirectDecomposition
      (((Dynamic.parabolic (ν ≫ j)).carrier test).subgroupOf SP)
      (((Dynamic.centralizer (ν ≫ j)).carrier test).subgroupOf SP)
      (((Dynamic.unipotent (ν ≫ j)).carrier test).subgroupOf SP) :=
  GroupTransport.semidirectDecomposition (dynamic_isSemidirectDecomposition ν test)
    (pointEquiv R S j hrep hc).toMulEquiv
    (parabolic_mem R S j hrep hc ν) (centralizer_mem R S j hrep hc ν)
    (unipotent_mem R S j hrep hc ν)

/-- The Levi point identification is the restriction of `pointEquiv`. -/
def centralizerEquiv :
    (Dynamic.centralizer ν).carrier test ≃ₜ*
      ((Dynamic.centralizer (ν ≫ j)).carrier test).subgroupOf SP :=
  GroupTransport.subgroupEquiv (pointEquiv R S j hrep hc)
    (centralizer_mem R S j hrep hc ν)

include hrep hc in
/-- Closedness of the ambient radical gives closedness of the
representative's radical in its pinned point topology. -/
theorem unipotentClosed
    (hU : IsClosed ((Dynamic.unipotent (ν ≫ j)).carrier test :
      Set (RationalPoint R G.X))) :
    IsClosed ((Dynamic.unipotent ν).carrier test : Set (RationalPoint R L.X)) := by
  have heq : ((Dynamic.unipotent ν).carrier test : Set (RationalPoint R L.X)) =
      (pointEquiv R S j hrep hc) ⁻¹'
        (((Dynamic.unipotent (ν ≫ j)).carrier test).subgroupOf SP : Set SP) :=
    Set.ext (unipotent_mem R S j hrep hc ν)
  rw [heq]
  exact (hU.preimage continuous_subtype_val).preimage (pointEquiv R S j hrep hc).continuous

section Topology

variable [LocallyCompactSpace (RationalPoint R G.X)]
    [NonarchimedeanGroup (RationalPoint R G.X)]
    (hS : IsClosed (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :
      Set (RationalPoint R G.X)))

omit [NonarchimedeanGroup (RationalPoint R G.X)] in
include hrep hc hS in
/-- Local compactness is transported from the literal closed subgroup. -/
theorem representative_locallyCompactSpace :
    LocallyCompactSpace (RationalPoint R L.X) := by
  let : LocallyCompactSpace SP := hS.locallyCompactSpace
  exact (pointEquiv R S j hrep hc).toHomeomorph.isClosedEmbedding.locallyCompactSpace

omit [LocallyCompactSpace (RationalPoint R G.X)] in
include hrep hc in
/-- The representative's pinned topology inherits the ambient
nonarchimedean group structure through the point identification. -/
theorem representative_nonarchimedeanGroup :
    NonarchimedeanGroup (RationalPoint R L.X) := by
  let e := pointEquiv R S j hrep hc
  let : IsTopologicalGroup (RationalPoint R L.X) :=
    e.toHomeomorph.isInducing.isTopologicalGroup e.toMonoidHom
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

end Topology

section Functors

variable [LocallyCompactSpace (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))))]
    [NonarchimedeanGroup (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))))]
    [LocallyCompactSpace (RationalPoint R L.X)]
    [NonarchimedeanGroup (RationalPoint R L.X)]

variable [IsSeparated L.X.hom]
    (hU : IsClosed ((Dynamic.unipotent (ν ≫ j)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) : Set (RationalPoint R G.X)))

/-- The full-parabolic Haar-normalized induction functors agree across the
actual point homeomorphism, naturally in every inducing representation. -/
def inductionIso :
    normalizedInductionFunctor.{u, uV} (insideDecomposition R S j hrep hc ν)
        (hU.preimage continuous_subtype_val) ⋙
      SmoothRep.pullbackFunctor (pointEquiv R S j hrep hc) ≅
    SmoothRep.pullbackFunctor (centralizerEquiv R S j hrep hc ν) ⋙
      normalizedInductionFunctor (dynamic_isSemidirectDecomposition ν test)
        (unipotentClosed R S j hrep hc ν hU) :=
  GroupTransport.inductionIso (insideDecomposition R S j hrep hc ν)
    (dynamic_isSemidirectDecomposition ν test) (pointEquiv R S j hrep hc)
    (parabolic_mem R S j hrep hc ν) (centralizer_mem R S j hrep hc ν)
    (unipotent_mem R S j hrep hc ν) (hU.preimage continuous_subtype_val)
    (unipotentClosed R S j hrep hc ν hU)

/-- The normalized Jacquet functors agree across the actual point
homeomorphism, naturally in the ambient representation. -/
def jacquetIso :
    jacquetFunctor.{u, uV} (insideDecomposition R S j hrep hc ν)
        (hU.preimage continuous_subtype_val) ⋙
      SmoothRep.pullbackFunctor (centralizerEquiv R S j hrep hc ν) ≅
    SmoothRep.pullbackFunctor (pointEquiv R S j hrep hc) ⋙
      jacquetFunctor (dynamic_isSemidirectDecomposition ν test)
        (unipotentClosed R S j hrep hc ν hU) :=
  GroupTransport.jacquetIso (insideDecomposition R S j hrep hc ν)
    (dynamic_isSemidirectDecomposition ν test) (pointEquiv R S j hrep hc)
    (centralizer_mem R S j hrep hc ν) (unipotent_mem R S j hrep hc ν)
    (hU.preimage continuous_subtype_val) (unipotentClosed R S j hrep hc ν hU)

/-- The induction comparison acts by precomposition with the actual
point identification. -/
@[simp]
theorem inductionIso_hom_eval
    (A : SmoothRep.{0, u, uV} ℂ
      (((Dynamic.centralizer (ν ≫ j)).carrier test).subgroupOf SP))
    (f : (normalizedInductionFunctor (insideDecomposition R S j hrep hc ν)
      (hU.preimage continuous_subtype_val)).obj A) (y : RationalPoint R L.X) :
    Induction.eval ((Dynamic.parabolic ν).carrier test)
      (inducingRepresentation (dynamic_isSemidirectDecomposition ν test)
        (unipotentClosed R S j hrep hc ν hU)
        ((SmoothRep.pullbackFunctor (centralizerEquiv R S j hrep hc ν)).obj A))
      (SmoothRep.hom ((inductionIso R S j hrep hc ν hU).app A).hom f) y =
    Induction.eval (((Dynamic.parabolic (ν ≫ j)).carrier test).subgroupOf SP)
      (inducingRepresentation (insideDecomposition R S j hrep hc ν)
        (hU.preimage continuous_subtype_val) A) f (pointEquiv R S j hrep hc y) := rfl

/-- The Jacquet comparison retains the actual vector representative. -/
@[simp]
theorem jacquetIso_hom_mk (A : SmoothRep.{0, u, uV} ℂ SP) (v : A) :
    SmoothRep.hom ((jacquetIso R S j hrep hc ν hU).app A).hom
      (Jacquet.Localization.mk A.representation
        (((Dynamic.unipotent (ν ≫ j)).carrier test).subgroupOf SP) 1 v) =
    Jacquet.Localization.mk
      (A.representation.comp (pointEquiv R S j hrep hc).toMonoidHom)
        ((Dynamic.unipotent ν).carrier test) 1 v := rfl

/-- The compared actual normalized induced representations have finite
group-algebra length simultaneously. -/
theorem induction_hasFiniteLength_iff
    (A : SmoothRep.{0, u, uV} ℂ
      (((Dynamic.centralizer (ν ≫ j)).carrier test).subgroupOf SP)) :
    ((normalizedInductionFunctor (insideDecomposition R S j hrep hc ν)
      (hU.preimage continuous_subtype_val)).obj A).HasFiniteLength ↔
    ((normalizedInductionFunctor (dynamic_isSemidirectDecomposition ν test)
      (unipotentClosed R S j hrep hc ν hU)).obj
      ((SmoothRep.pullbackFunctor (centralizerEquiv R S j hrep hc ν)).obj A)).HasFiniteLength := by
  let I := (normalizedInductionFunctor (insideDecomposition R S j hrep hc ν)
    (hU.preimage continuous_subtype_val)).obj A
  have hpb : I.HasFiniteLength ↔
      ((SmoothRep.pullbackFunctor (pointEquiv R S j hrep hc)).obj I).HasFiniteLength :=
    FiniteLengthAssembly.finiteLength_comp_surjective_iff I.representation
      (pointEquiv R S j hrep hc).toMonoidHom (pointEquiv R S j hrep hc).surjective
  exact hpb.trans ⟨SmoothRep.hasFiniteLength_of_iso
    ((inductionIso R S j hrep hc ν hU).app A),
    SmoothRep.hasFiniteLength_of_iso ((inductionIso R S j hrep hc ν hU).app A).symm⟩

end Functors

end RepresentedDynamicTransport
end Langlands.Aubert.General

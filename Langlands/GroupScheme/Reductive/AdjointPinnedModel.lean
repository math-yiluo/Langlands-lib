import Langlands.GroupScheme.Reductive.GeometricAdjoint
import Langlands.GroupScheme.Reductive.AdjointRootSpan
import Langlands.GroupScheme.Reductive.RootKernelCenter

/-! # Integral root generation on adjoint pinned charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

/-- An equivalence of full root data preserves integral root generation. -/
theorem rootSpan_eq_top_of_equiv
    {J X Y J' X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y']
    {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
    (e : RootPairing.Equiv P Q) (h : P.rootSpan ℤ = ⊤) :
    Q.rootSpan ℤ = ⊤ := by
  have hmap : (P.rootSpan ℤ).map e.toHom.weightMap = Q.rootSpan ℤ := by
    rw [Submodule.map_span, ← Set.range_comp, e.toHom.root_weightMap,
      e.toHom.indexEquiv.surjective.range_comp]
  rw [← hmap, h, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.bijective_weightMap.surjective

/-- Field realization preserves and reflects generation by the roots
in the full integral character lattice. -/
theorem rootSpan_fieldRealization_iff
    {I J : Type u} [Fintype I] (k : Type u) [Field k]
    (P : RootDatum J (I → ℤ) (I → ℤ)) :
    (fieldRealization k P).rootSpan ℤ = ⊤ ↔ P.rootSpan ℤ = ⊤ :=
  ⟨rootSpan_eq_top_of_equiv (fieldRealizationEquiv k P).symm,
    rootSpan_eq_top_of_equiv (fieldRealizationEquiv k P)⟩

/-- Full integral root generation makes the unsaturated exponent span the
whole character group. -/
theorem rootExponentSpan_eq_top_of_rootSpan_eq_top
    {I J : Type u} [Fintype I] (P : RootDatum J (I → ℤ) (I → ℤ))
    (h : P.rootSpan ℤ = ⊤) : rootExponentSpan P = ⊤ := by
  rw [rootExponentSpan, ← Submodule.span_int_eq_addSubgroupClosure]
  change (P.rootSpan ℤ).toAddSubgroup = ⊤
  rw [h]
  rfl

end CoordinateRootDatum

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- Root generation kills the full scheme-theoretic centre over the original
ring, including central points on nonreduced test schemes. -/
theorem center_eq_bot_of_rootSpan_eq_top
    (hspan : M.rootDatum.rootSpan ℤ = ⊤) : center M.group = ⊥ := by
  have hN := CoordinateRootDatum.rootExponentSpan_eq_top_of_rootSpan_eq_top
    M.rootDatum hspan
  let Q := Diagonalizable.exponentKernelLattice M.coordinates
    (CoordinateRootDatum.rootExponentSpan M.rootDatum)
  have : Subsingleton Q := QuotientAddGroup.subsingleton_iff.mpr hN
  apply SubgroupFunctor.ext
  intro U
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 1
  rw [← M.centerKernel_isSchemeTheoreticCenter.2] at hx
  obtain ⟨z, rfl⟩ := hx
  have hz : z = 1 := by
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of M.ring) Q U).injective
    apply MonoidHom.ext
    intro m
    rw [Subsingleton.elim m 1, map_one, map_one]
  rw [hz, map_one]

/-- On every supplied field-valued fibre, adjointness is exactly integral
generation by the roots of the constant full root datum. -/
theorem isAdjoint_field_iff (k : Type u) [Field k] [Algebra M.ring k] :
    IsAdjoint ((baseChange (algebraBaseMap M.ring k)).obj M.group) ↔
      M.rootDatum.rootSpan ℤ = ⊤ := by
  let : Smooth M.group.X.hom := M.reductive.smooth
  let H := (baseChange (algebraBaseMap M.ring k)).obj M.group
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates
  let i := splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion
  let P := CoordinateRootDatum.fieldRealization k M.rootDatum
  have hH : IsConnectedReductive H := M.reductive.isConnectedReductive_algebraMap k
  have hmax : IsMaximalTorus (T := T) i :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      M.coordinates M.group M.inclusion M.maximal k
  have hP : IsRootDatumOf i P := M.fibrewiseRootDatum.field k
  have hred : P.IsReduced :=
    LocalSplitCell.fieldRealization_isReduced M.fibrewiseRootDatum.isReduced
  constructor
  · intro hadj
    exact (CoordinateRootDatum.rootSpan_fieldRealization_iff k M.rootDatum).mp
      (hadj.rootSpan_eq_top (isSplitTorus_splitTorus M.coordinates) hmax P hP hred)
  · intro hspan
    have hspanP : P.rootSpan ℤ = ⊤ :=
      (CoordinateRootDatum.rootSpan_fieldRealization_iff k M.rootDatum).mpr hspan
    have hfinite : Finite (characterLattice T ⧸ P.rootSpan ℤ) := by
      rw [hspanP]
      infer_instance
    exact ⟨(splitSemisimpleRootDatum k H hH T
      (isSplitTorus_splitTorus M.coordinates) i hmax M.rootIndex P hP).1.mpr hfinite,
      center_eq_bot_baseChange _ (M.center_eq_bot_of_rootSpan_eq_top hspan)⟩

/-- The same criterion applies to the actual residue-field fibre. -/
theorem isAdjoint_residueFiber_iff (s : M.base) :
    IsAdjoint ((baseChange (M.base.fromSpecResidueField s)).obj M.group) ↔
      M.rootDatum.rootSpan ℤ = ⊤ := by
  let k := M.base.residueField s
  let : Algebra M.ring k := (Spec.preimage (M.base.fromSpecResidueField s)).hom.toAlgebra
  have hb : algebraBaseMap M.ring k = M.base.fromSpecResidueField s := Spec.map_preimage _
  rw [← hb]
  exact M.isAdjoint_field_iff k

/-- Adjointness of any one geometric fibre of a pinned chart is the integral
root criterion on its constant full datum. -/
theorem isAdjoint_geometricFiber_iff (s : M.base) :
    IsAdjoint (geometricFiber M.group s) ↔ M.rootDatum.rootSpan ℤ = ⊤ :=
  (geometricAdjoint_iff_residueFiber M.group s).trans
    (M.isAdjoint_residueFiber_iff s)

/-- Integral root generation makes all geometric fibres adjoint, including
when the base scheme is empty. -/
theorem isFibrewiseAdjoint_of_rootSpan_eq_top
    (hspan : M.rootDatum.rootSpan ℤ = ⊤) : IsFibrewiseAdjoint M.group := by
  intro s
  exact (M.isAdjoint_geometricFiber_iff s).mpr hspan

/-- Over a nonempty base, adjoint geometric fibres are equivalent to the
constant integral root criterion. -/
theorem isFibrewiseAdjoint_iff [Nonempty M.base] :
    IsFibrewiseAdjoint M.group ↔ M.rootDatum.rootSpan ℤ = ⊤ := by
  constructor
  · intro h
    exact (M.isAdjoint_geometricFiber_iff (Classical.choice inferInstance)).mp (h _)
  · exact M.isFibrewiseAdjoint_of_rootSpan_eq_top

end AffinePinnedModel

/-- A supplied pinned affine model with full integral root generation.
Its geometric fibres are adjoint semisimple groups. -/
structure AffineAdjointPinnedModel extends AffinePinnedModel.{u} where
  rootSpan_eq_top : rootDatum.rootSpan ℤ = ⊤

namespace AffineAdjointPinnedModel

/-- The integral root criterion gives adjointness of every geometric fibre. -/
theorem isFibrewiseAdjoint (M : AffineAdjointPinnedModel.{u}) :
    IsFibrewiseAdjoint M.group :=
  M.toAffinePinnedModel.isFibrewiseAdjoint_of_rootSpan_eq_top M.rootSpan_eq_top

/-- The full scheme-theoretic centre of an adjoint pinned chart is trivial
over its original base ring. -/
theorem center_eq_bot (M : AffineAdjointPinnedModel.{u}) : center M.group = ⊥ :=
  M.toAffinePinnedModel.center_eq_bot_of_rootSpan_eq_top M.rootSpan_eq_top

end AffineAdjointPinnedModel

end Langlands.GroupScheme

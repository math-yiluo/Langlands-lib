import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.LinearAlgebra.SimplyConnectedRootDatum

/-! # Integral coroot generation on simply connected pinned charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

/-- Realizing a full coordinate root datum over a field preserves and reflects
integral generation by its coroots. -/
theorem corootSpan_fieldRealization_iff
    {I J : Type u} [Fintype I] (k : Type u) [Field k]
    (P : RootDatum J (I → ℤ) (I → ℤ)) :
    (fieldRealization k P).corootSpan ℤ = ⊤ ↔ P.corootSpan ℤ = ⊤ := by
  constructor
  · exact Langlands.LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv
      (fieldRealizationEquiv k P).symm
  · exact Langlands.LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv
      (fieldRealizationEquiv k P)

end CoordinateRootDatum

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- On every supplied field-valued fibre of a pinned affine model, algebraic
simple connectedness is precisely integral generation by the constant coroots. -/
theorem isSimplyConnected_field_iff (k : Type u) [Field k] [Algebra M.ring k] :
    IsSimplyConnected ((baseChange (algebraBaseMap M.ring k)).obj M.group) ↔
      M.rootDatum.corootSpan ℤ = ⊤ := by
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
  · intro hsc
    exact (CoordinateRootDatum.corootSpan_fieldRealization_iff k M.rootDatum).mp
      (splitSimplyConnectedCorootSpan k H hsc T
        (isSplitTorus_splitTorus M.coordinates) i hmax M.rootIndex P hP hred)
  · intro hspan
    have hspanP : P.corootSpan ℤ = ⊤ :=
      (CoordinateRootDatum.corootSpan_fieldRealization_iff k M.rootDatum).mpr hspan
    have hfinite : Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) := by
      rw [hspanP]
      infer_instance
    have hss : IsSemisimple H :=
      (splitSemisimpleRootDatum k H hH T
        (isSplitTorus_splitTorus M.coordinates) i hmax M.rootIndex P hP).2.mpr hfinite
    exact splitCorootSpanSimplyConnected k H hss T
      (isSplitTorus_splitTorus M.coordinates) i hmax M.rootIndex P hP hspanP

/-- The same coroot criterion applies to the actual residue-field fibre at
any point of the affine base. -/
theorem isSimplyConnected_residueFiber_iff (s : M.base) :
    IsSimplyConnected ((baseChange (M.base.fromSpecResidueField s)).obj M.group) ↔
      M.rootDatum.corootSpan ℤ = ⊤ := by
  let k := M.base.residueField s
  let : Algebra M.ring k := (Spec.preimage (M.base.fromSpecResidueField s)).hom.toAlgebra
  have hb : algebraBaseMap M.ring k = M.base.fromSpecResidueField s := Spec.map_preimage _
  rw [← hb]
  exact M.isSimplyConnected_field_iff k

/-- Simple connectedness of any one geometric fibre of a pinned model
is the integral coroot criterion on its constant full root datum. -/
theorem isSimplyConnected_geometricFiber_iff (s : M.base) :
    IsSimplyConnected (geometricFiber M.group s) ↔
      M.rootDatum.corootSpan ℤ = ⊤ :=
  (geometricSimplyConnected_iff_residueFiber M.group s).trans
    (M.isSimplyConnected_residueFiber_iff s)

/-- Coroot generation implies simple connectedness of every geometric fibre,
including when the base is empty. -/
theorem isFibrewiseSimplyConnected_of_corootSpan_eq_top
    (hspan : M.rootDatum.corootSpan ℤ = ⊤) :
    IsFibrewiseSimplyConnected M.group := by
  intro s
  exact (M.isSimplyConnected_geometricFiber_iff s).mpr hspan

/-- On a nonempty affine base, the fibrewise condition is equivalent to the
single constant integral coroot criterion. -/
theorem isFibrewiseSimplyConnected_iff [Nonempty M.base] :
    IsFibrewiseSimplyConnected M.group ↔ M.rootDatum.corootSpan ℤ = ⊤ := by
  constructor
  · intro h
    exact (M.isSimplyConnected_geometricFiber_iff (Classical.choice inferInstance)).mp
      (h _)
  · exact M.isFibrewiseSimplyConnected_of_corootSpan_eq_top

end AffinePinnedModel

/-- A supplied pinned affine model whose full coweight lattice is generated
integrally by the coroots. Its geometric fibres are simply connected. -/
structure AffineSimplyConnectedPinnedModel extends AffinePinnedModel.{u} where
  corootSpan_eq_top : rootDatum.corootSpan ℤ = ⊤

namespace AffineSimplyConnectedPinnedModel

/-- The geometric simple-connectedness condition follows from the stored
integral coroot criterion. -/
theorem isFibrewiseSimplyConnected (M : AffineSimplyConnectedPinnedModel.{u}) :
    IsFibrewiseSimplyConnected M.group :=
  M.toAffinePinnedModel.isFibrewiseSimplyConnected_of_corootSpan_eq_top M.corootSpan_eq_top

end AffineSimplyConnectedPinnedModel

end Langlands.GroupScheme

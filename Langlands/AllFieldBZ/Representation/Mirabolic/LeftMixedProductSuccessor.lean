import Langlands.AllFieldBZ.Representation.Derivative.MirabolicCharacter
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Mirabolic.LeftMixedProductSuccessor

/-!
# All-field port of `Langlands.Representation.Mirabolic.LeftMixedProductSuccessor`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Mirabolic.LeftMixedProductSuccessor` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedProduct
open Langlands.GeneralLinear.Mirabolic.MixedProduct
universe u

variable {R : Type u} [CommRing R] {k n : ℕ}

end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedProduct
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding blockSum rankInclusion
open Langlands.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
universe uF

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) {k n : ℕ}

/-- `ν(h) = ν(a) ν(p)` for `h ∈ leftSubgroup` with diagonal blocks `(a, p)`. -/
theorem determinantNorm_leftSubgroup (g : leftSubgroup k n F.Carrier) :
    T.determinantNorm (k + n + 1) (g : mirabolic (k + n) F.Carrier).val =
      T.determinantNorm k (leftProjection g).1 *
        T.determinantNorm (n + 1) (leftProjection g).2.val := by
  change T.normalizedAbsUnits (determinant _) =
    T.normalizedAbsUnits (determinant _) * T.normalizedAbsUnits (determinant _)
  rw [← map_mul]
  congr 1
  exact Units.ext (det_leftSubgroup g)

/-- Every coset `leftSubgroup * x` meets the Levi image of the integral group. -/
theorem quotientMap_leftSubgroup_image_levi_integralRange (k n : ℕ) :
    letI := T.valuativeRel
    Induction.quotientMap (leftSubgroup k n F.Carrier) ''
      (levi '' (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) (k + n) :
        Set (GeneralLinear (k + n) F.Carrier))) = Set.univ := by
  let := T.valuativeRel
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨κ, hκ, hup⟩ := Iwasawa.exists_mul_upperTriangular
      (ValuativeRel.valuation F.Carrier) (k + n) (projection g)
    refine ⟨levi κ⁻¹, ⟨κ⁻¹, inv_mem hκ, rfl⟩, Quotient.sound ?_⟩
    change QuotientGroup.rightRel _ (levi κ⁻¹) g
    rw [QuotientGroup.rightRel_apply, map_inv, inv_inv]
    rw [eq_radicalElement_mul_levi g, mul_assoc, ← map_mul]
    exact mul_mem (radical_mem_leftSubgroup _) (levi_mem_leftSubgroup_of_isUpperTriangular hup)

/-- The coset space `leftSubgroup k n \ P_(k+n+1)` is compact. -/
theorem compactSpace_leftQuotient (k n : ℕ) :
    letI := T.topology
    CompactSpace (Induction.LeftQuotient (leftSubgroup k n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  refine ⟨?_⟩
  rw [← T.quotientMap_leftSubgroup_image_levi_integralRange k n]
  exact ((Parabolic.isCompact_integralRange T (k + n)).image continuous_levi).image
    continuous_quotient_mk'

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
/-! ## Closed and compact projected supports -/

namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uR uG uW

variable {R : Type uR} {G : Type uG} {V : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

end Langlands.AllFieldBZ.Induction
/-! ## Vanishing of tensors -/

namespace Langlands.AllFieldBZ.MixedProductTensor
open Langlands.MixedProductTensor
open scoped TensorProduct
universe uX uY

end Langlands.AllFieldBZ.MixedProductTensor
/-! ## Determinants -/

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding blockSum rankInclusion
open Langlands.GeneralLinear.Mirabolic
universe uF

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Radical elements have determinant one. -/
theorem det_radical {n : ℕ} (u : radical n F.Carrier) :
    (u : mirabolic n F.Carrier).val.val.det = 1 := by
  have hu : (u : mirabolic n F.Carrier).val ∈ GeneralLinear.upperUnipotent (n + 1) F.Carrier :=
    radical_le_upperUnipotent u.property
  change (u : mirabolic n F.Carrier).val.val.det = 1
  rw [Matrix.det_of_isUpperTriangular hu.1]
  exact Finset.prod_eq_one fun i _ => hu.2 i

/-- Radical elements have normalized determinant norm one. -/
theorem determinantNorm_radical' {n : ℕ} (u : radical n F.Carrier) :
    T.determinantNorm (n + 1) (u : mirabolic n F.Carrier).val = 1 := by
  change T.normalizedAbsUnits (determinant _) = 1
  rw [show determinant (u : mirabolic n F.Carrier).val = 1 from Units.ext (det_radical u),
    map_one]

/-- The successor embedding keeps the normalized determinant norm. -/
theorem determinantNorm_successor {n : ℕ} (h : mirabolic n F.Carrier) :
    T.determinantNorm (n + 1 + 1) (successor h).val = T.determinantNorm (n + 1) h.val := by
  have hdet : determinant (successor h).val = determinant h.val := by
    apply Units.ext
    change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks h.val.val 0 0 (1 : Langlands.GeneralLinear 1 F.Carrier).val)) =
        Matrix.det h.val.val
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one, Matrix.det_one,
      mul_one]
  change T.normalizedAbsUnits (determinant (successor h).val) =
    T.normalizedAbsUnits (determinant h.val)
  rw [hdet]

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

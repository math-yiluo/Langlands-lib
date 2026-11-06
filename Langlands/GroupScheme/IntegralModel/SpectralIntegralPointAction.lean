import Langlands.GroupScheme.IntegralModel.IntegralPointAutomorphisms
import Langlands.GroupScheme.AlgebraicGaloisPointDescent
import Langlands.Galois.Local.AbsoluteDefinitions

/-! # The actual Galois action on an extended original integral image -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LocalGalois GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)
  (L : Type u) [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

private instance spectralExtendsCanonical :
    (ValuativeRel.valuation F).HasExtension (spectralValuation F L) where
  val_isEquiv_comap x y := by
    change ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y ↔
      spectralNorm F L (algebraMap F L x) ≤
        spectralNorm F L (algebraMap F L y)
    simp only [spectralNorm_extends]
    exact (localNormedField_le F x y).symm

local instance : Algebra ↥𝒪[F] (extensionIntegers F L) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := spectralValuation F L)

local instance : IsScalarTower ↥𝒪[F] (extensionIntegers F L) L :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := spectralValuation F L)

/-- Base change of the supplied model to the actual spectral integer ring of
an arbitrary algebraic extension of the local field. -/
def baseChangeSpectral :
    IntegralModel (extensionIntegers F L) L (baseChanged F L G) :=
  M.baseChange (extensionIntegers F L) L

private theorem mem_spectralIntegerRange (x : L) :
    x ∈ Set.range (algebraMap (extensionIntegers F L) L) ↔
      spectralValuation F L x ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Every base-field coefficient automorphism preserves and reflects the
actual extended integer ring, without a separate preservation assumption. -/
theorem spectralIntegerRange_conjugate_iff (σ : L ≃ₐ[F] L) (x : L) :
    σ x ∈ Set.range (algebraMap (extensionIntegers F L) L) ↔
      x ∈ Set.range (algebraMap (extensionIntegers F L) L) := by
  rw [mem_spectralIntegerRange, mem_spectralIntegerRange]
  have h : spectralValuation F L (σ x) = spectralValuation F L x :=
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  rw [h]

/-- The actual coefficient Galois group acts by multiplicative automorphisms
of the original-model image after spectral integer base change. -/
def spectralIntegralPointAction :
    (L ≃ₐ[F] L) →* MulAut (M.baseChangeSpectral L).integralPoints where
  toFun σ := M.baseChangeIntegralPointAut (extensionIntegers F L) L σ
    (spectralIntegerRange_conjugate_iff L σ)
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact rationalConjugate_one F L G g.val
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact rationalConjugate_mul F L G σ τ g.val

@[simp] theorem spectralIntegralPointAction_coe (σ : L ≃ₐ[F] L)
    (g : (M.baseChangeSpectral L).integralPoints) :
    (M.spectralIntegralPointAction L σ g : rationalPoints (baseChanged F L G)) =
      rationalConjugate F L G σ g := rfl

/-- The actual scalar intersection needed to descend the original integral
image is automatic for the spectral extension. -/
theorem spectralIntegerRange_intersection (x : F) :
    algebraMap F L x ∈ Set.range (algebraMap (extensionIntegers F L) L) ↔
      x ∈ Set.range (algebraMap ↥𝒪[F] F) := by
  rw [mem_spectralIntegerRange,
    Valuation.HasExtension.val_map_le_one_iff (ValuativeRel.valuation F)
      (spectralValuation F L)]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact a.property

/-- Rational extension preserves and reflects the supplied original image. -/
theorem mem_integralPoints_rationalExtend_iff_spectral
    (g : rationalPoints G) :
    rationalExtend F L G g ∈ (M.baseChangeSpectral L).integralPoints ↔
      g ∈ M.integralPoints :=
  M.mem_integralPoints_rationalExtend_iff (extensionIntegers F L) L
    (spectralIntegerRange_intersection L) g

/-- Fixed points of the actual coefficient action on the extended integral image. -/
def spectralIntegralFixedSubgroup :
    Subgroup (M.baseChangeSpectral L).integralPoints where
  carrier := {g | ∀ σ : L ≃ₐ[F] L, M.spectralIntegralPointAction L σ g = g}
  one_mem' σ := map_one _
  mul_mem' hg hh σ := by rw [map_mul, hg σ, hh σ]
  inv_mem' hg σ := by rw [map_inv, hg σ]

/-- An integral point fixed by this action is fixed on the existing coefficient carrier. -/
def spectralIntegralFixedCoefficient (g : M.spectralIntegralFixedSubgroup L) :
    GaloisPoint.fixedSubgroup F L G :=
  ⟨baseChangeCoeffEquiv F L G g.val.val, fun σ => by
    have h := congrArg
      (fun z : (M.baseChangeSpectral L).integralPoints =>
        baseChangeCoeffEquiv F L G z.val) (g.property σ)
    simpa only [spectralIntegralPointAction_coe,
      baseChangeCoeffEquiv_rationalConjugate] using h⟩

include M in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem genericAffineFromSuppliedModel : IsAffine G.X.left := by
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let : IsAffine M.genericFibre.X.left := by
    change IsAffine
      (CategoryTheory.Limits.pullback M.group.X.hom (Spec.algebraMap ↥𝒪[F] F))
    infer_instance
  exact IsAffine.of_isIso M.genericIso.inv.hom.hom.left

/-- Extend an original integral-image point to an actual fixed integral-image point. -/
def spectralIntegralFixedExtend :
    M.integralPoints →* M.spectralIntegralFixedSubgroup L where
  toFun g := ⟨⟨rationalExtend F L G g.val,
    (M.mem_integralPoints_rationalExtend_iff_spectral L g.val).mpr g.property⟩,
    fun σ => by
      apply Subtype.ext
      apply (baseChangeCoeffEquiv F L G).injective
      simp only [spectralIntegralPointAction_coe,
        baseChangeCoeffEquiv_rationalConjugate, baseChangeCoeffEquiv_rationalExtend,
        GaloisPoint.conjugate_extend]⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' g h := Subtype.ext (Subtype.ext (map_mul _ g.val h.val))

variable [IsGalois F L]

/-- Descend a fixed extended integral point to the original integral image. -/
def spectralIntegralDescend (g : M.spectralIntegralFixedSubgroup L) :
    M.integralPoints := by
  let : IsAffine G.X.left := M.genericAffineFromSuppliedModel
  let p := (GaloisPoint.algebraicFixedEquiv F L G).symm
    (M.spectralIntegralFixedCoefficient L g)
  let q := (rationalCoeffEquiv F G).symm p
  have hq : rationalExtend F L G q = g.val.val := by
    apply (baseChangeCoeffEquiv F L G).injective
    rw [baseChangeCoeffEquiv_rationalExtend]
    change GaloisPoint.extend F L G
      ((rationalCoeffEquiv F G) ((rationalCoeffEquiv F G).symm p)) = _
    rw [MulEquiv.apply_symm_apply]
    exact GaloisPoint.extend_algebraicFixedEquiv_symm F L G
      (M.spectralIntegralFixedCoefficient L g)
  exact ⟨q, (M.mem_integralPoints_rationalExtend_iff_spectral L q).mp
    (hq.symm ▸ g.val.property)⟩

@[simp] theorem rationalExtend_spectralIntegralDescend
    (g : M.spectralIntegralFixedSubgroup L) :
    rationalExtend F L G (M.spectralIntegralDescend L g).val = g.val.val := by
  let : IsAffine G.X.left := M.genericAffineFromSuppliedModel
  apply (baseChangeCoeffEquiv F L G).injective
  rw [baseChangeCoeffEquiv_rationalExtend]
  change GaloisPoint.extend F L G
    ((rationalCoeffEquiv F G) ((rationalCoeffEquiv F G).symm _)) = _
  rw [MulEquiv.apply_symm_apply]
  exact GaloisPoint.extend_algebraicFixedEquiv_symm F L G
    (M.spectralIntegralFixedCoefficient L g)

/-- The original integral image is the fixed subgroup of the actual extended
integral image for an arbitrary, possibly infinite, Galois extension. -/
def spectralIntegralFixedEquiv :
    M.integralPoints ≃* M.spectralIntegralFixedSubgroup L where
  toFun := M.spectralIntegralFixedExtend L
  invFun := M.spectralIntegralDescend L
  left_inv g := by
    let : IsAffine G.X.left := M.genericAffineFromSuppliedModel
    apply Subtype.ext
    apply (rationalCoeffEquiv F G).injective
    apply GaloisPoint.extend_injective F L G
    have h : rationalExtend F L G
        (M.spectralIntegralDescend L (M.spectralIntegralFixedExtend L g)).val =
          rationalExtend F L G g.val :=
      M.rationalExtend_spectralIntegralDescend L (M.spectralIntegralFixedExtend L g)
    simpa only [baseChangeCoeffEquiv_rationalExtend] using
      congrArg (baseChangeCoeffEquiv F L G) h
  right_inv g := Subtype.ext (Subtype.ext
    (M.rationalExtend_spectralIntegralDescend L g))
  map_mul' := map_mul (M.spectralIntegralFixedExtend L)

@[simp] theorem spectralIntegralFixedEquiv_coe (g : M.integralPoints) :
    (M.spectralIntegralFixedEquiv L g).val.val =
      rationalExtend F L G g.val := rfl

end Langlands.GroupScheme.IntegralModel

import Langlands.Geometry.FormalGroup.HarrisCharacterKernel
import Langlands.GroupScheme.FiniteAlgebraRightRegularAffine
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters

/-! # The actual character quotient and its two valuation coordinates -/

noncomputable section
universe u

namespace Langlands.FormalGroup.Harris

open _root_.AlgebraicGeometry CategoryTheory Opposite MulOpposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Shimura.LocalDivision Langlands.CentralDivision ValuativeRel
open scoped CategoryTheory.MonObj TensorProduct WithZero

variable {k B : Type u} [Field k] {n : ℕ}

private theorem rationalDetEval
    (x : rationalPoints (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k))) :
    rationalCharacterEval (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of k)) x =
      Matrix.GeneralLinearGroup.det (GeneralLinear.affinePointsEquiv (Fin n)
        (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) k)
        (GaloisPointComparison.rationalCoeffEquiv k _ x)) := by
  rw [rationalCharacterEval_eq_affineUnitsEquiv,
    ← GaloisPointComparison.rationalCoeffEquiv_eq]
  let S := CommAlgCat.of (CommRingCat.of k) k
  let G := GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)
  let y := GaloisPointComparison.rationalCoeffEquiv k G x
  have h := GeneralLinear.characterOnAffineMatrices_determinantCharacter S
    (GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of k) S y)
  change Gm.affineUnitsEquiv (CommRingCat.of k) S
    (((GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of k) S).symm
      (GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of k) S y)) ≫
        (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of k)).toMul.hom.hom) = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

section Ring

variable [Ring B] [Algebra k B] (b : Module.Basis (Fin n) k Bᵐᵒᵖ)

private theorem rightRegularUnits_det_opposite (v : (k ⊗[k] Bᵐᵒᵖ)ˣ) :
    (Matrix.GeneralLinearGroup.det (FiniteAlgebraUnits.rightRegularUnits b k v) : k) =
      Algebra.norm k (unop (Algebra.TensorProduct.lid k Bᵐᵒᵖ (↑v⁻¹ : k ⊗[k] Bᵐᵒᵖ))) := by
  let a : k ⊗[k] Bᵐᵒᵖ := ↑v⁻¹
  let l := Algebra.TensorProduct.lid k Bᵐᵒᵖ
  let e : k ⊗[k] Bᵐᵒᵖ ≃ₗ[k] B := l.toLinearEquiv.trans (opLinearEquiv k).symm
  change (FiniteAlgebraUnits.rightMulMatrix b k a).det = Algebra.norm k (e a)
  rw [FiniteAlgebraUnits.rightMulMatrix, LinearMap.det_toMatrix, Algebra.norm_apply]
  have h : (e : _ →ₗ[k] _) ∘ₗ LinearMap.mulRight k a ∘ₗ (e.symm : _ →ₗ[k] _) =
      Algebra.lmul k B (e a) := by
    apply LinearMap.ext
    intro x
    change e (e.symm x * a) = e a * x
    calc
      _ = e a * e (e.symm x) := by
        change unop (l (e.symm x * a)) = unop (l a) * unop (l (e.symm x))
        rw [map_mul, unop_mul]
      _ = e a * x := by rw [e.apply_symm_apply]
  rw [← h, LinearMap.det_conj]

/-- The regular determinant character measures the scalar-field norm of the inverse
of the opposite coordinate, taken in the original algebra. -/
theorem rationalCharacterEval_splitRegularDeterminant
    (x : rationalPoints (splitGroupScheme b)) :
    (rationalCharacterEval (splitRegularDeterminantCharacter b) x : k) =
      Algebra.norm k (unop (↑((splitSimilitudeCoordinates k B
        (splitGroupRationalPointsEquiv b x)).1⁻¹) : Bᵐᵒᵖ)) := by
  let U := FiniteAlgebraUnits.groupScheme b
  let V := (Gm (Spec (CommRingCat.of k))).toGrp
  let y : rationalPoints U := x ≫ fst U.X V.X
  let ρ := FiniteAlgebraUnits.rightRegularRepresentation b
  have hcoord : (splitSimilitudeCoordinates k B (splitGroupRationalPointsEquiv b x)).1 =
      FiniteAlgebraUnits.rationalPointsEquiv b y := by
    simp only [splitGroupRationalPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [hcoord, splitRegularDeterminantCharacter, rationalCharacterEval_characterRestrict]
  have hmap : rationalPoints.map (fst U V ≫ ρ) x = rationalPoints.map ρ y := by
    change x ≫ fst U.X V.X ≫ ρ.hom.hom = (x ≫ fst U.X V.X) ≫ ρ.hom.hom
    rw [Category.assoc]
  rw [hmap, rationalDetEval, GaloisPointComparison.rationalCoeffEquiv_map]
  change (Matrix.GeneralLinearGroup.det (ρ.affineMatrix _
    (GaloisPointComparison.rationalCoeffEquiv k U y)) : k) = _
  rw [FiniteAlgebraUnits.affineMatrix_rightRegularRepresentation,
    rightRegularUnits_det_opposite]
  rfl

end Ring

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [DivisionRing B] [Algebra k B] (b : Module.Basis (Fin n) k Bᵐᵒᵖ)

local instance : NontriviallyNormedField k := LocalGalois.localNormedField k
local instance : CompleteSpace k := LocalGalois.localNormedField_complete k
local instance : IsUltrametricDist k := LocalGalois.localNormedField_ultrametric k

instance splitRationalCharacterKernel_normal : (splitRationalCharacterKernel b).Normal := by
  unfold splitRationalCharacterKernel
  exact Subgroup.normal_iInf_normal fun _ => inferInstance

/-- The quotient of actual split similitudes by the common character kernel in (A.2). -/
abbrev CharacterComponentGroup :=
  (splitInvolution k B).similitudes ⧸ splitRationalCharacterKernel b

private theorem norm_one_of_splitRegularDeterminant {g : (splitInvolution k B).similitudes}
    (hg : g ∈ splitRationalCharacterKernel b) :
    ‖Algebra.norm k (unop (↑((splitSimilitudeCoordinates k B g).1⁻¹) : Bᵐᵒᵖ))‖ = 1 := by
  have h := (mem_splitRationalCharacterKernel_iff b g).mp hg (splitRegularDeterminantCharacter b)
  rw [rationalCharacterEval_splitRegularDeterminant, MulEquiv.apply_symm_apply] at h
  exact h

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] [Algebra k F] [Algebra F B] [IsScalarTower k F B]
variable [FiniteDimensional F B] [TopologicalSpace B] [IsModuleTopology F B]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F

private theorem splitRationalCharacterKernel_le_integerUnits (hkF : Continuous (algebraMap k F)) :
    splitRationalCharacterKernel b ≤ splitIntegerUnits k F B := by
  let : T2Space B := t2Space_of_isModuleTopology F B
  let : IsTopologicalAddGroup B := IsModuleTopology.isTopologicalAddGroup F B
  let : FiniteDimensional k B := Module.Finite.of_basis (b.map (opLinearEquiv k).symm)
  have hsmul : ContinuousSMul k B := ⟨by
    have h := (continuous_smul (M := F) (X := B)).comp
      ((hkF.comp continuous_fst).prodMk continuous_snd)
    convert h using 1
    funext p
    exact (algebraMap_smul F p.1 p.2).symm⟩
  let : IsModuleTopology k B := isModuleTopologyOfFiniteDimensional
  have hcompact := le_maximalCompactLevel_of_isCompact F B
    (maximalCompactLevel k B).subgroup (maximalCompactLevel k B).isCompact
  intro g hg
  let d := (splitSimilitudeCoordinates k B g).1
  let e := (splitSimilitudeCoordinates k B g).2
  let a := (Units.opEquiv d).unop
  have hdet_inv : ‖Algebra.norm k (↑a⁻¹ : B)‖ = 1 :=
    norm_one_of_splitRegularDeterminant b hg
  have hdet : ‖Algebra.norm k (a : B)‖ = 1 := by
    have h := norm_one_of_splitRegularDeterminant b ((splitRationalCharacterKernel b).inv_mem hg)
    rw [map_inv] at h
    change ‖Algebra.norm k (unop (↑((d⁻¹)⁻¹) : Bᵐᵒᵖ))‖ = 1 at h
    rw [inv_inv] at h
    exact h
  have hnorm (x : B) (hx : ‖Algebra.norm k x‖ = 1) : regularAbsoluteValue k B x ≤ 1 := by
    rw [← map_one (regularAbsoluteValue k B), regularAbsoluteValue_le_iff,
      map_one, norm_one, hx]
  have hmult : e ∈ (integerRing k k).toSubmonoid.units := by
    have h : rationalCharacterEval (splitMultiplierCharacter b)
        ((splitGroupRationalPointsEquiv b).symm g) ∈ (integerRing k k).toSubmonoid.units :=
      (Subgroup.mem_iInf.mp hg) (splitMultiplierCharacter b)
    rw [rationalCharacterEval_splitMultiplier, MulEquiv.apply_symm_apply] at h
    exact h
  change a ∈ (maximalCompactLevel F B).subgroup ∧ e ∈ (integerRing k k).toSubmonoid.units
  exact ⟨hcompact (⟨hnorm _ hdet, hnorm _ hdet_inv⟩ :
    a ∈ (maximalCompactLevel k B).subgroup), hmult⟩

/-- The actual common character kernel consists exactly of the two integral unit coordinates. -/
theorem splitRationalCharacterKernel_eq_integerUnits (hkF : Continuous (algebraMap k F)) :
    splitRationalCharacterKernel b = splitIntegerUnits k F B := by
  apply le_antisymm
  · exact splitRationalCharacterKernel_le_integerUnits b F hkF
  · exact splitIntegerUnits_le_splitRationalCharacterKernel F b hkF

variable [Algebra.IsCentral F B]

/-- The actual component quotient in (A.2) is the quotient by the two local valuation orders. -/
def characterComponentValuationEquiv (hkF : Continuous (algebraMap k F)) :
    CharacterComponentGroup b ≃*
      (splitInvolution k B).similitudes ⧸ (localSplitValuationCoordinates k F B).ker :=
  QuotientGroup.quotientMulEquivOfEq
    ((splitRationalCharacterKernel_eq_integerUnits b F hkF).trans
      (localSplitValuationCoordinates_ker k F B).symm)

@[simp]
theorem characterComponentValuationEquiv_mk (hkF : Continuous (algebraMap k F))
    (g : (splitInvolution k B).similitudes) :
    characterComponentValuationEquiv b F hkF (QuotientGroup.mk g) = QuotientGroup.mk g :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

variable (hkF : Continuous (algebraMap k F))
variable (uniformizer : (Bᵐᵒᵖ)ˣ) (p : kˣ)
variable (hUniformizer :
  oppositeUnitOrder (localReducedNormIntValuation F B) uniformizer = Multiplicative.ofAdd (1 : ℤ))
variable (hp : valuationUnitOrder (Langlands.FML.normalizedMultiplicativeValuation k) p = Multiplicative.ofAdd (1 : ℤ))

/-- Units of order one exhibit the actual character quotient as two integer coordinates. -/
def characterComponentCoordinates : CharacterComponentGroup b ≃*
    Multiplicative ℤ × Multiplicative ℤ :=
  (characterComponentValuationEquiv b F hkF).trans
    (valuationComponentEquiv k B (localReducedNormIntValuation F B) (Langlands.FML.normalizedMultiplicativeValuation k)
      uniformizer p hUniformizer hp)

@[simp]
theorem characterComponentCoordinates_mk (g : (splitInvolution k B).similitudes) :
    characterComponentCoordinates b F hkF uniformizer p hUniformizer hp (QuotientGroup.mk g) =
      localSplitValuationCoordinates k F B g := rfl

/-- Translation by the component of (A.3) adds one to the opposite order and `f`
to the scalar order. -/
theorem characterComponentCoordinates_mul_weil (x : CharacterComponentGroup b) (f : ℕ) :
    characterComponentCoordinates b F hkF uniformizer p hUniformizer hp
        (x * QuotientGroup.mk (weilComponentElement k B uniformizer p f)) =
      characterComponentCoordinates b F hkF uniformizer p hUniformizer hp x *
        (Multiplicative.ofAdd (1 : ℤ), Multiplicative.ofAdd (f : ℤ)) := by
  rw [map_mul, characterComponentCoordinates_mk]
  have h := splitValuationCoordinates_weil k B (localReducedNormIntValuation F B)
    (Langlands.FML.normalizedMultiplicativeValuation k) uniformizer p hUniformizer hp 1 f
  simpa only [one_mul, map_one, localSplitValuationCoordinates] using congrArg
    (fun z => characterComponentCoordinates b F hkF uniformizer p hUniformizer hp x * z) h

/-- Translation by the component of (A.6) adds the negative determinant order
to the opposite order and preserves the scalar order. -/
theorem characterComponentCoordinates_mul_determinant (x : CharacterComponentGroup b)
    (detOrder : ℤ) :
    characterComponentCoordinates b F hkF uniformizer p hUniformizer hp
        (x * QuotientGroup.mk (determinantComponentElement k B uniformizer detOrder)) =
      characterComponentCoordinates b F hkF uniformizer p hUniformizer hp x *
        (Multiplicative.ofAdd (-detOrder), 1) := by
  rw [map_mul, characterComponentCoordinates_mk]
  have h := splitValuationCoordinates_determinant k B (localReducedNormIntValuation F B)
    (Langlands.FML.normalizedMultiplicativeValuation k) uniformizer hUniformizer 1 detOrder
  simpa only [one_mul, map_one, localSplitValuationCoordinates] using congrArg
    (fun z => characterComponentCoordinates b F hkF uniformizer p hUniformizer hp x * z) h

end LocalField
end Langlands.FormalGroup.Harris

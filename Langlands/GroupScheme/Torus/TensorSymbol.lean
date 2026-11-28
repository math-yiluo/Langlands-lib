import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Torus.PointsTensor
import Langlands.GroupTheory.CocycleExtensionCommutator
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Tensor symbol cocycle of a split torus -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct commutatorElement

namespace Langlands.GroupScheme.TorusSymbol

variable {F : Type u} [Field F] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {A : Type v} [CommGroup A]

local notation "Y" => cocharacterLattice T
local notation "Points" => rationalPoints T.toGrp
set_option hygiene false in
local notation "R" => ULift.{u} ℤ
local notation "base" => 𝟙 (Spec (CommRingCat.of F))

/-- Evaluate the actual cocharacter at a field unit. -/
def cocharacterPoint (y : Y) : Fˣ →* Points :=
  (rationalPoints.map (CommGroupScheme.groupHom y)).comp
    (Gm.affinePointsEquiv base).symm.toMonoidHom

/-- Cocharacter evaluation identifies the unit-lattice tensor product with rational points. -/
def unitsTensorPointEquiv (hT : IsSplitTorus T.toGrp) :
    Additive Fˣ ⊗[R] Y ≃ₗ[R] Additive Points :=
  (TensorProduct.congr
    ((Gm.affinePointsEquiv base).symm.toAdditive.toIntLinearEquiv.restrictScalars R)
    (LinearEquiv.refl R Y)).trans (TorusPointsTensor.tensorPointEquiv F T hT (Over.mk base))

@[simp] theorem unitsTensorPointEquiv_tmul (hT : IsSplitTorus T.toGrp) (a : Fˣ) (y : Y) :
    unitsTensorPointEquiv hT (Additive.ofMul a ⊗ₜ[R] y) = Additive.ofMul (cocharacterPoint y a) :=
  rfl

private def linearPairing (h : Fˣ →* Fˣ →* A) :
    Additive Fˣ →ₗ[R] Additive Fˣ →ₗ[R] Additive A :=
  let linearize : Additive (Fˣ →* A) →+ (Additive Fˣ →ₗ[R] Additive A) :=
    { toFun f := f.toMul.toAdditive.toIntLinearMap.restrictScalars R
      map_zero' := LinearMap.ext fun _ => rfl
      map_add' _ _ := LinearMap.ext fun _ => rfl }
  (linearize.comp h.toAdditive).toIntLinearMap.restrictScalars R

private def liftedForm (D : Y →ₗ[ℤ] Y →ₗ[ℤ] ℤ) : Y →ₗ[R] Y →ₗ[R] R :=
  LinearMap.mk₂ R (fun y z => ULift.up (D y z))
    (fun y y' z => ULift.ext (LinearMap.congr_fun (D.map_add y y') z))
    (fun n y z => ULift.ext (LinearMap.congr_fun (D.map_smul n.down y) z))
    (fun y z z' => ULift.ext ((D y).map_add z z'))
    (fun n y z => ULift.ext ((D y).map_smul n.down z))

variable (hT : IsSplitTorus T.toGrp)
  (D : cocharacterLattice T →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ) (h : Fˣ →* Fˣ →* A)

private def symbolTensor : (Additive Fˣ ⊗[R] Y) ⊗[R] (Additive Fˣ ⊗[R] Y) →ₗ[R] Additive A :=
  let pairUnits : Additive Fˣ ⊗[R] Additive Fˣ →ₗ[R] Additive A :=
    TensorProduct.lift (linearPairing h)
  let pairLattice : Y ⊗[R] Y →ₗ[R] R :=
    TensorProduct.lift (liftedForm (F := F) (T := T) D)
  let regroup := TensorProduct.tensorTensorTensorComm R (Additive Fˣ) Y (Additive Fˣ) Y
  (TensorProduct.rid R (Additive A)).toLinearMap ∘ₗ
    TensorProduct.map pairUnits pairLattice ∘ₗ regroup.toLinearMap

/-- The tensor symbol on actual rational points, with values in the coefficient group. -/
def symbol (x z : Points) : A :=
  let e := (unitsTensorPointEquiv hT).symm
  (symbolTensor (T := T) D h (e (Additive.ofMul x) ⊗ₜ[R] e (Additive.ofMul z))).toMul

theorem symbol_mul_left (x x' z : Points) :
    symbol hT D h (x * x') z = symbol hT D h x z * symbol hT D h x' z := by
  simp only [symbol, ← toMul_add, ofMul_mul, map_add, TensorProduct.add_tmul]

theorem symbol_mul_right (x z z' : Points) :
    symbol hT D h x (z * z') = symbol hT D h x z * symbol hT D h x z' := by
  simp only [symbol, ← toMul_add, ofMul_mul, map_add, TensorProduct.tmul_add]

@[simp] theorem symbol_one_left (z : Points) : symbol hT D h 1 z = 1 := by
  simp only [symbol, ofMul_one, map_zero, TensorProduct.zero_tmul, toMul_zero]

@[simp] theorem symbol_one_right (x : Points) : symbol hT D h x 1 = 1 := by
  simp only [symbol, ofMul_one, map_zero, TensorProduct.tmul_zero, toMul_zero]

@[simp] theorem symbol_cocharacterPoint (y z : Y) (a b : Fˣ) :
    symbol hT D h (cocharacterPoint y a) (cocharacterPoint z b) = h a b ^ D y z := by
  rw [symbol, ← unitsTensorPointEquiv_tmul hT a y, ← unitsTensorPointEquiv_tmul hT b z]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

/-- The point group acts trivially on the coefficient group. -/
@[instance_reducible] def coefficientAction (G A : Type*) [Monoid G] [Monoid A] :
    MulDistribMulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

attribute [local instance] coefficientAction

/-- The tensor symbol is a normalized multiplicative two-cocycle for the trivial action. -/
def normalizedCocycle : NormalizedTwoCocycle Points A where
  toFun p := symbol hT D h p.1 p.2
  normalized := symbol_one_left hT D h 1
  cocycle x y z := by
    change symbol hT D h (x * y) z * symbol hT D h x y =
      symbol hT D h y z * symbol hT D h x (y * z)
    rw [symbol_mul_left, symbol_mul_right]
    ac_rfl

/-- The central extension of the actual point group defined by the tensor symbol. -/
abbrev Extension := (normalizedCocycle hT D h).Extension

/-- The coefficient inclusion. -/
def inclusion : A →* Extension hT D h :=
  NormalizedTwoCocycle.Extension.inl (normalizedCocycle hT D h)

/-- The projection to actual rational points. -/
def projection : Extension hT D h →* Points :=
  NormalizedTwoCocycle.Extension.projection (normalizedCocycle hT D h)

/-- The distinguished section on actual rational points. -/
def sectionMap (x : Points) : Extension hT D h :=
  NormalizedTwoCocycle.Extension.sectionMap (normalizedCocycle hT D h) x

@[simp] theorem projection_sectionMap (x : Points) :
    projection hT D h (sectionMap hT D h x) = x :=
  rfl

@[simp] theorem projection_inclusion (a : A) :
    projection hT D h (inclusion hT D h a) = 1 :=
  rfl

theorem inclusion_injective : Function.Injective (inclusion hT D h) :=
  NormalizedTwoCocycle.Extension.inl_injective (normalizedCocycle hT D h)

theorem projection_surjective : Function.Surjective (projection hT D h) :=
  NormalizedTwoCocycle.Extension.projection_surjective (normalizedCocycle hT D h)

theorem range_inclusion_eq_ker_projection :
    (inclusion hT D h).range = (projection hT D h).ker :=
  NormalizedTwoCocycle.Extension.range_inl_eq_ker_projection (normalizedCocycle hT D h)

theorem inclusion_central (a : A) (e : Extension hT D h) :
    Commute (inclusion hT D h a) e :=
  (NormalizedTwoCocycle.Extension.mul_inl (normalizedCocycle hT D h) e a).symm

theorem sectionMap_mul (x z : Points) :
    sectionMap hT D h x * sectionMap hT D h z =
      inclusion hT D h (symbol hT D h x z) * sectionMap hT D h (x * z) :=
  NormalizedTwoCocycle.Extension.sectionMap_mul (normalizedCocycle hT D h) x z

/-- For a skew pairing, the commutator on cocharacter points has the symmetric exponent. -/
theorem commutator_cocharacterPoint (hswap : ∀ a b : Fˣ, h b a = (h a b)⁻¹)
    (y z : Y) (a b : Fˣ) (e f : Extension hT D h)
    (he : projection hT D h e = cocharacterPoint y a)
    (hf : projection hT D h f = cocharacterPoint z b) :
    ⁅e, f⁆ = inclusion hT D h (h a b ^ (D y z + D z y)) := by
  have hc := NormalizedTwoCocycle.Extension.commutator_eq_inl_div
    (normalizedCocycle hT D h) (fun _ _ => rfl) e f
  change ⁅e, f⁆ = inclusion hT D h
    (symbol hT D h (projection hT D h e) (projection hT D h f) /
      symbol hT D h (projection hT D h f) (projection hT D h e)) at hc
  simp only [he, hf, symbol_cocharacterPoint] at hc
  rw [hc, hswap a b, inv_zpow, div_inv_eq_mul, ← zpow_add]

end Langlands.GroupScheme.TorusSymbol

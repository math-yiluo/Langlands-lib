import Langlands.Global.AdelicBlockParabolic
import Langlands.Global.HeckeCharacterFiniteOrder
import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Group.GL.BlockDeterminant
import Langlands.Representation.Induction.Definitions

/-!
# Actual adelic block characters from Hecke characters

The character is the product of the supplied block determinant characters.
Its central weight is an actual Hecke character, with block-rank exponents.
-/

noncomputable section

universe uF

namespace Langlands.Global.AdelicBlockHeckeCharacter

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- The actual product of the supplied block determinant Hecke characters. -/
def leviCharacter (χ : Fin B.length → HeckeCharacter F) : FullLevi F B →ₜ* ℂˣ where
  toFun m := ∏ i, (χ i).adelicDeterminant (B.size i) (m i)
  map_one' := by simp
  map_mul' m k := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  continuous_toFun := continuous_finsetProd _ fun i _ =>
    ((χ i).adelicDeterminant (B.size i)).continuous.comp (continuous_apply i)

@[simp]
theorem leviCharacter_apply (χ : Fin B.length → HeckeCharacter F) (m : FullLevi F B) :
    leviCharacter F B χ m = ∏ i, (χ i).adelicDeterminant (B.size i) (m i) := rfl

/-- The central character retains the actual rank of every block. -/
def centralCharacter (χ : Fin B.length → HeckeCharacter F) : HeckeCharacter F :=
  ∏ i, χ i ^ B.size i

@[simp]
theorem leviCharacter_scalar (χ : Fin B.length → HeckeCharacter F) (z : Ideles F) :
    leviCharacter F B χ (fun i => AdelicGL.scalar F (B.size i) z) =
      (centralCharacter F B χ).onIdeles z := by
  classical
  have heval (S : Finset (Fin B.length)) :
      (∏ i ∈ S, χ i ^ B.size i) (ideleClassMap F z) =
        ∏ i ∈ S, (χ i (ideleClassMap F z)) ^ B.size i := by
    induction S using Finset.induction_on with
    | empty => rfl
    | @insert i S hi hS =>
      simp only [Finset.prod_insert hi, ContinuousMonoidHom.mul_apply,
        ContinuousMonoidHom.pow_apply, hS]
  change (∏ i, (χ i).onIdeles (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin (B.size i)) z))) =
      (∏ i, χ i ^ B.size i) (ideleClassMap F z)
  rw [heval]
  simp [Matrix.GeneralLinearGroup.det_scalar, HeckeCharacter.onIdeles]

@[simp]
theorem leviCharacter_rational (χ : Fin B.length → HeckeCharacter F) (m : B.Levi F) :
    leviCharacter F B χ (fun i => AdelicGL.rational F (B.size i) (m i)) = 1 := by
  simp only [leviCharacter_apply, HeckeCharacter.adelicDeterminant_rational,
    Finset.prod_const_one]

/-- Restriction to the actual finite Levi factor. -/
def finiteLeviCharacter (χ : Fin B.length → HeckeCharacter F) : FiniteLevi F B →ₜ* ℂˣ :=
  (leviCharacter F B χ).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (leviSplit F B).symm).comp
      (ContinuousMonoidHom.inr _ _))

/-- Restriction to the actual archimedean Levi factor. -/
def infiniteLeviCharacter (χ : Fin B.length → HeckeCharacter F) : InfiniteLevi F B →ₜ* ℂˣ :=
  (leviCharacter F B χ).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (leviSplit F B).symm).comp
      (ContinuousMonoidHom.inl _ _))

@[simp]
theorem finiteLeviCharacter_apply (χ : Fin B.length → HeckeCharacter F)
    (m : FiniteLevi F B) :
    finiteLeviCharacter F B χ m =
      ∏ i, (χ i).adelicDeterminant (B.size i) (AdelicGL.ofFinite F (B.size i) (m i)) := rfl

@[simp]
theorem infiniteLeviCharacter_apply (χ : Fin B.length → HeckeCharacter F)
    (m : InfiniteLevi F B) :
    infiniteLeviCharacter F B χ m =
      ∏ i, (χ i).adelicDeterminant (B.size i) (AdelicGL.ofInfinite F (B.size i) (m i)) := rfl

theorem leviCharacter_split (χ : Fin B.length → HeckeCharacter F) (m : FullLevi F B) :
    leviCharacter F B χ m =
      infiniteLeviCharacter F B χ (leviInfinite F B m) *
        finiteLeviCharacter F B χ (leviFinite F B m) := by
  change leviCharacter F B χ m =
    leviCharacter F B χ (leviPair F B (leviInfinite F B m) 1) *
      leviCharacter F B χ (leviPair F B 1 (leviFinite F B m))
  rw [← map_mul]
  congr 1
  apply (leviSplit F B).injective
  change (leviInfinite F B m, leviFinite F B m) =
    (leviInfinite F B _, leviFinite F B _)
  simp only [map_mul, leviInfinite_pair, leviFinite_pair, mul_one, one_mul]

/-- Actual parabolic inflation along the continuous diagonal-block projection. -/
def parabolicCharacter (χ : Fin B.length → HeckeCharacter F) : Full F B →ₜ* ℂˣ :=
  (leviCharacter F B χ).comp (B.leviProjectionContinuous (Adeles F))

@[simp]
theorem parabolicCharacter_section (χ : Fin B.length → HeckeCharacter F)
    (m : FullLevi F B) :
    parabolicCharacter F B χ (B.leviInParabolic (Adeles F) m) = leviCharacter F B χ m := by
  change leviCharacter F B χ (B.leviProjection (Adeles F) (B.leviInParabolic _ m)) = _
  rw [B.leviProjection_section]

@[simp]
theorem parabolicCharacter_unipotent (χ : Fin B.length → HeckeCharacter F)
    (u : B.unipotentRadical (Adeles F)) : parabolicCharacter F B χ u = 1 := by
  change leviCharacter F B χ (B.leviProjection (Adeles F) u.val) = 1
  rw [u.property, map_one]

@[simp]
theorem parabolicCharacter_rational (χ : Fin B.length → HeckeCharacter F)
    (p : Rational F B) : parabolicCharacter F B χ (AdelicBlockParabolic.rational F B p) = 1 := by
  change leviCharacter F B χ
    (B.leviProjection (Adeles F) (AdelicBlockParabolic.rational F B p)) = 1
  have h : B.leviProjection (Adeles F) (AdelicBlockParabolic.rational F B p) =
      fun i => AdelicGL.rational F (B.size i) (B.leviProjection F p i) := by
    funext i
    apply Units.ext
    ext a b
    rfl
  rw [h, leviCharacter_rational]

/-- A common Hecke character on all blocks is the full parabolic determinant pullback. -/
theorem parabolicCharacter_constant (χ : HeckeCharacter F) (p : Full F B) :
    parabolicCharacter F B (fun _ => χ) p = χ.adelicDeterminant n p.val := by
  change (∏ i, χ.onIdeles (determinant (B.leviProjection (Adeles F) p i))) =
    χ.onIdeles (determinant p.val)
  rw [determinant_blockParabolic B p, map_prod]

/-- The actual one-dimensional Levi representation on the complex numbers. -/
def leviRepresentation (χ : Fin B.length → HeckeCharacter F) :
    Representation ℂ (FullLevi F B) ℂ :=
  Langlands.characterRepresentation (leviCharacter F B χ).toMonoidHom

@[simp]
theorem leviRepresentation_apply (χ : Fin B.length → HeckeCharacter F)
    (m : FullLevi F B) (v : ℂ) :
    leviRepresentation F B χ m v = (leviCharacter F B χ m : ℂ) * v := rfl

/-- The scalar action is jointly continuous for arbitrary continuous Hecke characters. -/
theorem leviRepresentation_continuous (χ : Fin B.length → HeckeCharacter F) :
    Continuous (fun p : FullLevi F B × ℂ => leviRepresentation F B χ p.1 p.2) :=
  (Units.continuous_val.comp ((leviCharacter F B χ).continuous.comp continuous_fst)).mul
    continuous_snd

/-- Finite-order block characters give a locally constant character on the whole Levi. -/
theorem leviCharacter_isLocallyConstant (χ : Fin B.length → HeckeCharacter F)
    (hχ : ∀ i, (χ i).HasFiniteOrder) : IsLocallyConstant (leviCharacter F B χ) := by
  classical
  have hfactor (i : Fin B.length) :
      IsLocallyConstant (fun m : FullLevi F B =>
        (χ i).adelicDeterminant (B.size i) (m i)) :=
    (hχ i).isLocallyConstant.comp_continuous
      ((ideleClassMap F).continuous.comp
        ((AdelicGL.determinant F (B.size i)).continuous.comp (continuous_apply i)))
  have hprod (S : Finset (Fin B.length)) :
      IsLocallyConstant (fun m : FullLevi F B =>
        ∏ i ∈ S, (χ i).adelicDeterminant (B.size i) (m i)) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact IsLocallyConstant.of_constant _ (fun _ _ => rfl)
    | @insert i S hi hS =>
      simpa only [Finset.prod_insert hi] using
        (hfactor i).comp₂ hS (fun a b => a * b)
  exact hprod Finset.univ

/-- Finite-order inducing data defines an actual smooth scalar Levi object. -/
def finiteOrderSmoothCharacter (χ : Fin B.length → HeckeCharacter F)
    (hχ : ∀ i, (χ i).HasFiniteOrder) : Induction.SmoothCharacter ℂ (FullLevi F B) where
  toMonoidHom := (leviCharacter F B χ).toMonoidHom
  isOpen_ker := (leviCharacter_isLocallyConstant F B χ hχ).isOpen_fiber 1

end Langlands.Global.AdelicBlockHeckeCharacter

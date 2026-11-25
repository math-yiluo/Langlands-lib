import Langlands.AbelianScheme.TorsionImageSum
import Langlands.AbelianScheme.IsogenyActionDescent
import Langlands.CategoryTheory.RationalizationScaledActions
import Langlands.CategoryTheory.RationalizationIntegralInverse

/-! # Integral actions on a supplied torsion-image quotient -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.OrderSaturation

variable {S : Scheme.{u}} {I : Type u} [Fintype I]
  {O : Type v} [Ring O] {A : AbelianScheme S}
  (b : Basis I ℤ O) {α : O →+* Rationalization.End A}
  (s : Rationalization.ScaledIntegralLift α)

variable [IsFinite (GroupScheme.torsion A.toGrp s.denom).X.hom]
  [Etale (GroupScheme.torsion A.toGrp s.denom).X.hom]

/-- The actual sum of the scaled basis endomorphisms' torsion images. -/
abbrev subgroup : FiniteEtaleSubgroup A :=
  FiniteEtaleSubgroup.TorsionImageSum.subgroup A s.denom (fun i => s.map (b i))

variable (D : (subgroup b s).QuotientData)

private theorem basis_restriction_q_zero (i : I) :
    (CommGroupScheme.torsionInclusion s.denom).app A.toCommGroupScheme ≫
      commHom (s.map (b i)).asHom ≫ commHom D.q = 0 := by
  rw [← Category.assoc, ← FiniteEtaleSubgroup.TorsionImageSum.component_inclusion A s.denom
    (fun j => s.map (b j)) i, Category.assoc, D.inclusion_comp_q, comp_zero]

/-- Every scaled endomorphism followed by the quotient kills the original torsion. -/
theorem restriction_q_zero (x : O) :
    (CommGroupScheme.torsionInclusion s.denom).app A.toCommGroupScheme ≫
      commHom ((s.map x).asHom ≫ D.q) = 0 := by
  let L : End A →ₗ[ℤ]
      ((CommGroupScheme.torsionFunctor s.denom).obj A.toCommGroupScheme ⟶
        D.B.toCommGroupScheme) :=
    (((Preadditive.leftComp D.B.toCommGroupScheme
      ((CommGroupScheme.torsionInclusion s.denom).app A.toCommGroupScheme)).comp
        (Preadditive.rightComp A.toCommGroupScheme (commHom D.q))).comp
          (CategoryTheory.End.addEquiv (X := A)).toAddMonoidHom).toIntLinearMap
  have h : L.comp s.map = 0 := by
    apply b.ext
    intro i
    exact basis_restriction_q_zero b s D i
  exact DFunLike.congr_fun h x

variable (hn : IsIsogeny (s.denom • (𝟙 A)))

private theorem kills_multiplication_kernel (x : O) :
    KillsKernel (s.denom • (𝟙 A)) ((s.map x).asHom ≫ D.q) := by
  exact congrArg Additive.toMul (restriction_q_zero b s D x)

/-- First factorization: descend the scaled map followed by the quotient through `[n]`. -/
def firstLift (x : O) : A ⟶ D.B :=
  IsogenyActionDescent.lift hn ((s.map x).asHom ≫ D.q)
    (kills_multiplication_kernel b s D x)

@[reassoc]
theorem firstLift_fac (x : O) :
    (s.denom • (𝟙 A)) ≫ firstLift b s D hn x = (s.map x).asHom ≫ D.q :=
  IsogenyActionDescent.fac hn _ _

/-- The exact scaled multiplication relation survives the first factorization. -/
@[reassoc]
theorem map_comp_firstLift (x y : O) :
    (s.map y).asHom ≫ firstLift b s D hn x = (s.map (x * y)).asHom ≫ D.q := by
  apply IsogenyActionDescent.hom_ext hn
  calc
    (s.denom • (𝟙 A)) ≫ ((s.map y).asHom ≫ firstLift b s D hn x) =
        (s.map y).asHom ≫ ((s.denom • (𝟙 A)) ≫ firstLift b s D hn x) := by
      simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
        Category.id_comp]
    _ = (s.map x * s.map y).asHom ≫ D.q := by
      rw [firstLift_fac]
      rfl
    _ = (s.denom • s.map (x * y)).asHom ≫ D.q := by rw [s.map_mul]
    _ = (s.denom • (𝟙 A)) ≫ ((s.map (x * y)).asHom ≫ D.q) := by
      simp only [Preadditive.zsmul_comp, Category.id_comp]
      exact Preadditive.zsmul_comp (s.map (x * y)).asHom D.q s.denom

/-- The first descended map kills the entire actual torsion-image subgroup. -/
theorem firstLift_kills_subgroup (x : O) :
    (subgroup b s).inclusion ≫ commHom (firstLift b s D hn x) = 0 := by
  apply (FiniteEtaleSubgroup.TorsionImageSum.inclusion_comp_eq_zero_iff A s.denom
    (fun i => s.map (b i)) (commHom (firstLift b s D hn x))).mpr
  intro i
  change (CommGroupScheme.torsionInclusion s.denom).app A.toCommGroupScheme ≫
    commHom ((s.map (b i)).asHom ≫ firstLift b s D hn x) = 0
  rw [map_comp_firstLift]
  exact restriction_q_zero b s D (x * b i)

/-- Second factorization: descend the first lift through the actual quotient. -/
def actionMap (x : O) : End D.B :=
  CategoryTheory.End.of (D.lift (firstLift b s D hn x) (firstLift_kills_subgroup b s D hn x))

@[reassoc]
theorem actionMap_fac (x : O) :
    D.q ≫ (actionMap b s D hn x).asHom = firstLift b s D hn x :=
  D.fac_lift _ (firstLift_kills_subgroup b s D hn x)

/-- The two factorizations reconstruct a unital integral ring action on the quotient. -/
def action : O →+* End D.B where
  toFun := actionMap b s D hn
  map_one' := by
    apply CategoryTheory.End.ext
    apply IsogenyActionDescent.hom_ext D.isIsogeny
    apply IsogenyActionDescent.hom_ext hn
    rw [actionMap_fac, firstLift_fac, s.map_one]
    rfl
  map_zero' := by
    apply CategoryTheory.End.ext
    apply IsogenyActionDescent.hom_ext D.isIsogeny
    apply IsogenyActionDescent.hom_ext hn
    rw [actionMap_fac, firstLift_fac, map_zero, CategoryTheory.End.zero_asHom,
      CategoryTheory.End.zero_asHom, zero_comp, comp_zero, comp_zero]
  map_add' x y := by
    apply CategoryTheory.End.ext
    rw [CategoryTheory.End.add_asHom]
    apply IsogenyActionDescent.hom_ext D.isIsogeny
    apply IsogenyActionDescent.hom_ext hn
    rw [actionMap_fac, firstLift_fac, map_add, CategoryTheory.End.add_asHom,
      Preadditive.add_comp,
      Preadditive.comp_add, Preadditive.comp_add, actionMap_fac, actionMap_fac,
      firstLift_fac, firstLift_fac]
  map_mul' x y := by
    apply CategoryTheory.End.ext
    apply IsogenyActionDescent.hom_ext D.isIsogeny
    apply IsogenyActionDescent.hom_ext hn
    change (s.denom • (𝟙 A)) ≫ (D.q ≫ (actionMap b s D hn (x * y)).asHom) =
      (s.denom • (𝟙 A)) ≫
        (D.q ≫ ((actionMap b s D hn y).asHom ≫ (actionMap b s D hn x).asHom))
    calc
      _ = (s.map (x * y)).asHom ≫ D.q := by rw [actionMap_fac, firstLift_fac]
      _ = (s.map y).asHom ≫ firstLift b s D hn x := (map_comp_firstLift b s D hn x y).symm
      _ = (s.map y).asHom ≫ (D.q ≫ (actionMap b s D hn x).asHom) := by rw [actionMap_fac]
      _ = ((s.denom • (𝟙 A)) ≫ firstLift b s D hn y) ≫
          (actionMap b s D hn x).asHom := by rw [firstLift_fac, Category.assoc]
      _ = _ := by rw [actionMap_fac_assoc, Category.assoc]

/-- The integral quotient action satisfies the exact scaled intertwining equation. -/
@[reassoc]
theorem action_scaled_fac (x : O) :
    (s.denom • (𝟙 A)) ≫ D.q ≫ (action b s D hn x).asHom = (s.map x).asHom ≫ D.q := by
  change (s.denom • (𝟙 A)) ≫ D.q ≫ (actionMap b s D hn x).asHom = _
  rw [actionMap_fac, firstLift_fac]

/-- The quotient intertwines the original rational action with the integral action. -/
theorem action_rational_fac (x : O) :
    Rationalization.ofHom D.q ≫
        (Rationalization.ofEnd D.B (action b s D hn x)).asHom =
      (α x).asHom ≫ Rationalization.ofHom D.q := by
  have hnQ : (s.denom : ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.denom_ne_zero
  apply smul_right_injective (M := Rationalization.Hom A D.B) hnQ
  have h := congrArg ((Rationalization.inclusion (C := AbelianScheme S)).map)
    (action_scaled_fac b s D hn x)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zsmul,
    CategoryTheory.Functor.map_id] at h
  change (s.denom • 𝟙 (Rationalization.of A)) ≫
      (Rationalization.ofHom D.q ≫
        (Rationalization.ofEnd D.B (action b s D hn x)).asHom) =
    Rationalization.ofHom (s.map x).asHom ≫ Rationalization.ofHom D.q at h
  rw [show Rationalization.ofHom (s.map x).asHom = s.denom • (α x).asHom from
    congrArg CategoryTheory.End.asHom (s.ofEnd_map x)] at h
  have heq : s.denom • (Rationalization.ofHom D.q ≫
        (Rationalization.ofEnd D.B (action b s D hn x)).asHom) =
      s.denom • ((α x).asHom ≫ Rationalization.ofHom D.q) := by
    calc
      _ = (s.denom • 𝟙 (Rationalization.of A)) ≫
          (Rationalization.ofHom D.q ≫
            (Rationalization.ofEnd D.B (action b s D hn x)).asHom) := by
        rw [Preadditive.zsmul_comp, Category.id_comp]
      _ = (s.denom • (α x).asHom) ≫ Rationalization.ofHom D.q := h
      _ = _ := Preadditive.zsmul_comp (C := Rationalization (AbelianScheme S))
        (P := Rationalization.of A) (Q := Rationalization.of A) (R := Rationalization.of D.B)
        (α x).asHom (Rationalization.ofHom (X := A) (Y := D.B) D.q) s.denom
  simpa only [← Int.cast_smul_eq_zsmul ℚ] using heq

/-- The exact scaled equation uniquely determines the integral action. -/
theorem action_unique (β : O →+* End D.B)
    (hβ : ∀ x, (s.denom • (𝟙 A)) ≫ D.q ≫ (β x).asHom = (s.map x).asHom ≫ D.q) :
    β = action b s D hn := by
  ext x : 1
  apply CategoryTheory.End.ext
  apply IsogenyActionDescent.hom_ext D.isIsogeny
  apply IsogenyActionDescent.hom_ext hn
  exact (hβ x).trans (action_scaled_fac b s D hn x).symm

/-- Multiplication by the denominator factors through the supplied quotient. -/
def inverseMultiple : D.B ⟶ A :=
  D.lift (s.denom • (𝟙 A))
    (FiniteEtaleSubgroup.TorsionImageSum.inclusion_zsmul A s.denom (fun i => s.map (b i)))

@[reassoc]
theorem q_inverseMultiple :
    D.q ≫ inverseMultiple b s D = s.denom • (𝟙 A) :=
  D.fac_lift _ _

@[reassoc]
theorem inverseMultiple_q :
    inverseMultiple b s D ≫ D.q = s.denom • (𝟙 D.B) := by
  apply IsogenyActionDescent.hom_ext D.isIsogeny
  rw [← Category.assoc, q_inverseMultiple, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]

/-- The quotient and its actual inverse-multiple map retain the nonzero denominator. -/
def inverseData : Rationalization.IntegralInverseData A D.B where
  multiple := s.denom
  multiple_ne_zero := s.denom_ne_zero
  hom := D.q
  inv := inverseMultiple b s D
  hom_inv := q_inverseMultiple b s D
  inv_hom := inverseMultiple_q b s D

/-- The actual quotient is an isomorphism in the rationalized category. -/
def rationalIso : Rationalization.of A ≅ Rationalization.of D.B :=
  (inverseData b s D).toIso

@[simp]
theorem rationalIso_hom :
    (rationalIso b s D).hom = Rationalization.ofHom D.q := rfl

@[simp]
theorem rationalIso_inv :
    (rationalIso b s D).inv = (s.denom : ℚ)⁻¹ •
      Rationalization.ofHom (inverseMultiple b s D) := rfl

/-- The inverse rational isomorphism also intertwines the original action. -/
theorem rationalIso_inv_fac (x : O) :
    (Rationalization.ofEnd D.B (action b s D hn x)).asHom ≫ (rationalIso b s D).inv =
      (rationalIso b s D).inv ≫ (α x).asHom := by
  apply (cancel_epi (rationalIso b s D).hom).mp
  calc
    _ = ((α x).asHom ≫ (rationalIso b s D).hom) ≫ (rationalIso b s D).inv := by
      rw [← Category.assoc, rationalIso_hom, action_rational_fac]
    _ = (α x).asHom := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end Langlands.AbelianScheme.OrderSaturation

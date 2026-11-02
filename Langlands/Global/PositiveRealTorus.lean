import Langlands.Global.PositiveRealIdeles
import Langlands.GroupScheme.Torus.Weights

/-!
# Positive real points of actual split tori

The chosen splitting is an isomorphism of group schemes. Its affine point
equivalence transports the scalar idele map to the actual torus points.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (F : Type u) [Field F]
variable (I : Type u) [Fintype I]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Coordinates on actual affine points through the supplied splitting. -/
def coordinates (A : Type u) [CommRing A] [Algebra F A] :
    Lie.AffinePoints T.toGrp A ≃* (I → Aˣ) :=
  (isoPointsEquiv e ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F A)))).trans
      (splitTorus.affinePointsEquiv I
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F A))).hom)

/-- The exponent vector of an actual character, expressed in the supplied splitting. -/
def characterExponents (χ : characterLattice T) : I → ℤ :=
  splitTorus.characterLatticeEquiv F I
    (Additive.ofMul (e.inv ≫ CommGroupScheme.groupHom χ))

/-- The positive monomial determined by the actual character. -/
def positiveCharacter (χ : characterLattice T) : (I → ℝ≥0ˣ) →* ℝ≥0ˣ where
  toFun x := ∏ i, x i ^ characterExponents F I T e χ i
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

/-- The affine version of the published monomial formula for split-torus characters. -/
theorem split_characterValue_eq_prod
    (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I))
    {A : Type u} [CommRing A] [Algebra F A]
    (x : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of F)) I) A) :
    Lie.characterValue χ x =
      ∏ i, splitTorus.affinePointsEquiv I
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F A))).hom x i ^
          splitTorus.characterLatticeEquiv F I χ i := by
  conv_lhs =>
    rw [← (splitTorus.characterLatticeEquiv F I).symm_apply_apply χ,
      splitTorus.characterLatticeEquiv_symm_eq]
  rw [Lie.characterValue]
  refine (congrArg (Gm.affinePointsEquiv
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F A))).hom)
    (comp_groupHom_sum
      (G := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I)
      x Finset.univ fun i =>
        splitTorus.characterLatticeEquiv F I χ i •
          splitTorus.proj (Spec (CommRingCat.of F)) I i)).trans ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (congrArg (Gm.affinePointsEquiv
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F A))).hom)
    (comp_groupHom_zsmul
      (G := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I)
      x (splitTorus.characterLatticeEquiv F I χ i)
      (splitTorus.proj (Spec (CommRingCat.of F)) I i))).trans ?_
  rw [map_zpow]
  rfl

/-- Characters of the actual torus evaluate by their genuine coordinate exponents. -/
theorem characterValue_eq_prod (χ : characterLattice T)
    {A : Type u} [CommRing A] [Algebra F A] (x : Lie.AffinePoints T.toGrp A) :
    Lie.characterValue χ x =
      ∏ i, coordinates F I T e A x i ^ characterExponents F I T e χ i := by
  let χ' : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I) :=
    Additive.ofMul (e.inv ≫ CommGroupScheme.groupHom χ)
  let y := isoPointsEquiv e ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F A))) x
  have h : Lie.characterValue χ x = Lie.characterValue χ' y := by
    unfold Lie.characterValue
    congr 1
    change x ≫ (CommGroupScheme.groupHom χ).hom.hom =
      (x ≫ e.hom.hom.hom) ≫ (e.inv ≫ CommGroupScheme.groupHom χ).hom.hom
    rw [Category.assoc]
    exact congrArg (fun f : T.toGrp ⟶ (Gm (Spec (CommRingCat.of F))).toGrp =>
      x ≫ f.hom.hom) (e.hom_inv_id_assoc (CommGroupScheme.groupHom χ)).symm
  exact h.trans (split_characterValue_eq_prod F I χ' y)

variable [NumberField F]

/-- Equal positive-real coordinates at every infinite place and identity at finite places. -/
def full : (I → ℝ≥0ˣ) →* Lie.AffinePoints T.toGrp (Adeles F) :=
  (coordinates F I T e (Adeles F)).symm.toMonoidHom.comp
    ((PositiveRealIdeles.full F).toMonoidHom.compLeft I)

@[simp]
theorem coordinates_full (x : I → ℝ≥0ˣ) :
    coordinates F I T e (Adeles F) (full F I T e x) =
      fun i => PositiveRealIdeles.full F (x i) :=
  MulEquiv.apply_symm_apply _ _

theorem full_injective : Function.Injective (full F I T e) := by
  intro x y h
  have hc := congrArg (coordinates F I T e (Adeles F)) h
  rw [coordinates_full, coordinates_full] at hc
  exact funext fun i => PositiveRealIdeles.full_injective F (congrFun hc i)

/-- The actual positive-real subgroup of the adelic torus for the supplied splitting. -/
def subgroup : Subgroup (Lie.AffinePoints T.toGrp (Adeles F)) :=
  (full F I T e).range

theorem mem_subgroup_iff (g : Lie.AffinePoints T.toGrp (Adeles F)) :
    g ∈ subgroup F I T e ↔ ∃ x, full F I T e x = g := Iff.rfl

/-- Actual character evaluation commutes with the positive-real scalar idele map. -/
@[simp]
theorem characterValue_full (χ : characterLattice T) (x : I → ℝ≥0ˣ) :
    Lie.characterValue χ (full F I T e x) =
      PositiveRealIdeles.full F (positiveCharacter F I T e χ x) := by
  rw [characterValue_eq_prod F I T e χ, coordinates_full]
  simp only [positiveCharacter, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow]

/-- The normalized idelic character norm retains the number-field degree. -/
@[simp]
theorem absoluteValue_characterValue_full (χ : characterLattice T) (x : I → ℝ≥0ˣ) :
    IdeleAbsoluteValue.full F (Lie.characterValue χ (full F I T e x)) =
      positiveCharacter F I T e χ x ^ Module.finrank ℚ F := by
  rw [characterValue_full, PositiveRealIdeles.absoluteValue_full]

end Langlands.Global.PositiveRealTorus

import Langlands.GroupScheme.HomogeneousCharacterProducts

/-! # Recovering an actual character from a normalized covariant coordinate -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AffineCoordinates

open HomogeneousQuotientFromEmbedding

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Normalization at the rational identity remains true on every test scheme. -/
theorem pointAlgebraHom_one_of_rational {d : algebra G}
    (h1 : pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1)
    (T : Over (Spec (CommRingCat.of k))) : pointAlgebraHom G T 1 d = 1 := by
  let a : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.homMk T.hom (by simp)
  have h := congrArg (fun f => f d) (pointAlgebraHom_naturality G a 1)
  simpa only [MonObj.comp_one, AlgHom.comp_apply, h1, map_one] using h

variable (i : H ⟶ G) (χ : algebra H) (d : algebra G)
  (hd : d ∈ leftCovariantSubspace i χ)
  (h1 : pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1)

include hd h1

/-- The weight value is the restriction of the normalized covariant function. -/
theorem pointAlgebraHom_weight_eq (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) :
    pointAlgebraHom H T h χ = pointAlgebraHom G T (h ≫ i.hom.hom) d := by
  have e := pointAlgebraHom_leftCovariant i χ hd T h 1
  simpa only [mul_one, pointAlgebraHom_one_of_rational h1] using e.symm

/-- A normalized covariance weight takes the identity to one. -/
theorem pointAlgebraHom_weight_one (T : Over (Spec (CommRingCat.of k))) :
    pointAlgebraHom H T 1 χ = 1 := by
  rw [pointAlgebraHom_weight_eq i χ d hd h1, MonObj.one_comp,
    pointAlgebraHom_one_of_rational h1]

/-- A normalized covariance weight is multiplicative on arbitrary scheme tests. -/
theorem pointAlgebraHom_weight_mul (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ H.X) :
    pointAlgebraHom H T (a * b) χ =
      pointAlgebraHom H T a χ * pointAlgebraHom H T b χ := by
  rw [pointAlgebraHom_weight_eq i χ d hd h1, MonObj.mul_comp,
    pointAlgebraHom_leftCovariant i χ hd,
    ← pointAlgebraHom_weight_eq i χ d hd h1]

/-- The weight and its value at the inverse give an actual global unit. -/
def normalizedWeightUnit (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) :
    Γ(T.left, ⊤)ˣ where
  val := pointAlgebraHom H T h χ
  inv := pointAlgebraHom H T h⁻¹ χ
  val_inv := by
    rw [← pointAlgebraHom_weight_mul i χ d hd h1, mul_inv_cancel,
      pointAlgebraHom_weight_one i χ d hd h1]
  inv_val := by
    rw [← pointAlgebraHom_weight_mul i χ d hd h1, inv_mul_cancel,
      pointAlgebraHom_weight_one i χ d hd h1]

/-- Evaluation of the recovered weight, as a homomorphism to global units. -/
def normalizedWeightUnits (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ H.X) →* Γ(T.left, ⊤)ˣ where
  toFun := normalizedWeightUnit i χ d hd h1 T
  map_one' := Units.ext (pointAlgebraHom_weight_one i χ d hd h1 T)
  map_mul' a b := Units.ext (pointAlgebraHom_weight_mul i χ d hd h1 T a b)

/-- Global-unit values of the weight commute with every test-scheme pullback. -/
theorem normalizedWeightUnits_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (h : T ⟶ H.X) :
    normalizedWeightUnits i χ d hd h1 T' (a ≫ h) =
      Units.map a.left.appTop.hom.toMonoidHom (normalizedWeightUnits i χ d hd h1 T h) := by
  apply Units.ext
  exact congrArg (fun f => f χ) (pointAlgebraHom_naturality H a h)

/-- The weight as a natural family of points of the multiplicative group. -/
def normalizedWeightPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ H.X) →* (T ⟶ (Gm (Spec (CommRingCat.of k))).X) :=
  (Gm.pointsEquiv (Spec (CommRingCat.of k)) T).symm.toMonoidHom.comp
    (normalizedWeightUnits i χ d hd h1 T)

/-- The multiplicative-group points of the weight are natural on all schemes. -/
theorem normalizedWeightPoints_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (h : T ⟶ H.X) :
    normalizedWeightPoints i χ d hd h1 T' (a ≫ h) =
      a ≫ normalizedWeightPoints i χ d hd h1 T h := by
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) T').injective
  simp only [normalizedWeightPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
  exact normalizedWeightUnits_naturality i χ d hd h1 a h

/-- The actual character determined by a normalized covariant coordinate. -/
def normalizedCovariantCharacter : rationalCharacters H :=
  Additive.ofMul (homOfPoints (normalizedWeightPoints i χ d hd h1)
    (normalizedWeightPoints_naturality i χ d hd h1))

/-- The recovered character has exactly the originally supplied weight values. -/
theorem characterEval_normalizedCovariantCharacter
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) :
    (characterEval (normalizedCovariantCharacter i χ d hd h1) T h : Γ(T.left, ⊤)) =
      pointAlgebraHom H T h χ := by
  rw [characterEval_apply]
  change ((Gm.pointsEquiv (Spec (CommRingCat.of k)) T)
    (h ≫ (homOfPoints (normalizedWeightPoints i χ d hd h1)
      (normalizedWeightPoints_naturality i χ d hd h1)).hom.hom) : Γ(T.left, ⊤)) = _
  rw [comp_homOfPoints]
  exact congrArg Units.val
    ((Gm.pointsEquiv (Spec (CommRingCat.of k)) T).apply_symm_apply
      (normalizedWeightUnits i χ d hd h1 T h))

/-- The supplied weight is the coordinate of the recovered actual character. -/
theorem characterCoordinate_normalizedCovariantCharacter :
    characterCoordinate H (normalizedCovariantCharacter i χ d hd h1) = χ := by
  apply (globalAlgHom_bijective H).1
  change pointAlgebraHom H H.X (𝟙 H.X) _ = pointAlgebraHom H H.X (𝟙 H.X) χ
  rw [pointAlgebraHom_characterCoordinate,
    characterEval_normalizedCovariantCharacter i χ d hd h1]

/-- On a proper homogeneous quotient, every power-weight covariant space is finite. -/
theorem finite_leftCovariantSubspace_pow_of_normalized [Mono i.hom.hom]
    (D : HomogeneousQuotient i) [IsProper D.scheme.hom] (e : ℕ) :
    Module.Finite k (leftCovariantSubspace i (χ ^ e)) := by
  let recovered := normalizedCovariantCharacter i χ d hd h1
  have hc : characterCoordinate H recovered = χ :=
    characterCoordinate_normalizedCovariantCharacter i χ d hd h1
  rw [← hc, ← characterCoordinate_nsmul]
  exact finite_leftCovariantSubspace_characterCoordinate i D (e • recovered)

end Langlands.GroupScheme.AffineCoordinates

import Langlands.GroupScheme.SpecialLinearAffineRow
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # The actual binary upper-triangular special linear subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

section Matrices

variable (A : Type u) [CommRing A]

/-- The upper-triangular determinant-one matrices over an arbitrary commutative ring. -/
def subgroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) A) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a * b) 1 0 = 0
    rw [upper_mul_bottomRow a b ha 0, hb, mul_zero]
  inv_mem' := by
    intro a ha
    change a⁻¹ 1 0 = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using congrArg Neg.neg ha

@[simp] theorem mem_subgroup (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    g ∈ subgroup A ↔ g 1 0 = 0 := Iff.rfl

variable {A}

/-- The last diagonal entry is a unit, with inverse the first diagonal entry. -/
def diagonalUnit (g : subgroup A) : Aˣ where
  val := g.val 1 1
  inv := g.val 0 0
  val_inv := by
    have h := g.val.property
    rw [Matrix.det_fin_two, g.property, mul_zero, sub_zero] at h
    exact (mul_comm _ _).trans h
  inv_val := by
    have h := g.val.property
    rwa [Matrix.det_fin_two, g.property, mul_zero, sub_zero] at h

@[simp] theorem diagonalUnit_val (g : subgroup A) :
    (diagonalUnit g : A) = g.val 1 1 := rfl

/-- Multiplication of upper-triangular matrices multiplies their last diagonal entries. -/
def diagonalHom : subgroup A →* Aˣ where
  toFun := diagonalUnit
  map_one' := by
    apply Units.ext
    change (1 : Matrix.SpecialLinearGroup (Fin 2) A) 1 1 = 1
    simp
  map_mul' g h := by
    apply Units.ext
    exact upper_mul_bottomRow g.val h.val g.property 1

end Matrices

section Schemes

variable (R : CommRingCat.{u})

/-- The ideal imposing the vanishing of the sole below-diagonal binary entry. -/
def upperIdeal : Ideal (CoordinateRing (Fin 2) R) :=
  Ideal.span {quotient (Fin 2) R (X (1, 0))}

/-- The actual upper-triangular matrix subgroup is cut out by its entry equation. -/
theorem isCutOutBy :
    Corepresented.IsCutOutBy (corepresentableBy (Fin 2) R)
      (fun A => subgroup A) (upperIdeal R) := by
  intro A g
  change Matrix.SpecialLinearGroup (Fin 2) A at g
  change g 1 0 = 0 ↔ ∀ b ∈ upperIdeal R, classify (R := R) g b = 0
  constructor
  · intro hg b hb
    have hle : upperIdeal R ≤ RingHom.ker (classify (R := R) g) := by
      rw [upperIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, classify_entry]
      exact hg
    exact hle hb
  · intro h
    have h' := h _ (Ideal.subset_span (Set.mem_singleton _))
    rwa [classify_entry] at h'

/-- The upper-triangular subgroup scheme, with its full scheme structure. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.cutGroupScheme (isCutOutBy R)

/-- Its closed inclusion into the actual binary special linear group. -/
abbrev inclusion : groupScheme R ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  Corepresented.cutHom (isCutOutBy R)

instance isAffine_groupScheme : IsAffine (groupScheme R).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of
    (CoordinateRing (Fin 2) R ⧸ upperIdeal R))))

instance isAffineHom_groupScheme : IsAffineHom (groupScheme R).X.hom :=
  isAffineHom_of_isAffine _

theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion R) :=
  Corepresented.isClosedSubgroup_cutHom _

/-- Points on every relative test scheme are precisely upper-triangular matrices. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme R).X) ≃* subgroup Γ(T.left, ⊤) :=
  Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy (isCutOutBy R)) T

/-- The actual inclusion recovers the ordinary matrix inclusion on all test schemes. -/
theorem pointsEquiv_inclusion (T : Over (Spec R)) (x : T ⟶ (groupScheme R).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (x ≫ (inclusion R).hom.hom) =
      (pointsEquiv R T x).val :=
  Corepresented.groupSchemeMap_points _ _ _ x

/-- Every test point of the actual subgroup has zero below-diagonal entry. -/
theorem inclusion_lowerEntry (T : Over (Spec R)) (x : T ⟶ (groupScheme R).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (x ≫ (inclusion R).hom.hom) 1 0 = 0 := by
  rw [pointsEquiv_inclusion]
  exact (pointsEquiv R T x).property

/-- Every upper-triangular test point of the special linear group factors through the subgroup. -/
theorem mem_range_inclusion {T : Over (Spec R)}
    (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :
    x ∈ (SubgroupFunctor.range (inclusion R)).carrier T ↔
      SpecialLinear.pointsEquiv (Fin 2) R T x 1 0 = 0 := by
  rw [Corepresented.range_cutHom]
  rfl

/-- The last diagonal unit, functorially on every relative test scheme. -/
def diagonalPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme R).X) →* (Γ(T.left, ⊤))ˣ :=
  diagonalHom.comp (pointsEquiv R T).toMonoidHom

theorem diagonalPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme R).X) :
    diagonalPoints R T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (diagonalPoints R T x) := by
  apply Units.ext
  change (pointsEquiv R T' (a ≫ x)).val 1 1 =
    a.left.appTop ((pointsEquiv R T x).val 1 1)
  rw [← pointsEquiv_inclusion, Category.assoc,
    SpecialLinear.pointsEquiv_naturality, pointsEquiv_inclusion]
  rfl

/-- The last diagonal as a homomorphism into the actual multiplicative-group points. -/
def diagonalPointToGm (T : Over (Spec R)) :
    (T ⟶ (groupScheme R).X) →* (T ⟶ (Gm (Spec R)).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp (diagonalPoints R T)

theorem diagonalPointToGm_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme R).X) :
    diagonalPointToGm R T' (a ≫ x) = a ≫ diagonalPointToGm R T x := by
  apply (Gm.pointsEquiv (Spec R) T').injective
  simp only [diagonalPointToGm, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
  exact diagonalPoints_naturality R a x

/-- Yoneda constructs the group-scheme map from the natural last-diagonal units. -/
def diagonalMorphism : groupScheme R ⟶ (Gm (Spec R)).toGrp :=
  homOfPoints (diagonalPointToGm R) (diagonalPointToGm_naturality R)

theorem comp_diagonalMorphism (T : Over (Spec R))
    (x : T ⟶ (groupScheme R).X) :
    x ≫ (diagonalMorphism R).hom.hom = diagonalPointToGm R T x :=
  comp_homOfPoints (diagonalPointToGm R) (diagonalPointToGm_naturality R) T x

/-- The actual rational character sending an upper-triangular matrix to its last diagonal. -/
def diagonalCharacter : rationalCharacters (groupScheme R) :=
  Additive.ofMul (diagonalMorphism R)

/-- The character has the prescribed entry value on every relative test scheme. -/
theorem characterEval_diagonalCharacter (T : Over (Spec R))
    (x : T ⟶ (groupScheme R).X) :
    characterEval (diagonalCharacter R) T x = diagonalPoints R T x := by
  rw [characterEval_apply]
  change Gm.pointsEquiv (Spec R) T (x ≫ (diagonalMorphism R).hom.hom) = _
  rw [comp_diagonalMorphism]
  exact (Gm.pointsEquiv (Spec R) T).apply_symm_apply _

end Schemes

section CovariantCoordinates

variable (k : Type u) [Field k]

local instance : IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance : IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

/-- The actual affine coordinate of the last-diagonal rational character. -/
def characterCoordinate : AffineCoordinates.algebra (groupScheme (CommRingCat.of k)) :=
  AffineCoordinates.characterCoordinate (groupScheme (CommRingCat.of k))
    (diagonalCharacter (CommRingCat.of k))

/-- Evaluation of the character coordinate is exactly the last matrix diagonal entry. -/
theorem pointAlgebraHom_characterCoordinate (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme (CommRingCat.of k)).X) :
    AffineCoordinates.pointAlgebraHom (groupScheme (CommRingCat.of k)) T x
        (characterCoordinate k) =
      SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k) T
        (x ≫ (inclusion (CommRingCat.of k)).hom.hom) 1 1 := by
  rw [characterCoordinate, AffineCoordinates.pointAlgebraHom_characterCoordinate,
    characterEval_diagonalCharacter, pointsEquiv_inclusion]
  rfl

/-- Every binary homogeneous polynomial defines a covariant coordinate for the actual subgroup. -/
theorem homogeneousRow_mem_leftCovariant (m : ℕ)
    (f : homogeneousSubmodule (Fin 2) k m) :
    affineHomogeneousRowMap m 1 f ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m) :=
  affineHomogeneousRowMap_mem_leftCovariant _ _
    (inclusion_lowerEntry _) (pointAlgebraHom_characterCoordinate k) m f

/-- The full homogeneous polynomial space maps into the actual covariant coordinate space. -/
def covariantRowMap (m : ℕ) : homogeneousSubmodule (Fin 2) k m →ₗ[k]
    AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
      (characterCoordinate k ^ m) :=
  (affineHomogeneousRowMap m 1).codRestrict _ (homogeneousRow_mem_leftCovariant k m)

/-- The map into actual covariant coordinates is injective in every degree. -/
theorem covariantRowMap_injective (m : ℕ) : Function.Injective (covariantRowMap k m) := by
  intro f g h
  apply binaryAffineHomogeneousRowMap_injective m
  exact congrArg Subtype.val h

end CovariantCoordinates

end Langlands.GroupScheme.SpecialLinear.BinaryUpper

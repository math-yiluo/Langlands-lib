import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.MultiplicativePointTopology

/-! # Character values and the universal point of a split torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitCharacterPoint

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The value of a character of `T` at an affine point, as a unit of the coefficient algebra. -/
def value (χ : characterLattice T) (s : Lie.AffinePoints T.toGrp A) : Aˣ :=
  Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) A)
    (s ≫ (CommGroupScheme.groupHom χ).hom.hom)

theorem value_add (χ ψ : characterLattice T) (s : Lie.AffinePoints T.toGrp A) :
    value (χ + ψ) s = value χ s * value ψ s := by
  unfold value
  rw [comp_groupHom_add, map_mul]

theorem value_zero (s : Lie.AffinePoints T.toGrp A) : value (0 : characterLattice T) s = 1 := by
  unfold value
  rw [comp_groupHom_zero, map_one]

/-- Character values at a fixed point, as a homomorphism on the character lattice. -/
def valueHom (s : Lie.AffinePoints T.toGrp A) : Multiplicative (characterLattice T) →* Aˣ where
  toFun χ := value χ.toAdd s
  map_one' := value_zero s
  map_mul' χ ψ := value_add χ.toAdd ψ.toAdd s

@[simp] theorem valueHom_apply (s : Lie.AffinePoints T.toGrp A)
    (χ : Multiplicative (characterLattice T)) : valueHom s χ = value χ.toAdd s := rfl

/-- Character values commute with change of coefficients. -/
theorem value_affineMap (f : A →ₐ[k] B) (χ : characterLattice T)
    (s : Lie.AffinePoints T.toGrp A) :
    (value χ (Lie.affineMap T.toGrp f s) : B) = f (value χ s) := by
  have h := Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
    (CommAlgCat.ofHom (R := CommRingCat.of k) f) (s ≫ (CommGroupScheme.groupHom χ).hom.hom)
  rw [GroupScheme.affinePointMap_apply, ← Category.assoc] at h
  exact congrArg Units.val h

/-- Character values along a homomorphism are values of the restricted character. -/
theorem value_comp_hom {T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : T'.toGrp ⟶ T.toGrp) (χ : characterLattice T) (s : Lie.AffinePoints T'.toGrp A) :
    value χ (s ≫ f.hom.hom) =
      value (T := T') (characterRestrict f ((rationalCharacters.equivCharacterLattice T).symm χ)) s := by
  unfold value
  rw [Category.assoc]
  rfl

variable (T) in
/-- Monomials of the group algebra of the character lattice, as units. -/
def monomialUnitHom : Multiplicative (characterLattice T) →*
    (AddMonoidAlgebra k (characterLattice T))ˣ :=
  (AddMonoidAlgebra.of k (characterLattice T)).toHomUnits

/-- The monomial unit of a character. -/
def monomialUnit (χ : characterLattice T) : (AddMonoidAlgebra k (characterLattice T))ˣ :=
  monomialUnitHom T (Multiplicative.ofAdd χ)

@[simp] theorem monomialUnit_val (χ : characterLattice T) :
    (monomialUnit χ : AddMonoidAlgebra k (characterLattice T)) =
      AddMonoidAlgebra.single χ 1 := rfl

section Split

variable (hT : IsSplitTorus T.toGrp)

/-- The index type of the chosen splitting of a split torus. -/
def splitIndex : Type u := hT.choose

theorem splitIndex_finite : Finite (splitIndex hT) := hT.choose_spec.choose

/-- The chosen isomorphism of a split torus with a standard split torus. -/
def splitIso : T.toGrp ≅ @splitTorus _ (splitIndex hT) (splitIndex_finite hT) :=
  hT.choose_spec.choose_spec.some

include hT in
/-- Points of a split torus are determined by the values of all its characters. -/
theorem ext_of_isSplitTorus {s s' : Lie.AffinePoints T.toGrp A}
    (h : ∀ χ : characterLattice T, value χ s = value χ s') : s = s' := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have key : s ≫ e.hom.hom.hom = s' ≫ e.hom.hom.hom := by
    apply (splitTorus.algebraPointsEquiv I A).injective
    funext i
    have hv : ∀ x : Lie.AffinePoints T.toGrp A,
        splitTorus.algebraPointsEquiv I A (x ≫ e.hom.hom.hom) i =
          value (T := T) (characterRestrict e.hom
            ((rationalCharacters.equivCharacterLattice _).symm (splitTorus.proj _ I i))) x :=
      fun x => value_comp_hom (T := splitTorus.commGroupScheme _ I) e.hom _ x
    rw [hv s, hv s']
    exact h _
  have hcancel : ∀ x : Lie.AffinePoints T.toGrp A,
      (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x := by
    intro x
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  rw [← hcancel s, key, hcancel]

instance : Finite (splitIndex hT) := splitIndex_finite hT

end Split

section Standard

variable (I : Type u) [Finite I]

/-- The coordinate characters of the standard split torus take the prescribed values. -/
theorem value_proj_symm (c : I → Aˣ) (i : I) :
    value (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) (splitTorus.proj _ I i)
      ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm c) = c i := by
  change splitTorus.algebraPointsEquiv I A ((splitTorus.algebraPointsEquiv I A).symm c) i = c i
  rw [MulEquiv.apply_symm_apply]

omit [Finite I] in
theorem value_sum_zsmul [Fintype I] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (m : I → ℤ) (χ : I → characterLattice T) (s : Lie.AffinePoints T.toGrp A) :
    value (∑ i, m i • χ i) s = ∏ i, value (χ i) s ^ m i := by
  show valueHom s (Multiplicative.ofAdd (∑ i, m i • χ i)) = _
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

omit [Finite I] in
theorem prod_monomialUnit_zpow [Fintype I] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (m : I → ℤ) (χ : I → characterLattice T) :
    ∏ i, monomialUnit (k := k) (χ i) ^ m i = monomialUnit (∑ i, m i • χ i) := by
  simp only [monomialUnit, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]

/-- Every character of the standard split torus is an integral combination of coordinate
characters. -/
theorem eq_sum_proj [Fintype I]
    (ψ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :
    ψ = ∑ i, splitTorus.characterLatticeEquiv k I ψ i • splitTorus.proj _ I i := by
  conv_lhs => rw [← (splitTorus.characterLatticeEquiv k I).symm_apply_apply ψ]
  exact finsum_eq_sum_of_fintype _

variable {I}

/-- The characters of `T` corresponding to the coordinate characters under `e`. -/
def isoCoordinateCharacter (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (i : I) :
    characterLattice T :=
  rationalCharacters.equivCharacterLattice T (characterRestrict e.hom
    ((rationalCharacters.equivCharacterLattice _).symm (splitTorus.proj _ I i)))

omit [Finite I] in
theorem characterRestrict_hom_inv {G H : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ H)
    (χ : rationalCharacters G) : characterRestrict e.hom (characterRestrict e.inv χ) = χ := by
  rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.hom_inv_id, characterRestrict_id]
  rfl

/-- Expansion of a character of `T` in the coordinate characters of a splitting. -/
theorem sum_isoCoordinateCharacter [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (χ : characterLattice T) :
    ∑ i, splitTorus.characterLatticeEquiv k I
        (characterRestrict e.inv ((rationalCharacters.equivCharacterLattice T).symm χ)) i •
      isoCoordinateCharacter e i = χ := by
  let R' : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) →+
      characterLattice T :=
    ((rationalCharacters.equivCharacterLattice T).toAddMonoidHom.comp
      (characterRestrict e.hom)).comp
        (rationalCharacters.equivCharacterLattice _).symm.toAddMonoidHom
  have h1 : ∀ m : I → ℤ, ∑ i, m i • isoCoordinateCharacter e i =
      R' (∑ i, m i • splitTorus.proj _ I i) := by
    intro m
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  rw [h1, ← eq_sum_proj]
  exact characterRestrict_hom_inv e ((rationalCharacters.equivCharacterLattice T).symm χ)

/-- The point with coordinates the monomials of the coordinate characters of a splitting
takes every character to its own monomial. -/
theorem value_isoPoint [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (χ : characterLattice T) :
    value χ ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I
        (AddMonoidAlgebra k (characterLattice T))).symm
        (fun i => monomialUnit (isoCoordinateCharacter e i)) ≫ e.inv.hom.hom) =
      monomialUnit χ := by
  rw [value_comp_hom (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e.inv χ,
    eq_sum_proj I
      (characterRestrict e.inv ((rationalCharacters.equivCharacterLattice T).symm χ)),
    value_sum_zsmul]
  simp only [value_proj_symm]
  rw [prod_monomialUnit_zpow, sum_isoCoordinateCharacter]

end Standard

section Split

variable (hT : IsSplitTorus T.toGrp)

/-- The coordinate characters of the chosen splitting. -/
def coordinateCharacter (i : splitIndex hT) : characterLattice T :=
  isoCoordinateCharacter (splitIso hT) i

/-- The point of `T` over the group algebra of its characters whose coordinates in the chosen
splitting are the monomials of the coordinate characters. -/
def universalPoint : Lie.AffinePoints T.toGrp (AddMonoidAlgebra k (characterLattice T)) :=
  (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) (splitIndex hT)
      (AddMonoidAlgebra k (characterLattice T))).symm
      (fun i => monomialUnit (coordinateCharacter hT i)) ≫ (splitIso hT).inv.hom.hom

/-- Every character takes its own monomial as value at the universal point. -/
theorem value_universalPoint (χ : characterLattice T) :
    value χ (universalPoint hT) = monomialUnit χ := by
  classical
  let _ := Fintype.ofFinite (splitIndex hT)
  exact value_isoPoint (splitIso hT) χ

/-- The algebra map sending each monomial to the value of its character at `s`. -/
def pointLift (s : Lie.AffinePoints T.toGrp A) :
    AddMonoidAlgebra k (characterLattice T) →ₐ[k] A :=
  AddMonoidAlgebra.lift k A (characterLattice T) ((Units.coeHom A).comp (valueHom s))

@[simp] theorem pointLift_single (s : Lie.AffinePoints T.toGrp A) (χ : characterLattice T)
    (r : k) : pointLift s (AddMonoidAlgebra.single χ r) = algebraMap k A r * value χ s := by
  simp [pointLift, Algebra.smul_def]

/-- Every point of a split torus is a coefficient change of the universal point. -/
theorem affineMap_pointLift (s : Lie.AffinePoints T.toGrp A) :
    Lie.affineMap T.toGrp (pointLift s) (universalPoint hT) = s := by
  apply ext_of_isSplitTorus hT
  intro χ
  apply Units.ext
  rw [value_affineMap, value_universalPoint, monomialUnit_val, pointLift_single, map_one,
    one_mul]

end Split

end Langlands.GroupScheme.SplitCharacterPoint

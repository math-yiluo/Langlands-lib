import Langlands.GroupScheme.CentralSurjectionImage.CocharacterFromPoint
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing

/-! # Points of infinite order for surjective characters

If a rational character `χ` of a commutative group scheme over a field `k` has surjective
underlying morphism of schemes, then some point of the group with values in an algebraically
closed field takes, under `χ`, a value transcendental over `k`: lift the generic point of `𝔾_m`
and pass to an algebraically closed field containing both residue fields. Consequently, for an
affine group scheme locally of finite type, `χ` restricts nontrivially to a cocharacter over `k`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The identity character of `𝔾_m` evaluates a point to its unit. -/
theorem characterValue_id {A : Type u} [CommRing A] [Algebra k A]
    (y : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp A) :
    Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k)))) y =
      Gm.affinePointsEquiv (R := CommRingCat.of A)
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))).hom y := by
  rw [Lie.characterValue]
  congr 1

/-- No positive power of the variable is `1` in the field of rational functions. -/
theorem X_pow_ne_one (n : ℕ) (hn : n ≠ 0) :
    (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X) ^ n ≠ 1 := by
  rw [← map_pow, ← map_one (algebraMap (Polynomial k) (FractionRing (Polynomial k))), Ne,
    (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k))).eq_iff]
  intro h
  have := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one] at this
  exact hn this

/-- Two field extensions of a common field embed compatibly into one algebraically closed
field. -/
theorem exists_isAlgClosed_compositum {F A B : Type u} [Field F] [Field A] [Field B]
    (f : F →+* A) (g : F →+* B) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (a : A →+* K) (b : B →+* K),
      a.comp f = b.comp g := by
  let : Algebra F A := f.toAlgebra
  let : Algebra F B := g.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[F] B)
  let := Ideal.Quotient.field m
  refine ⟨AlgebraicClosure (A ⊗[F] B ⧸ m), inferInstance, inferInstance,
    (algebraMap _ _).comp ((Ideal.Quotient.mk m).comp
      Algebra.TensorProduct.includeLeftRingHom),
    (algebraMap _ _).comp ((Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[F] A ⊗[F] B).toRingHom), ?_⟩
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  congr 2
  change f r ⊗ₜ[F] (1 : B) = (1 : A) ⊗ₜ[F] g r
  rw [show f r = r • (1 : A) by rw [Algebra.smul_def, mul_one]; rfl,
    show g r = r • (1 : B) by rw [Algebra.smul_def, mul_one]; rfl, TensorProduct.smul_tmul]

variable {Z : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Points of infinite order.** If the underlying morphism of a rational character `χ` is
surjective, some point of `Z` with values in an algebraically closed field has a value under `χ`
no positive power of which is `1`. -/
theorem exists_point_of_surjective (χ : rationalCharacters Z.toGrp)
    (hχ : Surjective χ.toMul.hom.hom.left) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K)
      (x : Lie.AffinePoints Z.toGrp K), ∀ n : ℕ, n ≠ 0 →
        Lie.characterValue (rationalCharacters.equivCharacterLattice Z χ) x ^ n ≠ 1 := by
  classical
  let R := CommRingCat.of k
  let L := FractionRing (Polynomial k)
  let X₀ : L := algebraMap (Polynomial k) L Polynomial.X
  have hX₀ : X₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) L)).mpr Polynomial.X_ne_zero
  let t₀ : Lˣ := Units.mk0 X₀ hX₀
  let G₁ := Gm (Spec R)
  let y : Lie.AffinePoints G₁.toGrp L :=
    (Gm.affinePointsEquiv (R := CommRingCat.of L)
      ((algSpec R).obj (op (CommAlgCat.of R L))).hom).symm t₀
  let yL : Spec (CommRingCat.of L) ⟶ G₁.X.left := y.left
  let χL := χ.toMul.hom.hom.left
  obtain ⟨z, hz⟩ := hχ.surj (yL (IsLocalRing.closedPoint L))
  let α := G₁.X.left.descResidueField (Scheme.stalkClosedPointTo yL)
  have hα : Spec.map α ≫ G₁.X.left.fromSpecResidueField _ = yL :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L _ yL
  let β := (G₁.X.left.residueFieldCongr hz.symm).hom ≫ χL.residueFieldMap z
  have hβ : Spec.map β ≫ G₁.X.left.fromSpecResidueField _ =
      Z.X.left.fromSpecResidueField z ≫ χL := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  obtain ⟨K, _, _, a, b, hab⟩ := exists_isAlgClosed_compositum β.hom α.hom
  let : Algebra k K := (b.comp (algebraMap k L)).toAlgebra
  let b' : L →ₐ[k] K := { b with commutes' := fun r => rfl }
  let x' : Spec (CommRingCat.of K) ⟶ Z.X.left :=
    Spec.map (CommRingCat.ofHom a) ≫ Z.X.left.fromSpecResidueField z
  have e : β ≫ CommRingCat.ofHom a = α ≫ CommRingCat.ofHom b := by
    ext r
    exact congrArg (fun f : _ →+* K => f r) hab
  have hx' : x' ≫ χL = Spec.map (CommRingCat.ofHom b) ≫ yL := by
    calc x' ≫ χL = Spec.map (CommRingCat.ofHom a) ≫ (Z.X.left.fromSpecResidueField z ≫ χL) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom a) ≫ (Spec.map β ≫ G₁.X.left.fromSpecResidueField _) := by
          rw [hβ]
      _ = Spec.map (β ≫ CommRingCat.ofHom a) ≫ G₁.X.left.fromSpecResidueField _ := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (α ≫ CommRingCat.ofHom b) ≫ G₁.X.left.fromSpecResidueField _ := by rw [e]
      _ = Spec.map (CommRingCat.ofHom b) ≫ (Spec.map α ≫ G₁.X.left.fromSpecResidueField _) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom b) ≫ yL := congrArg (Spec.map (CommRingCat.ofHom b) ≫ ·) hα
  have hw : x' ≫ Z.X.hom = ((algSpec R).obj (op (CommAlgCat.of R K))).hom := by
    have h1 : χL ≫ G₁.X.hom = Z.X.hom := Over.w χ.toMul.hom.hom
    have h2 : yL ≫ G₁.X.hom = ((algSpec R).obj (op (CommAlgCat.of R L))).hom := Over.w y
    rw [← h1, ← Category.assoc, hx', Category.assoc, h2, algSpec_obj_hom, algSpec_obj_hom,
      ← Spec.map_comp]
    rfl
  let x : Lie.AffinePoints Z.toGrp K := Over.homMk x' hw
  refine ⟨K, inferInstance, inferInstance, inferInstance, x, ?_⟩
  have hxχ : x ≫ χ.toMul.hom.hom = Lie.affineMap G₁.toGrp b' y := by
    apply Over.OverMorphism.ext
    change x' ≫ χL = ((algSpec R).map (CommAlgCat.ofHom b').op).left ≫ yL
    rw [hx']
    rfl
  have hval : Lie.characterValue (rationalCharacters.equivCharacterLattice Z χ) x =
      Units.map b'.toMonoidHom t₀ := by
    have h1 : Lie.characterValue (rationalCharacters.equivCharacterLattice Z χ) x =
        Lie.characterValue (𝟙 G₁) (Lie.affineMap G₁.toGrp b' y) := by
      rw [characterValue_id, ← hxχ]
      rfl
    rw [h1, characterValue_affineMap, characterValue_id]
    congr 1
    exact MulEquiv.apply_symm_apply _ _
  intro n hn h
  rw [hval, ← map_pow] at h
  have h' := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_one] at h'
  apply X_pow_ne_one (k := k) n hn
  apply b'.toRingHom.injective
  rw [map_one]
  exact h'

/-- **Cocharacters detect surjective characters.** Let `Z` be an affine commutative group scheme
locally of finite type over a field `k`, and `χ` a rational character whose underlying morphism
of schemes is surjective. Then some cocharacter `𝔾_m ⟶ Z` defined over `k` restricts `χ`
nontrivially. No smoothness, connectedness or multiplicative-type hypothesis is imposed. -/
theorem exists_gm_characterRestrict_ne_zero_of_surjective [IsAffineHom Z.toGrp.X.hom]
    [LocallyOfFiniteType Z.toGrp.X.hom] (χ : rationalCharacters Z.toGrp)
    (hχ : Surjective χ.toMul.hom.hom.left) :
    ∃ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, characterRestrict φ χ ≠ 0 := by
  obtain ⟨K, _, _, _, x, hx⟩ := exists_point_of_surjective χ hχ
  exact exists_gm_characterRestrict_ne_zero_of_point x hx

end Langlands.GroupScheme.CentralSurjectionImage

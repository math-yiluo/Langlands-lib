import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.Representation.Plancherel.TorusNormKernel.NormCharacter
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependence

/-! # Norm characters and the integer centralizer valuation

Let `E / k` be a finite field extension. The norm character `normCharacter χ` of a character
`χ` of a base change `Z_E` is natural for restriction along group-scheme morphisms, and the norm
character of the base change of a `k`-character `a` is `[E : k] • a`. Consequently, if the
restriction of `χ` along the base change of `s : S → Z` is the base change of a character `a`
of `S`, then the actual restriction of `normCharacter χ` along `s` is `[E : k] • a`. With the
integer centralizer valuation `ν` attached to a bijective restriction evaluation, the order of
the field norm of `χ(z_E)` is `[E : k]` times the pairing of `a` with `ν(z)`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.TorusNormKernel

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

section Functoriality

variable {D : Type u} [CommRing D] [Algebra F D] [Algebra E D] [IsScalarTower F E D]
variable {H T : GroupScheme (Spec (CommRingCat.of F))}

/-- `pointE` commutes with a group-scheme morphism and its base change. -/
theorem pointE_comp (f : H ⟶ T) (y : H.affinePoints (CommAlgCat.of F D)) :
    pointE F E D T (y ≫ f.hom.hom) =
      pointE F E D H y ≫ ((GroupScheme.baseChange (baseMap F E)).map f).hom.hom := by
  apply (baseChangePointsEquiv (baseMap F E) T
    ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D)))).injective
  rw [baseChangePointsEquiv_pointE, baseChangePointsEquiv_comp, baseChangePointsEquiv_pointE,
    Category.assoc]

/-- The value of a restricted `E`-character is the value at the image point. -/
theorem valueE_characterRestrict (f : H ⟶ T)
    (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T))
    (y : H.affinePoints (CommAlgCat.of F D)) :
    valueE (characterRestrict ((GroupScheme.baseChange (baseMap F E)).map f) χ) D y =
      valueE χ D (y ≫ f.hom.hom) := by
  rw [valueE_apply, valueE_apply, pointE_comp, Category.assoc]
  rfl

/-- The value of a base-changed character is the value of the original character. -/
theorem valueE_baseChange (χ : rationalCharacters T) (y : T.affinePoints (CommAlgCat.of F D)) :
    valueE (rationalCharacters.baseChange (baseMap F E) χ) D y =
      Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F D) (y ≫ χ.toMul.hom.hom) := by
  have key := rationalCharacters.characterEval_baseChange (baseMap F E) χ
    ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E D))) (pointE F E D T y)
  rw [baseChangePointsEquiv_pointE, characterEval_naturality] at key
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of D)).hom
      (characterEval (rationalCharacters.baseChange (baseMap F E) χ) _ (pointE F E D T y)).val =
    (Scheme.ΓSpecIso (CommRingCat.of D)).hom (characterEval χ _ y).val
  rw [key]
  rfl

end Functoriality

/-- The affine value of a natural multiple of a character is the power of the value. -/
theorem affineUnitsEquiv_nsmul {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} (n : ℕ)
    (χ : rationalCharacters H) (A : CommAlgCat.{u} R) (y : H.affinePoints A) :
    Gm.affineUnitsEquiv R A (y ≫ (n • χ).toMul.hom.hom) =
      Gm.affineUnitsEquiv R A (y ≫ χ.toMul.hom.hom) ^ n := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (characterEval (n • χ) _ y).val =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (characterEval χ _ y).val) ^ n
  rw [← natCast_zsmul, characterEval_zsmul, zpow_natCast, Units.val_pow_eq_pow_val]
  exact map_pow _ _ _

variable [FiniteDimensional F E]

/-- Norm characters are natural for restriction along group-scheme morphisms. -/
theorem normCharacter_characterRestrict {H T : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] [IsAffine T.X.left] (f : H ⟶ T)
    (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T)) :
    characterRestrict f (normCharacter χ) =
      normCharacter (characterRestrict ((GroupScheme.baseChange (baseMap F E)).map f) χ) := by
  apply rationalCharacters_ext_affinePoints
  intro A y
  apply (Gm.affineUnitsEquiv (CommRingCat.of F) A).injective
  have hl : y ≫ (characterRestrict f (normCharacter χ)).toMul.hom.hom =
      (y ≫ f.hom.hom) ≫ (normCharacter χ).toMul.hom.hom := by
    rw [Category.assoc]
    rfl
  rw [hl, normCharacter_affinePoints, normCharacter_affinePoints, valueE_characterRestrict,
    affinePointMap_apply, affinePointMap_apply, Category.assoc]

/-- The norm character of a base-changed character is its multiple by the degree. -/
theorem normCharacter_baseChange {T : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine T.X.left] (χ : rationalCharacters T) :
    normCharacter (rationalCharacters.baseChange (baseMap F E) χ) = Module.finrank F E • χ := by
  apply rationalCharacters_ext_affinePoints
  intro A y
  apply (Gm.affineUnitsEquiv (CommRingCat.of F) A).injective
  rw [normCharacter_affinePoints, valueE_baseChange, affineUnitsEquiv_nsmul]
  have hp : T.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[F] E ⊗[F] A)) y ≫ χ.toMul.hom.hom =
      GroupScheme.affinePointMap (Gm (Spec (CommRingCat.of F))).toGrp (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[F] E ⊗[F] A)) (y ≫ χ.toMul.hom.hom) := by
    rw [affinePointMap_apply, affinePointMap_apply, Category.assoc]
  rw [hp, Gm.affineUnitsEquiv_naturality]
  apply Units.ext
  exact Langlands.Algebra.tensorNorm_scalar _

end Langlands.Plancherel.TorusNormKernel

namespace Langlands.Geometry.Building.IntegerValuation

open Langlands.Plancherel.TorusNormKernel Langlands.BruhatTits

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine S.toGrp.X.left] [IsAffine Z.X.left]

/-- If the restriction of an `E`-character `α` of `Z_E` along the base change of `s` is the base
change of `a`, the actual restriction of its norm character along `s` is `[E : k] • a`. -/
theorem characterRestriction_normCharacter (s : S.toGrp ⟶ Z)
    {α : rationalCharacters (GaloisPointComparison.baseChanged k E Z)} {a : characterLattice S}
    (hα : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) α =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm a)) :
    Cartan.characterRestriction s (normCharacter α) = Module.finrank k E • a := by
  rw [Cartan.characterRestriction, AddMonoidHom.comp_apply, normCharacter_characterRestrict, hα,
    normCharacter_baseChange, map_nsmul]
  simp

variable (v : Valuation k (WithZero (Multiplicative ℤ)))

/-- The order of the norm character at `z` is the degree times the pairing of `a` with the
integer centralizer valuation of `z`. -/
theorem order_normCharacter (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {α : rationalCharacters (GaloisPointComparison.baseChanged k E Z)} {a : characterLattice S}
    (hα : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) α =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm a))
    (z : rationalPoints Z) :
    order v (rationalCharacterEval (normCharacter α) z) =
      Module.finrank k E * RealTorusSpace.eval S a (centralizerValuation v s h z).toAdd := by
  rw [← centralizerValuation_spec v s h z, characterRestriction_normCharacter s hα,
    ← natCast_zsmul, RealTorusSpace.eval_eq_pair, RealTorusSpace.eval_eq_pair,
    TensorProduct.tmul_smul, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_natCast]

/-- **Norm-value formula.** The order of the field norm of `α(z_E)` is the degree times the
pairing of `a` with the integer centralizer valuation of `z`. -/
theorem order_norm_rationalCharacterEval (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {α : rationalCharacters (GaloisPointComparison.baseChanged k E Z)} {a : characterLattice S}
    (hα : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) α =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm a))
    (z : rationalPoints Z) :
    order v (Units.map (Algebra.norm k : E →* k)
        (rationalCharacterEval α (GaloisPointComparison.rationalExtend k E Z z))) =
      Module.finrank k E * RealTorusSpace.eval S a (centralizerValuation v s h z).toAdd := by
  have hn : Units.map (Algebra.norm k : E →* k)
      (rationalCharacterEval α (GaloisPointComparison.rationalExtend k E Z z)) =
        rationalCharacterEval (normCharacter α) z :=
    Units.ext (normCharacter_eval α z).symm
  rw [hn, order_normCharacter v s h hα z]

/-- The degree-normalized order of the field norm of the value of an `E`-character of `Z_E` at
the scalar extension of a rational point of `Z`. -/
def characterNormOrder (α : rationalCharacters (GaloisPointComparison.baseChanged k E Z))
    (z : rationalPoints Z) : ℝ :=
  order v (Units.map (Algebra.norm k : E →* k)
      (rationalCharacterEval α (GaloisPointComparison.rationalExtend k E Z z))) /
    Module.finrank k E

/-- The degree-normalized norm order of `α` is the pairing of `a` with the integer centralizer
valuation. -/
theorem characterNormOrder_eq_eval (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {α : rationalCharacters (GaloisPointComparison.baseChanged k E Z)} {a : characterLattice S}
    (hα : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) α =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm a))
    (z : rationalPoints Z) :
    characterNormOrder v α z =
      RealTorusSpace.eval S a (centralizerValuation v s h z).toAdd := by
  have hd : (Module.finrank k E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [characterNormOrder, order_norm_rationalCharacterEval v s h hα z]
  exact mul_div_cancel_left₀ _ hd

end Langlands.Geometry.Building.IntegerValuation

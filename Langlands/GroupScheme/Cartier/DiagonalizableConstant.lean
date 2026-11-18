import Langlands.GroupScheme.Cartier.DiagonalizableRigidity
import Langlands.GroupScheme.Cartier.DiagonalizableGlue
import Langlands.AlgebraicGeometry.EtaleLocalSystem

/-! # The character presheaf of a diagonalizable group is the constant presheaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.LocallyConstantUnitPower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier.DiagonalizableCharacters

open RelativeMultiplicativeType Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

/-! ### The two constructions are inverse -/

lemma toLocallyConstant_ofLocallyConstant {T : Over S} (f : LocallyConstant T.left M) :
    toLocallyConstant (ofLocallyConstant (S := S) f) = f := by
  ext x
  rw [toLocallyConstant_apply, charValue_eq_iff]
  refine ⟨⟨{y | f y = f x}, f.isLocallyConstant.isOpen_fiber _⟩, show f x = f x from rfl, ?_⟩
  exact restrict_ofLocallyConstant_eq_evalChar _ f (f x) (fun y => y.2)

lemma ofLocallyConstant_toLocallyConstant {T : Over S}
    (χ : (characters (model S M)).obj (op T)) :
    ofLocallyConstant (toLocallyConstant χ) = χ := by
  apply act_ext
  intro V t
  rw [act_ofLocallyConstant]
  symm
  apply eq_lcPow_of_cover
  intro y
  obtain ⟨U, hU, hχ⟩ := charValue_spec χ (V.hom y)
  refine ⟨V.hom ⁻¹ᵁ U, hU, ?_⟩
  let b : Over.mk ((V.hom ⁻¹ᵁ U).ι ≫ V.hom) ⟶ V := Over.homMk (V.hom ⁻¹ᵁ U).ι
  have h1 := act_naturality χ b t
  rw [act_of_isEvalOn hχ (Over.mk ((V.hom ⁻¹ᵁ U).ι ≫ V.hom))] at h1
  · exact h1.symm
  · rintro _ ⟨z, rfl⟩
    change ((V.hom ⁻¹ᵁ U).ι ≫ V.hom) z ∈ U
    rw [Scheme.Hom.comp_apply]
    exact z.2

/-! ### The comparison isomorphism -/

variable (M) in
/-- Characters of `D_S(M)` over `T` are the locally constant functions `T.left → M`. -/
def charactersEquiv (T : Over S) :
    (characters (model S M)).obj (op T) ≃+ LocallyConstant T.left M where
  toFun := toLocallyConstant
  invFun := ofLocallyConstant
  left_inv := ofLocallyConstant_toLocallyConstant
  right_inv := toLocallyConstant_ofLocallyConstant
  map_add' := toLocallyConstant_add

lemma charactersEquiv_apply (T : Over S) (χ : (characters (model S M)).obj (op T)) :
    charactersEquiv M T χ = toLocallyConstant χ := rfl

lemma charactersEquiv_symm_apply (T : Over S) (f : LocallyConstant T.left M) :
    (charactersEquiv M T).symm f = ofLocallyConstant f := rfl

variable (S M) in
/-- **The canonical comparison.** The Cartier character presheaf of the diagonalizable model
`D_S(M)` is naturally isomorphic to the constant abelian presheaf with coefficients `M`. -/
def charactersIso :
    characters (model S M) ≅ EtaleLocalSystem.constant S (AddCommGrpCat.of M) :=
  NatIso.ofComponents
    (fun T => AddEquiv.toAddCommGrpIso
      ((charactersEquiv M T.unop).trans
        (EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T.unop).symm))
    (fun {T T'} a => by
      ext χ
      apply (EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T'.unop).injective
      ext x
      change toLocallyConstant ((characters (model S M)).map a χ) x =
        EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T'.unop
          ((EtaleLocalSystem.constant S (AddCommGrpCat.of M)).map a.unop.op
            ((EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T.unop).symm
              (toLocallyConstant χ))) x
      rw [EtaleLocalSystem.constantSections_map, AddEquiv.apply_symm_apply]
      exact toLocallyConstant_restrict a.unop χ x)

/-! ### Component formulas -/

/-- The component of the comparison on a character is its locally constant function. -/
lemma constantSections_charactersIso_hom (T : Over S) (χ : (characters (model S M)).obj (op T)) :
    EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T
      ((charactersIso S M).hom.app (op T) χ) = toLocallyConstant χ :=
  AddEquiv.apply_symm_apply _ _

lemma charactersIso_inv_app (T : Over S) (s : (EtaleLocalSystem.constant S (AddCommGrpCat.of M)).obj (op T)) :
    (charactersIso S M).inv.app (op T) s =
      ofLocallyConstant (EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T s) :=
  rfl

/-- **Normalization.** The evaluation character at `m` corresponds to the constant function
with value `m`. -/
lemma constantSections_charactersIso_hom_evalChar (T : Over S) (m : M) :
    EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T
      ((charactersIso S M).hom.app (op T) (evalChar T m)) = LocallyConstant.const T.left m := by
  rw [constantSections_charactersIso_hom, toLocallyConstant_evalChar]

lemma charactersIso_inv_app_const (T : Over S) (m : M) :
    (charactersIso S M).inv.app (op T)
        ((EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T).symm
          (LocallyConstant.const T.left m)) = evalChar T m := by
  rw [charactersIso_inv_app, AddEquiv.apply_symm_apply, ofLocallyConstant_const]

/-- A character corresponds to the constant function `m` exactly when it is the evaluation
character at `m`. -/
lemma constantSections_charactersIso_hom_eq_const_iff (T : Over S)
    (χ : (characters (model S M)).obj (op T)) (m : M) :
    EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T
        ((charactersIso S M).hom.app (op T) χ) = LocallyConstant.const T.left m ↔
      χ = evalChar T m := by
  rw [constantSections_charactersIso_hom, ← toLocallyConstant_evalChar]
  exact (charactersEquiv M T).injective.eq_iff

/-- **Local characterization.** The value at `x` of the function attached to `χ` is `m`
exactly when `χ` restricts to the evaluation character at `m` on an open neighbourhood
of `x`. -/
lemma constantSections_charactersIso_hom_apply_eq_iff (T : Over S)
    (χ : (characters (model S M)).obj (op T)) (x : T.left) (m : M) :
    EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T
        ((charactersIso S M).hom.app (op T) χ) x = m ↔
      ∃ U : T.left.Opens, x ∈ U ∧
        (characters (model S M)).map (opensι T U).op χ = evalChar (opensOver T U) m := by
  rw [constantSections_charactersIso_hom]
  exact charValue_eq_iff χ x m

/-- **Restriction-compatible characterization.** The restriction of `χ` along `a : T' ⟶ T` is
the evaluation character at `m` exactly when the function attached to `χ` is constantly `m`
on the image of `a`. -/
lemma restrict_eq_evalChar_iff {T T' : Over S} (a : T' ⟶ T)
    (χ : (characters (model S M)).obj (op T)) (m : M) :
    (characters (model S M)).map a.op χ = evalChar T' m ↔
      ∀ x : T'.left, EtaleLocalSystem.constantSections S (AddCommGrpCat.of M) T
        ((charactersIso S M).hom.app (op T) χ) (a.left x) = m := by
  rw [constantSections_charactersIso_hom]
  constructor
  · intro h x
    rw [← toLocallyConstant_restrict, h, toLocallyConstant_evalChar]
    rfl
  · intro h
    apply (charactersEquiv M T').injective
    rw [charactersEquiv_apply, charactersEquiv_apply, toLocallyConstant_evalChar]
    ext x
    rw [toLocallyConstant_restrict]
    exact h x

end Langlands.GroupScheme.Cartier.DiagonalizableCharacters

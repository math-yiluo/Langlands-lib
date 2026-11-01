import Langlands.Shimura.PEL.HarrisTaylorPositiveLiePullback
import Langlands.Shimura.PEL.HarrisTaylorLieClasses
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Actual positive Lie and dimension moduli presheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite NumberField Algebra
open Langlands.AbelianScheme

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L]
    {K : Type} [Field K] [NumberField K] [Algebra L K]
    (E : Type) [Field E] [Algebra E K]
    {S T : Scheme.{0}} (s : S ⟶ Spec (.of K)) (b : T ⟶ S)
    {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A] (n : ℕ)

/-- The actual positive Lie predicate on rational action classes survives arbitrary pullback. -/
theorem lieCompatibilityClassCondition_pullback
    (q : RationalAlgebraAction.IsoClass S A)
    (hq : LieCompatibilityClassCondition L E s n q) :
    LieCompatibilityClassCondition L E (b ≫ s) n
      (RationalAlgebraAction.pullbackClass b q) := by
  obtain ⟨X, rfl⟩ := RationalAlgebraAction.classOf_surjective q
  exact lieCompatibility_pullback s b L X.abelianScheme X.action E n hq

variable [NumberField E]

/-- Both geometric dimension and positive Lie compatibility hold on the same pulled-back object. -/
theorem dimensionLieCondition_pullback (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    (h : DimensionLieCondition L E s n B i) :
    DimensionLieCondition L E (b ≫ s) n ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) :=
  ⟨prescribedRelativeDimension_baseChange E B n h.1 b,
    lieCompatibility_pullback s b L B i E n h.2⟩

/-- Pullback retains one actual representative satisfying dimension and positive Lie compatibility. -/
theorem dimensionLieActionClassCondition_pullback
    (q : RationalAlgebraAction.IsoClass S A)
    (hq : DimensionLieActionClassCondition L E s n q) :
    DimensionLieActionClassCondition L E (b ≫ s) n
      (RationalAlgebraAction.pullbackClass b q) := by
  obtain ⟨X, hX, hgood⟩ := hq
  refine ⟨(RationalAlgebraAction.pullback b).obj X, ?_, ?_⟩
  · rw [← hX]
    rfl
  · exact dimensionLieCondition_pullback L E s b n X.abelianScheme X.action hgood

/-- The joint dimension and actual positive Lie image is stable in the actual action presheaf. -/
def dimensionLieActionSubfunctor :
    Subfunctor (RationalAlgebraAction.isoClassOverPresheaf
      (Spec (CommRingCat.of K)) A) where
  obj X := {q | DimensionLieActionClassCondition L E X.unop.hom n q}
  map {X Y} f q hq := by
    change DimensionLieActionClassCondition L E Y.unop.hom n
      (RationalAlgebraAction.pullbackClass f.unop.left q)
    rw [← Over.w f.unop]
    exact dimensionLieActionClassCondition_pullback L E X.unop.hom f.unop.left n q hq

/-- Actual rational action classes with one dimension-and-positive-Lie representative, over Spec K. -/
def dimensionLieActionPresheaf : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ Type 1 :=
  (dimensionLieActionSubfunctor L E n (A := A)).toFunctor

/-- Forgetting the joint restriction is the natural inclusion into actual rational action classes. -/
def dimensionLieActionPresheafInclusion :
    dimensionLieActionPresheaf L E n (A := A) ⟶
      RationalAlgebraAction.isoClassOverPresheaf (Spec (CommRingCat.of K)) A :=
  (dimensionLieActionSubfunctor L E n).ι

@[simp]
theorem dimensionLieActionPresheaf_obj (X : Over (Spec (CommRingCat.of K))) :
    (dimensionLieActionPresheaf L E n (A := A)).obj (op X) =
      DimensionLieActionClass L E X.hom n (A := A) := rfl

@[simp]
theorem dimensionLieActionPresheaf_map_val
    {X Y : Over (Spec (CommRingCat.of K))} (f : Y ⟶ X)
    (q : DimensionLieActionClass L E X.hom n (A := A)) :
    ((dimensionLieActionPresheaf L E n).map f.op q).val =
      RationalAlgebraAction.pullbackClass f.left q.val := rfl

@[simp]
theorem dimensionLieActionPresheaf_map_classOf_val
    {X Y : Over (Spec (CommRingCat.of K))} (f : Y ⟶ X)
    (Z : RationalAlgebraAction X.left A)
    (hZ : DimensionLieCondition L E X.hom n Z.abelianScheme Z.action) :
    ((dimensionLieActionPresheaf L E n).map f.op
      (dimensionLieActionClassOf L E X.hom n Z hZ)).val =
        RationalAlgebraAction.classOf ((RationalAlgebraAction.pullback f.left).obj Z) := rfl

/-- The inclusion is injective at every actual base scheme. -/
theorem dimensionLieActionPresheafInclusion_injective
    (X : Over (Spec (CommRingCat.of K))) :
    Function.Injective ((dimensionLieActionPresheafInclusion L E n (A := A)).app (op X)) :=
  Subtype.val_injective

end Langlands.Shimura.HarrisTaylor

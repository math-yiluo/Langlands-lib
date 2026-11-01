import Langlands.AlgebraicGeometry.Picard.TwoAxisNormalModel
import Langlands.AlgebraicGeometry.Picard.SelfProductBaseChange
import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality
import Langlands.AlgebraicGeometry.Picard.ValuationRingTwoAxisExtensionStatement

/-! # Pulling an actual normal-model extension back to the original base -/

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.NoetherianApproximation

namespace TwoAxisNormalModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {A : AbelianScheme (Spec (CommRingCat.of R))}
  {D : LineBundle (mumfordProduct ((baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left}
  (M : TwoAxisNormalModel A D)

/-- The actual comparison between the total self-products. -/
abbrev totalProductMap :
    (mumfordProduct A).left ⟶ (mumfordProduct M.model).left :=
  cartesianMumfordProductMap A M.model M.totalMap
    (Spec.map (CommRingCat.ofHom (algebraMap M.T R))) M.totalPullback.w

/-- Pull an actual line bundle on the total normal model to the original product. -/
def extensionPullback (E : LineBundle (mumfordProduct M.model).left) :
    LineBundle (mumfordProduct A).left :=
  (LineBundle.pullback M.totalProductMap).obj E

/-- The generic and total product comparisons commute with the precise
canonical product restriction maps. -/
theorem product_square :
    mumfordProductBaseChangeMap A
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ M.totalProductMap =
      cartesianMumfordProductMap
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)
        ((baseChange (Spec.map (CommRingCat.ofHom
          (algebraMap M.T (FractionRing M.T))))).obj M.model)
        M.genericMap
        (Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K M.T)))
        M.genericSnd ≫
      mumfordProductBaseChangeMap M.model
        (Spec.map (CommRingCat.ofHom (algebraMap M.T (FractionRing M.T)))) := by
  change cartesianSelfProductMap _ A.X.hom
      (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      _ pullback.condition ≫
    cartesianSelfProductMap A.X.hom M.model.X.hom M.totalMap _ M.totalPullback.w =
    cartesianSelfProductMap _ _ M.genericMap _ M.genericSnd ≫
    cartesianSelfProductMap _ M.model.X.hom
      (pullback.fst M.model.X.hom (Spec.map (CommRingCat.ofHom
        (algebraMap M.T (FractionRing M.T))))) _ pullback.condition
  apply pullback.hom_ext <;>
    simp only [Category.assoc, cartesianSelfProductMap_fst,
      cartesianSelfProductMap_snd, cartesianSelfProductMap_fst_assoc,
      cartesianSelfProductMap_snd_assoc, M.genericFst]
    <;> rfl

/-- An actual extension of the model bundle gives an actual extension of `D`. -/
theorem exists_extension
    (E : LineBundle (mumfordProduct M.model).left)
    (hE : Nonempty ((Scheme.Modules.pullback
      (mumfordProductBaseChangeMap M.model (Spec.map (CommRingCat.ofHom
        (algebraMap M.T (FractionRing M.T)))))).obj E.obj ≅ M.bundle.obj)) :
    ∃ F : LineBundle (mumfordProduct A).left,
      Nonempty ((Scheme.Modules.pullback (mumfordProductBaseChangeMap A
        (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj F.obj ≅ D.obj) := by
  obtain ⟨eE⟩ := hE
  obtain ⟨eM⟩ := M.comparison
  refine ⟨M.extensionPullback E, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp _ M.totalProductMap).app E.obj ≪≫
    (Scheme.Modules.pullbackCongr M.product_square).app E.obj ≪≫
    ((Scheme.Modules.pullbackComp _ _).app E.obj).symm ≪≫
    (Scheme.Modules.pullback _).mapIso eE ≪≫ eM

end TwoAxisNormalModel

/-- The remaining extension property for normal rings of finite type over the
integers and their canonical fraction fields. This defines a proposition. -/
def NormalFiniteTypeTwoAxisExtensionProperty : Prop :=
  ∀ (T : Type u) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [Algebra.FiniteType ℤ T]
    (B : AbelianScheme (Spec (CommRingCat.of T))),
    let b := Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))
    let G := (baseChange b).obj B
    ∀ (N : LineBundle (mumfordProduct G).left),
      Nonempty ((Scheme.Modules.pullback (mumfordSection G)).obj N.obj ≅
        Langlands.Scheme.Modules.structureSheaf G.X.left) →
      Nonempty ((Scheme.Modules.pullback (twoAxisSecond G)).obj N.obj ≅
        Langlands.Scheme.Modules.structureSheaf G.X.left) →
      ∃ E : LineBundle (mumfordProduct B).left,
        Nonempty ((Scheme.Modules.pullback (mumfordProductBaseChangeMap B b)).obj
          E.obj ≅ N.obj)

/-- Normal finite-stage existence and actual extension on those finite normal
bases suffice for the exact arbitrary-valuation bundle conclusion. -/
theorem valuationRingTwoAxisExtension_of_normalFiniteType
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    (hExtend : NormalFiniteTypeTwoAxisExtensionProperty.{u}) :
    ValuationRingTwoAxisExtensionStatement.{u} := by
  intro R _ _ _ K _ _ _ A
  dsimp only
  intro D e₁ e₂
  obtain ⟨M, -⟩ := exists_twoAxisNormalModel hNormal A D e₁ e₂ (∅ : Finset R)
  let := M.normal
  let : Algebra.FiniteType ℤ M.T := (Subalgebra.fg_iff_finiteType _).mp M.fg
  obtain ⟨E, hE⟩ := hExtend M.T M.model M.bundle M.first M.second
  exact M.exists_extension E hE

end Langlands.AbelianScheme

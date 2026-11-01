import Langlands.AlgebraicGeometry.Picard.TwoAxisExtensionReduction
import Langlands.AlgebraicGeometry.Picard.NormalNoetherianFractionFieldSections
import Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionReduction
import Langlands.AlgebraicGeometry.NoetherianApproximation.NormalFiniteTypeSubalgebraProof
import Mathlib.CategoryTheory.Yoneda

/-! # Two-axis class extension from an explicit representation -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle

variable {S X T : Scheme.{u}} (A : Langlands.AbelianScheme S) (p : X ⟶ S)
  (r : (classPresheaf A).RepresentableBy (Over.mk p))

/-- A supplied representation identifies actual maps over the base with the
actual compatible two-axis-rigidified line-bundle classes. -/
def sectionClassEquiv (b : T ⟶ S) :
    {s : T ⟶ X // s ≫ p = b} ≃ Classes A (Over.mk b) :=
  (show {s : T ⟶ X // s ≫ p = b} ≃ (Over.mk b ⟶ Over.mk p) from
    { toFun := fun s => Over.homMk s.val s.property
      invFun := fun f => ⟨f.left, Over.w f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans r.homEquiv

/-- The equivalence commutes with restriction from an actual section over the
base, along the exact specified test-scheme map. -/
theorem sectionClassEquiv_toBase (b : T ⟶ S)
    (s : {s : S ⟶ X // s ≫ p = 𝟙 S}) :
    sectionClassEquiv A p r b
        ⟨b ≫ s.val, by rw [Category.assoc, s.property, Category.comp_id]⟩ =
      classesPullback A (TwoAxisFamily.toBase b)
        (sectionClassEquiv A p r (𝟙 S) s) := by
  exact r.homEquiv_comp (TwoAxisFamily.toBase b) (Over.homMk s.val s.property)

variable (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (B : Langlands.AbelianScheme (Spec R))
  {Y : Scheme.{u}} (q : Y ⟶ Spec R)
  (e : (classPresheaf B).RepresentableBy (Over.mk q))
  [IsSeparated q] [LocallyOfFiniteType q] [FormallyUnramified q]

include e in
/-- For an explicitly represented presheaf, the published discrete valuative
section theorem gives surjectivity on classes over a normal noetherian domain. -/
theorem classesPullback_surjective_of_normal_discreteValuativeExistence
    (hq : DiscreteValuativeCriterion.Existence q) :
    Function.Surjective (classesPullback B (TwoAxisFamily.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))) := by
  intro c
  obtain ⟨s, hs⟩ :=
    (fractionFieldSectionRestriction_bijective_of_normal_discreteValuativeExistence
      R K q hq).surjective
        ((sectionClassEquiv B q e
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).symm c)
  refine ⟨sectionClassEquiv B q e (𝟙 (Spec R)) s, ?_⟩
  rw [← sectionClassEquiv_toBase]
  change sectionClassEquiv B q e
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (fractionFieldSectionRestriction R K q s) = c
  rw [hs, Equiv.apply_symm_apply]

open Langlands.AbelianScheme Langlands.Scheme.Modules

include e in
/-- The explicit representation and discrete valuative existence produce an
actual bundle extension along the canonical product map. -/
theorem actualBundleExtension_of_normal_discreteValuativeExistence
    (hq : DiscreteValuativeCriterion.Existence q)
    (D : LineBundle (mumfordProduct ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B)).left)
    (hα : Nonempty ((Scheme.Modules.pullback
      (mumfordSection ((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B))).obj D.obj ≅
      structureSheaf ((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B).X.left))
    (hβ : Nonempty ((Scheme.Modules.pullback
      (twoAxisSecond ((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B))).obj D.obj ≅
      structureSheaf ((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B).X.left)) :
    ∃ E : LineBundle (mumfordProduct B).left,
      Nonempty (((LineBundle.pullback (mumfordProductBaseChangeMap B
        (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj E).obj ≅ D.obj) :=
  actualBundleExtension_of_classesPullback_surjective B
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (classesPullback_surjective_of_normal_discreteValuativeExistence R K B q e hq)
    D hα hβ

end Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle

namespace Langlands.AbelianScheme

/-- The published normal-subalgebra theorem discharges the algebraic premise
of the normal-model reduction; actual finite-normal extension remains explicit. -/
theorem valuationRingTwoAxisExtension_of_normalFiniteTypeExtension
    (hExtend : NormalFiniteTypeTwoAxisExtensionProperty.{u}) :
    ValuationRingTwoAxisExtensionStatement.{u} :=
  valuationRingTwoAxisExtension_of_normalFiniteType
    Langlands.AlgebraicGeometry.NoetherianApproximation.normalFiniteTypeSubalgebra
    hExtend

end Langlands.AbelianScheme

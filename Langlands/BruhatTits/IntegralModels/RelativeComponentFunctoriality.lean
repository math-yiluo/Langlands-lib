import Langlands.BruhatTits.IntegralModels.ConnectedFactorization
import Langlands.BruhatTits.IntegralModels.ModelMorphism
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof

/-! # Functoriality and coefficient recovery of supplied neutral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

namespace RelativeComponentModelData

variable (D : RelativeComponentModelData R K G)

/-- The neutral representative of a smooth full model has geometrically
connected fibres, even when the supplied data records only connectedness. -/
theorem neutral_geometricallyConnected : GeometricallyConnected D.neutral.group.X.hom := by
  obtain ⟨N, j, hj, -, hN⟩ := RelativeIdentityComponent.smoothExistence
    (Spec (CommRingCat.of R)) D.full.group D.full_smooth
  let : GeometricallyConnected N.X.hom := hN
  exact D.isRelativeComponent.geometricallyConnected hj

variable {M : IntegralModel R K H} [GeometricallyConnected M.group.X.hom]
  {f : H ⟶ G}

/-- Factor an actual compatible map from a geometrically connected model
through the neutral representative, retaining its original generic map. -/
def toNeutral (φ : M.Hom D.full f) : M.Hom D.neutral f where
  hom := RelativeIdentityComponent.factor φ.hom D.isRelativeComponent
  generic_comm := by
    have hi : (GroupScheme.baseChange (Spec.algebraMap R K)).map D.inclusion.hom ≫
        D.full.genericIso.hom = D.neutral.genericIso.hom := by
      simpa only [Category.comp_id] using D.inclusion.generic_comm
    rw [← hi, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      RelativeIdentityComponent.factor_comp]
    exact φ.generic_comm

@[reassoc (attr := simp)]
theorem toNeutral_comp (φ : M.Hom D.full f) :
    (D.toNeutral φ).hom ≫ D.inclusion.hom = φ.hom :=
  RelativeIdentityComponent.factor_comp φ.hom D.isRelativeComponent

end RelativeComponentModelData

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}

/-- Every actual full-model map restricts canonically to the neutral models. -/
def ofFull (φ : source.full.Hom target.full (𝟙 G)) :
    RelativeComponentModelHom source target := by
  letI := source.neutral_geometricallyConnected
  let ψ : source.neutral.Hom target.full (𝟙 G) := by
    simpa only [Category.id_comp] using source.inclusion.comp φ
  exact
    { full := φ
      neutral := target.toNeutral ψ
      component_comm := target.toNeutral_comp ψ }

@[simp] theorem ofFull_full (φ : source.full.Hom target.full (𝟙 G)) :
    (ofFull φ).full = φ := rfl

/-- The compatible restriction is unique as an actual integral-model map. -/
theorem existsUnique_neutral (φ : source.full.Hom target.full (𝟙 G)) :
    ∃! ψ : source.neutral.Hom target.neutral (𝟙 G),
      ψ.hom ≫ target.inclusion.hom = source.inclusion.hom ≫ φ.hom :=
  ⟨(ofFull φ).neutral, (ofFull φ).component_comm,
    fun _ _ => Subsingleton.elim _ _⟩

end RelativeComponentModelHom

namespace RelativeComponentModelData

variable (D E : RelativeComponentModelData R K G)

/-- Full-model recovery over the identity of the original generic group
canonically recovers the actual neutral models. -/
def neutralIso (e : D.full.Iso E.full (CategoryTheory.Iso.refl G)) :
    D.neutral.Iso E.neutral (CategoryTheory.Iso.refl G) :=
  IntegralModel.Iso.ofHoms (RelativeComponentModelHom.ofFull e.toHom).neutral
    (RelativeComponentModelHom.ofFull e.symm.toHom).neutral

@[reassoc]
theorem neutralIso_hom_comp (e : D.full.Iso E.full (CategoryTheory.Iso.refl G)) :
    (D.neutralIso E e).iso.hom ≫ E.inclusion.hom = D.inclusion.hom ≫ e.iso.hom :=
  (RelativeComponentModelHom.ofFull e.toHom).component_comm

/-- The equality concerns the original generic-point subgroup images. -/
theorem neutral_integralPoints_eq (e : D.full.Iso E.full (CategoryTheory.Iso.refl G)) :
    D.neutral.integralPoints = E.neutral.integralPoints :=
  (D.neutralIso E e).integralPoints_eq

section Coefficients

variable (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- Pull back both actual models and their inclusion along a coefficient
square; the pulled-back neutral model represents the relative component. -/
def baseChange : RelativeComponentModelData A L
    ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G) where
  full := D.full.baseChange A L
  neutral := D.neutral.baseChange A L
  full_smooth := D.full.isSmooth_baseChange A L D.full_smooth
  neutral_smooth := D.neutral.isSmooth_baseChange A L D.neutral_smooth
  neutral_connectedFibres := by
    let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
    apply IntegralModel.hasConnectedFibres_of_geometricallyConnected
    change GeometricallyConnected (pullback.snd D.neutral.group.X.hom
      (Spec.algebraMap R A))
    infer_instance
  inclusion :=
    { hom := (GroupScheme.baseChange (Spec.algebraMap R A)).map D.inclusion.hom
      generic_comm := by
        have h := D.neutral.baseChangeGenericIso_naturality A L D.full D.inclusion
        rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
        exact h }
  isRelativeComponent := by
    let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
    exact D.isRelativeComponent.baseChange (Spec.algebraMap R A)

@[simp] theorem baseChange_full : (D.baseChange A L).full = D.full.baseChange A L := rfl

@[simp] theorem baseChange_neutral :
    (D.baseChange A L).neutral = D.neutral.baseChange A L := rfl

@[simp] theorem baseChange_inclusion_hom :
    (D.baseChange A L).inclusion.hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map D.inclusion.hom := rfl

variable (E' : RelativeComponentModelData A L
  ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))

/-- A supplied full-model recovery after coefficient base change recovers the
neutral model with its original coefficient-square generic identification. -/
def baseChangeNeutralIso
    (e : (D.full.baseChange A L).Iso E'.full
      (CategoryTheory.Iso.refl ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))) :
    (D.neutral.baseChange A L).Iso E'.neutral
      (CategoryTheory.Iso.refl ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)) :=
  (D.baseChange A L).neutralIso E' e

@[reassoc]
theorem baseChangeNeutralIso_hom_comp
    (e : (D.full.baseChange A L).Iso E'.full
      (CategoryTheory.Iso.refl ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))) :
    (D.baseChangeNeutralIso A L E' e).iso.hom ≫ E'.inclusion.hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map D.inclusion.hom ≫ e.iso.hom :=
  (D.baseChange A L).neutralIso_hom_comp E' e

/-- Recovery gives equality of the exact upstairs neutral integral-point
images, rather than only an abstract isomorphism of special fibres. -/
theorem baseChange_neutral_integralPoints_eq
    (e : (D.full.baseChange A L).Iso E'.full
      (CategoryTheory.Iso.refl ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))) :
    (D.neutral.baseChange A L).integralPoints = E'.neutral.integralPoints :=
  (D.baseChangeNeutralIso A L E' e).integralPoints_eq

end Coefficients
end RelativeComponentModelData

/-- Functoriality and exact recovery for any supplied smooth full models and
their actual relative identity components, in arbitrary characteristic. -/
def RelativeComponentFunctorialityStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (D E : RelativeComponentModelData R K G),
    (∀ φ : D.full.Hom E.full (𝟙 G),
      ∃! ψ : D.neutral.Hom E.neutral (𝟙 G),
        ψ.hom ≫ E.inclusion.hom = D.inclusion.hom ≫ φ.hom) ∧
    (∀ e : D.full.Iso E.full (CategoryTheory.Iso.refl G),
      ∃ e₀ : D.neutral.Iso E.neutral (CategoryTheory.Iso.refl G),
        e₀.iso.hom ≫ E.inclusion.hom = D.inclusion.hom ≫ e.iso.hom ∧
          D.neutral.integralPoints = E.neutral.integralPoints)

/-- Proof of the functoriality and exact recovery statement. -/
theorem relativeComponentFunctoriality : RelativeComponentFunctorialityStatement.{u} := by
  intro R K _ _ _ _ _ G D E
  exact ⟨RelativeComponentModelHom.existsUnique_neutral,
    fun e => ⟨D.neutralIso E e, D.neutralIso_hom_comp E e,
      D.neutral_integralPoints_eq E e⟩⟩

end Langlands.BruhatTits.IntegralModels

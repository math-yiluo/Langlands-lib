import Langlands.Geometry.FormalGroup.AtlasLocalTests

/-! # Localized chart tuples with explicit overlap equations -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (X : BasicAtlas O R σ)

/-- A localization map can be cancelled when comparing coefficient maps. -/
theorem localMap_ext {A B : CommAlgCat.{v} R} (a : X.opens)
    {f g : X.localAlgebra A a ⟶ B}
    (h : X.localizationMap A a ≫ f = X.localizationMap A a ≫ g) : f = g := by
  have he : f.hom.toRingHom = g.hom.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A a.val))
    exact congrArg (fun k : A ⟶ B => k.hom.toRingHom) h
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  exact RingHom.congr_fun he

/-- The localization factor of a test is natural under a further test map. -/
theorem testFactor_comp {A : CommAlgCat.{v} R} (t : X.ChartTest A)
    {B : CommAlgCat.{v} R} (ψ : t.algebra ⟶ B)
    (hb : IsUnit (algebraMap R B t.chart.val)) :
    X.testFactor t ≫ ψ = X.testFactor ⟨B, t.map ≫ ψ, t.chart, hb⟩ := by
  apply X.localMap_ext t.chart
  rw [← Category.assoc, X.localizationMap_testFactor t]
  exact (X.localizationMap_testFactor ⟨B, t.map ≫ ψ, t.chart, hb⟩).symm

/-- The actual coefficient algebra of the pairwise principal-open intersection. -/
abbrev overlapAlgebra (A : CommAlgCat.{v} R) (a b : X.opens) : CommAlgCat.{v} R :=
  CommAlgCat.of R (Localization.Away (algebraMap R A a.val * algebraMap R A b.val))

/-- The structural test map to the pairwise intersection. -/
def overlapMap (A : CommAlgCat.{v} R) (a b : X.opens) : A ⟶ X.overlapAlgebra A a b :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom R A
    (Localization.Away (algebraMap R A a.val * algebraMap R A b.val)))

/-- Both chart generators are invertible on the actual overlap. -/
theorem overlapUnitLeft (A : CommAlgCat.{v} R) (a b : X.opens) :
    IsUnit (algebraMap R (X.overlapAlgebra A a b) a.val) := by
  rw [IsScalarTower.algebraMap_apply R A (X.overlapAlgebra A a b)]
  apply isUnit_of_mul_isUnit_left (y := algebraMap A (X.overlapAlgebra A a b)
    (algebraMap R A b.val))
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := X.overlapAlgebra A a b) (algebraMap R A a.val * algebraMap R A b.val)
  exact (algebraMap A (X.overlapAlgebra A a b)).map_mul _ _ ▸ h

/-- Both chart generators are invertible on the actual overlap. -/
theorem overlapUnitRight (A : CommAlgCat.{v} R) (a b : X.opens) :
    IsUnit (algebraMap R (X.overlapAlgebra A a b) b.val) := by
  rw [IsScalarTower.algebraMap_apply R A (X.overlapAlgebra A a b)]
  apply isUnit_of_mul_isUnit_right (x := algebraMap A (X.overlapAlgebra A a b)
    (algebraMap R A a.val))
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := X.overlapAlgebra A a b) (algebraMap R A a.val * algebraMap R A b.val)
  exact (algebraMap A (X.overlapAlgebra A a b)).map_mul _ _ ▸ h

/-- Restrict the left localization to the actual overlap. -/
def overlapFromLeft (A : CommAlgCat.{v} R) (a b : X.opens) :
    X.localAlgebra A a ⟶ X.overlapAlgebra A a b :=
  X.testFactor ⟨X.overlapAlgebra A a b, X.overlapMap A a b, a, X.overlapUnitLeft A a b⟩

/-- Restrict the right localization to the same actual overlap. -/
def overlapFromRight (A : CommAlgCat.{v} R) (a b : X.opens) :
    X.localAlgebra A b ⟶ X.overlapAlgebra A a b :=
  X.testFactor ⟨X.overlapAlgebra A a b, X.overlapMap A a b, b, X.overlapUnitRight A a b⟩

/-- Every simultaneous chart test factors through the universal overlap. -/
def overlapFactor {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    X.overlapAlgebra A a b ⟶ B :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom
    (algebraMap R A a.val * algebraMap R A b.val) (f := φ.hom)
    (by
      change IsUnit (φ.hom (algebraMap R A a.val * algebraMap R A b.val))
      rw [map_mul, φ.hom.commutes, φ.hom.commutes]
      exact ha.mul hb))

/-- The overlap lift recovers the original coefficient map. -/
@[simp]
theorem overlapMap_factor {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    X.overlapMap A a b ≫ X.overlapFactor φ a b ha hb = φ := by
  ext z
  exact IsLocalization.Away.lift_eq
    (algebraMap R A a.val * algebraMap R A b.val)
    (by
      change IsUnit (φ.hom (algebraMap R A a.val * algebraMap R A b.val))
      rw [map_mul, φ.hom.commutes, φ.hom.commutes]
      exact ha.mul hb) z

/-- The universal overlap lift agrees with the left test factor. -/
theorem overlapFromLeft_factor {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    X.overlapFromLeft A a b ≫ X.overlapFactor φ a b ha hb =
      X.testFactor ⟨B, φ, a, ha⟩ := by
  apply X.localMap_ext a
  rw [← Category.assoc]
  change (X.localizationMap A a ≫ X.testFactor
    ⟨X.overlapAlgebra A a b, X.overlapMap A a b, a, X.overlapUnitLeft A a b⟩) ≫ _ = _
  rw [X.localizationMap_testFactor
    ⟨X.overlapAlgebra A a b, X.overlapMap A a b, a, X.overlapUnitLeft A a b⟩,
    X.overlapMap_factor, X.localizationMap_testFactor ⟨B, φ, a, ha⟩]

/-- The universal overlap lift agrees with the right test factor. -/
theorem overlapFromRight_factor {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    X.overlapFromRight A a b ≫ X.overlapFactor φ a b ha hb =
      X.testFactor ⟨B, φ, b, hb⟩ := by
  apply X.localMap_ext b
  rw [← Category.assoc]
  change (X.localizationMap A b ≫ X.testFactor
    ⟨X.overlapAlgebra A a b, X.overlapMap A a b, b, X.overlapUnitRight A a b⟩) ≫ _ = _
  rw [X.localizationMap_testFactor
    ⟨X.overlapAlgebra A a b, X.overlapMap A a b, b, X.overlapUnitRight A a b⟩,
    X.overlapMap_factor, X.localizationMap_testFactor ⟨B, φ, b, hb⟩]

/-- One actual nilpotent tuple over the canonical localization of each chart. -/
abbrev LocalizedFamily (A : CommAlgCat.{v} R) :=
  (a : X.opens) → X.ChartPoint (X.localAlgebra A a) a (X.localUnit A a)

/-- The actual transition equation on every universal pairwise overlap. -/
def OverlapCompatible {A : CommAlgCat.{v} R} (z : X.LocalizedFamily A) : Prop :=
  ∀ a b : X.opens,
    X.transitionPoints (X.overlapAlgebra A a b) a b
      (X.overlapUnitLeft A a b) (X.overlapUnitRight A a b)
      (pointMap (X.chart a) (X.overlapFromLeft A a b) (X.localUnit A a)
        (X.overlapUnitLeft A a b) (z a)) =
      pointMap (X.chart b) (X.overlapFromRight A a b) (X.localUnit A b)
        (X.overlapUnitRight A a b) (z b)

/-- The solution submodule of the explicit pairwise-overlap equations. -/
def overlapSubmodule (A : CommAlgCat.{v} R) : Submodule O (X.LocalizedFamily A) where
  carrier := X.OverlapCompatible
  zero_mem' := by
    intro a b
    change X.transitionPoints _ _ _ _ _ (pointMap _ _ _ _ 0) = pointMap _ _ _ _ 0
    rw [map_zero, map_zero, map_zero]
  add_mem' := by
    intro z w hz hw a b
    change X.transitionPoints _ _ _ _ _ (pointMap _ _ _ _ (z a + w a)) =
      pointMap _ _ _ _ (z b + w b)
    rw [map_add, map_add, map_add, hz a b, hw a b]
  smul_mem' := by
    intro c z hz a b
    change X.transitionPoints _ _ _ _ _ (pointMap _ _ _ _ (c • z a)) =
      pointMap _ _ _ _ (c • z b)
    rw [map_smul, map_smul, map_smul, hz a b]

/-- Actual local chart tuples satisfying every pairwise-overlap equation. -/
abbrev OverlapPoint (A : CommAlgCat.{v} R) := X.overlapSubmodule A

/-- Full compatible families give matching universal localized chart tuples. -/
theorem localizedCoordinates_compatible (A : CommAlgCat.{v} R) (x : X.Point A) :
    X.OverlapCompatible (X.localizedCoordinates A x) := by
  intro a b
  have ha := X.component_from_localTest x
    ⟨X.overlapAlgebra A a b, X.overlapMap A a b, a, X.overlapUnitLeft A a b⟩
  have hb := X.component_from_localTest x
    ⟨X.overlapAlgebra A a b, X.overlapMap A a b, b, X.overlapUnitRight A a b⟩
  change pointMap (X.chart a) (X.overlapFromLeft A a b) (X.localUnit A a)
    (X.overlapUnitLeft A a b) (x.val (X.localTest A a)) =
      x.val ⟨X.overlapAlgebra A a b, X.overlapMap A a b, a, X.overlapUnitLeft A a b⟩ at ha
  change pointMap (X.chart b) (X.overlapFromRight A a b) (X.localUnit A b)
    (X.overlapUnitRight A a b) (x.val (X.localTest A b)) =
      x.val ⟨X.overlapAlgebra A a b, X.overlapMap A a b, b, X.overlapUnitRight A a b⟩ at hb
  change X.transitionPoints (X.overlapAlgebra A a b) a b
    (X.overlapUnitLeft A a b) (X.overlapUnitRight A a b)
    (pointMap (X.chart a) (X.overlapFromLeft A a b) (X.localUnit A a)
      (X.overlapUnitLeft A a b) (x.val (X.localTest A a))) =
    pointMap (X.chart b) (X.overlapFromRight A a b) (X.localUnit A b)
      (X.overlapUnitRight A a b) (x.val (X.localTest A b))
  rw [ha, hb]
  exact x.property.2 _ (X.overlapMap A a b) a b _ _

/-- The universal localized coordinate map with its actual overlap equations. -/
def toOverlapPoints (A : CommAlgCat.{v} R) : X.Point A →ₗ[O] X.OverlapPoint A where
  toFun x := ⟨X.localizedCoordinates A x, X.localizedCoordinates_compatible A x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reconstruct every chart-test component by its universal localization lift. -/
def familyOfOverlap {A : CommAlgCat.{v} R} (z : X.OverlapPoint A) : X.Family A :=
  fun t => pointMap (X.chart t.chart) (X.testFactor t) (X.localUnit A t.chart) t.isUnit
    (z.val t.chart)

/-- Universal overlap equations imply all coefficient and chart compatibilities. -/
theorem familyOfOverlap_compatible {A : CommAlgCat.{v} R} (z : X.OverlapPoint A) :
    X.Compatible (X.familyOfOverlap z) := by
  constructor
  · intro B C φ ψ a hb hc
    change pointMap (X.chart a) ψ hb hc
      (pointMap (X.chart a) (X.testFactor ⟨B, φ, a, hb⟩) (X.localUnit A a) hb
        (z.val a)) =
      pointMap (X.chart a) (X.testFactor ⟨C, φ ≫ ψ, a, hc⟩)
        (X.localUnit A a) hc (z.val a)
    rw [← pointMap_comp, X.testFactor_comp ⟨B, φ, a, hb⟩ ψ hc]
  · intro B φ a b ha hb
    have h := congrArg
      (fun q : X.ChartPoint (X.overlapAlgebra A a b) b (X.overlapUnitRight A a b) =>
        pointMap (X.chart b) (X.overlapFactor φ a b ha hb)
          (X.overlapUnitRight A a b) hb q) (z.property a b)
    rw [X.transitionPoints_natural (X.overlapFactor φ a b ha hb) a b
      (X.overlapUnitLeft A a b) (X.overlapUnitRight A a b) ha hb,
      ← pointMap_comp, ← pointMap_comp,
      X.overlapFromLeft_factor, X.overlapFromRight_factor] at h
    exact h

/-- The constructed inverse is linear on the actual chart tuples. -/
def fromOverlapPoints (A : CommAlgCat.{v} R) : X.OverlapPoint A →ₗ[O] X.Point A where
  toFun z := ⟨X.familyOfOverlap z, X.familyOfOverlap_compatible z⟩
  map_add' z w := by
    apply Subtype.ext
    funext t
    change pointMap (X.chart t.chart) (X.testFactor t) (X.localUnit A t.chart) t.isUnit
      (z.val t.chart + w.val t.chart) = _
    exact map_add _ _ _
  map_smul' c z := by
    apply Subtype.ext
    funext t
    change pointMap (X.chart t.chart) (X.testFactor t) (X.localUnit A t.chart) t.isUnit
      (c • z.val t.chart) = _
    exact map_smul _ _ _

/-- The universal factor of the canonical localization is its identity map. -/
@[simp]
theorem testFactor_localTest (A : CommAlgCat.{v} R) (a : X.opens) :
    X.testFactor (X.localTest A a) = 𝟙 (X.localAlgebra A a) := by
  apply X.localMap_ext a
  have h : X.localizationMap A a ≫ X.testFactor (X.localTest A a) =
      X.localizationMap A a := X.localizationMap_testFactor (X.localTest A a)
  exact h.trans (Category.comp_id _).symm

/-- Reconstructing a full family from its localized components recovers it. -/
@[simp]
theorem fromOverlapPoints_toOverlapPoints (A : CommAlgCat.{v} R) (x : X.Point A) :
    X.fromOverlapPoints A (X.toOverlapPoints A x) = x := by
  apply Subtype.ext
  funext t
  exact X.component_from_localTest x t

/-- Reconstructed families have exactly the prescribed localized components. -/
@[simp]
theorem toOverlapPoints_fromOverlapPoints (A : CommAlgCat.{v} R) (z : X.OverlapPoint A) :
    X.toOverlapPoints A (X.fromOverlapPoints A z) = z := by
  apply Subtype.ext
  funext a
  change pointMap (X.chart a) (X.testFactor (X.localTest A a))
    (X.localUnit A a) (X.localUnit A a) (z.val a) = z.val a
  rw [X.testFactor_localTest]
  exact pointMap_id (X.chart a) (X.localAlgebra A a) (X.localUnit A a) (z.val a)

/-- Actual atlas points are precisely localized tuples matching on all overlaps. -/
def overlapPointEquiv (A : CommAlgCat.{v} R) : X.Point A ≃ₗ[O] X.OverlapPoint A where
  __ := X.toOverlapPoints A
  invFun := X.fromOverlapPoints A
  left_inv := X.fromOverlapPoints_toOverlapPoints A
  right_inv := X.toOverlapPoints_fromOverlapPoints A

@[simp]
theorem overlapPointEquiv_apply (A : CommAlgCat.{v} R) (x : X.Point A) (a : X.opens) :
    (X.overlapPointEquiv A x).val a = x.val (X.localTest A a) := rfl

@[simp]
theorem overlapPointEquiv_symm_apply (A : CommAlgCat.{v} R) (z : X.OverlapPoint A)
    (t : X.ChartTest A) :
    ((X.overlapPointEquiv A).symm z).val t =
      pointMap (X.chart t.chart) (X.testFactor t) (X.localUnit A t.chart) t.isUnit
        (z.val t.chart) := rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

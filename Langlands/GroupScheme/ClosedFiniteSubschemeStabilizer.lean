import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardFreeCharts
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.Rational.TorusNormalizer
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Closed conjugation stabilizers of finite locally free subschemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S} {Z : Over S}

/-- Image of a morphism of relative schemes on the literal points of a test. -/
def schemePointRange (z : Z ⟶ G.X) (U : Over S) : Set (U ⟶ G.X) :=
  Set.range (fun y : U ⟶ Z => y ≫ z)

/-- The subgroup functor preserving the represented subscheme by conjugation
and inverse conjugation on every refinement of a test scheme. -/
def conjugationStabilizer (z : Z ⟶ G.X) : SubgroupFunctor G where
  carrier U :=
    { carrier := {g | ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X), x ∈ schemePointRange z V →
        (a ≫ g) * x * (a ≫ g)⁻¹ ∈ schemePointRange z V ∧
        (a ≫ g)⁻¹ * x * (a ≫ g) ∈ schemePointRange z V}
      one_mem' := by
        intro V a x hx
        rw [MonObj.comp_one, inv_one, one_mul, mul_one]
        exact ⟨hx, hx⟩
      mul_mem' := by
        intro g h hg hh V a x hx
        rw [MonObj.comp_mul, mul_inv_rev]
        constructor
        · simpa only [mul_assoc] using (hg V a _ (hh V a x hx).1).1
        · simpa only [mul_assoc] using (hh V a _ (hg V a x hx).2).2
      inv_mem' := by
        intro g hg V a x hx
        rw [GrpObj.comp_inv, inv_inv]
        exact ⟨(hg V a x hx).2, (hg V a x hx).1⟩ }
  comp_mem a g hg V b x hx := by
    rw [← Category.assoc]
    exact hg V (b ≫ a) x hx

/-- For a subgroup homomorphism, the subscheme stabilizer is the group normalizer. -/
theorem conjugationStabilizer_hom {H : GroupScheme S} (f : H ⟶ G) :
    conjugationStabilizer f.hom.hom = (SubgroupFunctor.range f).normalizer := by
  apply SubgroupFunctor.ext
  intro T
  ext g
  rfl

private def universalConjugate (z : Z ⟶ G.X) : Z ⊗ G.X ⟶ G.X :=
  (snd Z G.X) * (fst Z G.X ≫ z) * (snd Z G.X)⁻¹

private theorem conjugate_universal (z : Z ⟶ G.X) {U : Over S}
    (x : U ⟶ Z) (g : U ⟶ G.X) :
    lift x g ≫ universalConjugate z = g * (x ≫ z) * g⁻¹ := by
  simp only [universalConjugate, MonObj.comp_mul, GrpObj.comp_inv,
    CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_fst_assoc]

private theorem forward_iff_universal (z : Z ⟶ G.X) {U : Over S} (g : U ⟶ G.X) :
    (∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ Z),
      (a ≫ g) * (x ≫ z) * (a ≫ g)⁻¹ ∈ schemePointRange z V) ↔
    (Z ◁ g) ≫ universalConjugate z ∈ schemePointRange z (Z ⊗ U) := by
  have hk (V : Over S) (a : V ⟶ U) (x : V ⟶ Z) :
      lift x a ≫ (Z ◁ g) ≫ universalConjugate z =
        (a ≫ g) * (x ≫ z) * (a ≫ g)⁻¹ := by
    rw [← Category.assoc]
    have hl : lift x a ≫ (Z ◁ g) = lift x (a ≫ g) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hl, conjugate_universal]
  constructor
  · intro h
    have h' := h _ (snd Z U) (fst Z U)
    rw [← hk, CartesianMonoidalCategory.lift_fst_snd, Category.id_comp] at h'
    exact h'
  · rintro ⟨y, hy⟩ V a x
    exact ⟨lift x a ≫ y, (Category.assoc _ _ _).trans ((congrArg (lift x a ≫ ·) hy).trans (hk V a x))⟩

private theorem factors_pullback_snd_iff {C : Type*} [Category C] {Z Y X T : C}
    (z : Z ⟶ Y) (f : X ⟶ Y) [HasPullback z f] (g : T ⟶ X) :
    (∃ y : T ⟶ pullback z f, y ≫ pullback.snd z f = g) ↔
      ∃ y : T ⟶ Z, y ≫ z = g ≫ f := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ pullback.fst z f, by rw [Category.assoc, pullback.condition, ← Category.assoc, hy]⟩
  · rintro ⟨y, hy⟩
    exact ⟨pullback.lift y g hy, pullback.lift_snd _ _ _⟩

set_option maxHeartbeats 800000 in
private theorem exists_forward_locus {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {Z : Over (Spec R)} [IsAffineHom Z.hom] [Flat Z.hom]
    (hZ : Langlands.AlgebraicGeometry.HasFpqcProjectiveCoordinateModule Z)
    (z : Z ⟶ G.X) [IsClosedImmersion z.left] :
    ∃ (P : Over (Spec R)) (i : P ⟶ G.X), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec R)) (g : T ⟶ G.X), (∃ y : T ⟶ P, y ≫ i = g) ↔
        ∀ (V : Over (Spec R)) (a : V ⟶ T) (x : V ⟶ Z),
          (a ≫ g) * (x ≫ z) * (a ≫ g)⁻¹ ∈ schemePointRange z V := by
  let f := universalConjugate z
  let d := pullback.snd z f
  have hd : IsClosedImmersion d.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback z f).map (Over.forget _))
    (show IsClosedImmersion z.left from inferInstance)
  obtain ⟨P, i, hi, h⟩ := Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus
    R Z inferInstance inferInstance hZ G.X _ d hd
  refine ⟨P, i, hi, fun T g => (h T g).trans ?_⟩
  exact (factors_pullback_snd_iff z f (Z ◁ g)).trans (forward_iff_universal z g).symm

set_option maxHeartbeats 850000 in
private theorem exists_stabilizer_of_coordinates {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {Z : Over (Spec R)} [IsAffineHom Z.hom] [Flat Z.hom]
    (hZ : Langlands.AlgebraicGeometry.HasFpqcProjectiveCoordinateModule Z)
    (z : Z ⟶ G.X) [IsClosedImmersion z.left] :
    (conjugationStabilizer z).IsClosedRepresentable := by
  obtain ⟨P, i, hi, h⟩ := exists_forward_locus hZ z
  let ν : G.X ⟶ G.X := ι[G.X]
  let j := pullback.snd i ν
  let l := pullback.snd i j
  have : IsClosedImmersion i.left := hi
  have : IsClosedImmersion j.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback i ν).map (Over.forget _)) hi
  have : IsClosedImmersion l.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback i j).map (Over.forget _)) hi
  let c := l ≫ j
  have : IsClosedImmersion c.left := inferInstanceAs (IsClosedImmersion (l.left ≫ j.left))
  have : Mono c := Over.mono_of_mono_left _
  apply (conjugationStabilizer z).isClosedRepresentable_of_scheme c
  intro T g
  have hp : (∃ y, y ≫ c = g) ↔ (∃ y, y ≫ i = g) ∧ (∃ y, y ≫ i = g ≫ ν) := by
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨⟨y ≫ pullback.fst i j, ?_⟩, ?_⟩
      · rw [Category.assoc, pullback.condition]
      · exact (factors_pullback_snd_iff i ν (y ≫ c)).mp ⟨y ≫ l, Category.assoc _ _ _⟩
    · rintro ⟨⟨x, hx⟩, hy⟩
      obtain ⟨y, hy⟩ := (factors_pullback_snd_iff i ν g).mpr hy
      refine ⟨pullback.lift x y (hx.trans hy.symm), ?_⟩
      change pullback.lift x y (hx.trans hy.symm) ≫ l ≫ j = g
      rw [← Category.assoc, pullback.lift_snd, hy]
  rw [hp, h T g, h T (g ≫ ν)]
  constructor
  · intro hg
    refine ⟨fun V a x => (hg V a _ ⟨x, rfl⟩).1, fun V a x => ?_⟩
    change (a ≫ g⁻¹) * (x ≫ z) * (a ≫ g⁻¹)⁻¹ ∈ schemePointRange z V
    rw [GrpObj.comp_inv, inv_inv]
    exact (hg V a _ ⟨x, rfl⟩).2
  · rintro ⟨h₁, h₂⟩ V a x ⟨y, rfl⟩
    refine ⟨h₁ V a y, ?_⟩
    have hh := h₂ V a y
    change (a ≫ g⁻¹) * (y ≫ z) * (a ≫ g⁻¹)⁻¹ ∈ schemePointRange z V at hh
    simpa only [GrpObj.comp_inv, inv_inv] using hh

/-- Every finite flat finitely presented closed subscheme of a group over an
arbitrary affine base has a closed conjugation stabilizer. -/
def ClosedFiniteSubschemeStabilizerStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R)) (Z : Over (Spec R))
    [IsFinite Z.hom] [Flat Z.hom] [LocallyOfFinitePresentation Z.hom],
    ∀ z : Z ⟶ G.X, IsClosedImmersion z.left → (conjugationStabilizer z).IsClosedRepresentable

set_option maxHeartbeats 1000000 in
theorem closedFiniteSubschemeStabilizer : ClosedFiniteSubschemeStabilizerStatement.{u} := by
  intro R G Z _ _ _ z hz
  have : IsClosedImmersion z.left := hz
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : R ⟶ Γ(Z.left, ⊤) := (Scheme.ΓSpecIso R).inv ≫ Z.hom.appTop
  have hspec : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := by
    rw [← Langlands.AlgebraicGeometry.Modules.DerivedSections.isoSpec_hom_comp_specMap_structureRingHom
      Z.hom, Iso.inv_hom_id_assoc]
    rfl
  have : IsFinite (Spec.map φ) := by rw [hspec]; infer_instance
  have : Flat (Spec.map φ) := by rw [hspec]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hspec]; infer_instance
  let D := ((algΓ R).obj Z).unop
  have : Module.Finite R D := (IsFinite.SpecMap_iff φ).mp inferInstance
  have : Module.Flat R D := Flat.SpecMap_iff.mp (inferInstanceAs (Flat (Spec.map φ)))
  have : Algebra.FinitePresentation R D := (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  have : Module.FinitePresentation R D := Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have : Module.Projective R D := Module.Flat.projective_of_finitePresentation
  exact exists_stabilizer_of_coordinates ⟨CommAlgCat.of R R, inferInstance, inferInstance⟩ z

end Langlands.GroupScheme

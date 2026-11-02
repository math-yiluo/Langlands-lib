import Langlands.AbelianScheme.GroupScheme
import Langlands.CategoryTheory.GroupObjectDescent
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Actual images of finite étale group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteEtaleImage

variable {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
  [IsFinite G.X.hom] [Etale G.X.hom] [IsFinite H.X.hom] [Etale H.X.hom]

/-- A morphism between finite étale group schemes is finite étale. -/
theorem finiteEtale_hom : Langlands.AlgebraicGeometry.FiniteEtale.finiteEtale f.hom.hom.left :=
  Langlands.AlgebraicGeometry.FiniteEtale.finiteEtale.of_postcomp
    (W' := Langlands.AlgebraicGeometry.FiniteEtale.finiteEtale)
    f.hom.hom.left H.X.hom ⟨inferInstance, inferInstance⟩ (by
      rw [Over.w]
      exact ⟨inferInstance, inferInstance⟩)

/-- The actual topological image is open and closed. -/
theorem isClopen_range : IsClopen (Set.range f.hom.hom.left) := by
  have := (finiteEtale_hom f).1
  have := (finiteEtale_hom f).2
  exact ⟨f.hom.hom.left.isClosedMap.isClosed_range,
    f.hom.hom.left.isOpenMap.isOpen_range⟩

/-- The open subscheme with the actual image as its underlying open subset. -/
def imageOpen : H.X.left.Opens := ⟨Set.range f.hom.hom.left, (isClopen_range f).isOpen⟩

instance : IsClosedImmersion (imageOpen f).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (isClopen_range f).isClosed)

/-- The actual image scheme over the original base. -/
abbrev imageOver : Over S := Over.mk ((imageOpen f).ι ≫ H.X.hom)

/-- Its inclusion into the target. -/
abbrev inclusionOver : imageOver f ⟶ H.X := Over.homMk (imageOpen f).ι

instance : IsOpenImmersion (inclusionOver f).left :=
  inferInstanceAs (IsOpenImmersion (imageOpen f).ι)

instance : IsClosedImmersion (inclusionOver f).left :=
  inferInstanceAs (IsClosedImmersion (imageOpen f).ι)

instance : Mono (inclusionOver f) := Over.mono_of_mono_left _

instance : IsFinite (imageOver f).hom := inferInstanceAs
  (IsFinite ((imageOpen f).ι ≫ H.X.hom))

instance : Etale (imageOver f).hom := inferInstanceAs
  (Etale ((imageOpen f).ι ≫ H.X.hom))

/-- Factor a map over the base through a supplied open immersion. -/
def liftOver {P Q R : Over S} (j : P ⟶ Q) [IsOpenImmersion j.left]
    (g : R ⟶ Q) (h : Set.range g.left ⊆ Set.range j.left) : R ⟶ P :=
  Over.homMk (IsOpenImmersion.lift j.left g.left h) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

@[reassoc (attr := simp)]
theorem liftOver_fac {P Q R : Over S} (j : P ⟶ Q) [IsOpenImmersion j.left]
    (g : R ⟶ Q) (h : Set.range g.left ⊆ Set.range j.left) :
    liftOver j g h ≫ j = g :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- The original map with codomain restricted to its actual open image. -/
def projectionOver : G.X ⟶ imageOver f :=
  liftOver (inclusionOver f) f.hom.hom (by
    change Set.range f.hom.hom.left ⊆ Set.range (imageOpen f).ι
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl)

@[reassoc (attr := simp)]
theorem projectionOver_fac : projectionOver f ≫ inclusionOver f = f.hom.hom :=
  liftOver_fac _ _ _

/-- The projection to the image is finite étale over the same base. -/
theorem finiteEtale_projectionOver :
    Langlands.AlgebraicGeometry.FiniteEtale.finiteEtale (projectionOver f).left :=
  Langlands.AlgebraicGeometry.FiniteEtale.finiteEtale.of_postcomp
    (W' := Langlands.AlgebraicGeometry.FiniteEtale.finiteEtale)
    (projectionOver f).left (imageOver f).hom ⟨inferInstance, inferInstance⟩ (by
      rw [Over.w]
      exact ⟨inferInstance, inferInstance⟩)

instance : IsFinite (projectionOver f).left := (finiteEtale_projectionOver f).1

instance : Etale (projectionOver f).left := (finiteEtale_projectionOver f).2

instance : Surjective (projectionOver f).left := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun g : G.X ⟶ H.X => g.left x) (projectionOver_fac f)).trans hx

/-- Surjective precomposition detects whether a map lands in an open subscheme. -/
theorem range_subset_of_surjective_factor {P Q R W : Over S}
    (j : P ⟶ Q) (g : R ⟶ Q) (p : W ⟶ R) [Surjective p.left]
    (a : W ⟶ P) (ha : a ≫ j = p ≫ g) : Set.range g.left ⊆ Set.range j.left := by
  rintro _ ⟨r, rfl⟩
  obtain ⟨w, hw⟩ := p.left.surjective r
  refine ⟨a.left w, ?_⟩
  have h := congrArg (fun k : W ⟶ Q => k.left w) ha
  simpa only [Over.comp_left, Scheme.Hom.comp_apply, hw] using h

instance : Surjective (projectionOver f ⊗ₘ projectionOver f).left := by
  let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun _ _ hf hg => ⟨hg.surj.comp hf.surj⟩⟩
  exact MorphismProperty.pullbackMap (P := @Surjective.{u})
    inferInstance inferInstance (Over.w (projectionOver f)).symm
      (Over.w (projectionOver f)).symm

/-- The ambient unit already factors through the image. -/
def imageOne : 𝟙_ (Over S) ⟶ imageOver f := η[G.X] ≫ projectionOver f

@[reassoc (attr := simp)]
theorem imageOne_fac : imageOne f ≫ inclusionOver f = η[H.X] := by
  rw [imageOne, Category.assoc, projectionOver_fac, IsMonHom.one_hom]

/-- Multiplication of image points lands in the same actual open subscheme. -/
theorem mul_range_subset :
    Set.range (((inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X]).left) ⊆
      Set.range (inclusionOver f).left := by
  apply range_subset_of_surjective_factor (inclusionOver f) _
    (projectionOver f ⊗ₘ projectionOver f) (μ[G.X] ≫ projectionOver f)
  rw [Category.assoc, projectionOver_fac, IsMonHom.mul_hom f.hom.hom,
    tensorHom_comp_tensorHom_assoc, projectionOver_fac]

/-- The actual restricted multiplication morphism. -/
def imageMul : imageOver f ⊗ imageOver f ⟶ imageOver f :=
  liftOver (inclusionOver f) ((inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X])
    (mul_range_subset f)

@[reassoc (attr := simp)]
theorem imageMul_fac : imageMul f ≫ inclusionOver f =
    (inclusionOver f ⊗ₘ inclusionOver f) ≫ μ[H.X] := liftOver_fac _ _ _

/-- Inversion of image points lands in the same actual open subscheme. -/
theorem inv_range_subset :
    Set.range ((inclusionOver f ≫ ι[H.X]).left) ⊆ Set.range (inclusionOver f).left := by
  apply range_subset_of_surjective_factor (inclusionOver f) _ (projectionOver f)
    (ι[G.X] ≫ projectionOver f)
  rw [Category.assoc, projectionOver_fac, ← Category.assoc, projectionOver_fac]
  exact GrpObj.inv_hom f.hom.hom

/-- The actual restricted inverse morphism. -/
def imageInv : imageOver f ⟶ imageOver f :=
  liftOver (inclusionOver f) (inclusionOver f ≫ ι[H.X]) (inv_range_subset f)

@[reassoc (attr := simp)]
theorem imageInv_fac : imageInv f ≫ inclusionOver f = inclusionOver f ≫ ι[H.X] :=
  liftOver_fac _ _ _

instance imageGrpObj : GrpObj (imageOver f) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver f) (imageOne f) (imageMul f) (imageInv f)
      (imageOne_fac f) (imageMul_fac f) (imageInv_fac f)

instance : IsMonHom (inclusionOver f) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver f) (imageOne f) (imageMul f) (imageInv f)
      (imageOne_fac f) (imageMul_fac f) (imageInv_fac f)

instance : IsMonHom (projectionOver f) where
  one_hom := by
    apply (cancel_mono (inclusionOver f)).mp
    rw [Category.assoc, projectionOver_fac, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (inclusionOver f)).mp
    rw [Category.assoc, projectionOver_fac, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      projectionOver_fac]

/-- The actual image group scheme. -/
abbrev image : GroupScheme S := { X := imageOver f }

instance [IsCommMonObj H.X] : IsCommMonObj (image f).X :=
  Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono (inclusionOver f)

/-- The closed immersion from the actual image group scheme. -/
def inclusion : image f ⟶ H := Grp.homMk (inclusionOver f)

/-- The actual surjective homomorphism onto the image. -/
def projection : G ⟶ image f := Grp.homMk (projectionOver f)

@[reassoc (attr := simp)]
theorem projection_inclusion : projection f ≫ inclusion f = f :=
  Grp.hom_ext _ _ (projectionOver_fac f)

instance : IsClosedImmersion (inclusion f).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver f).left)

instance : IsOpenImmersion (inclusion f).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (inclusionOver f).left)

instance : IsFinite (projection f).hom.hom.left :=
  inferInstanceAs (IsFinite (projectionOver f).left)

instance : Etale (projection f).hom.hom.left :=
  inferInstanceAs (Etale (projectionOver f).left)

instance : Surjective (projection f).hom.hom.left :=
  inferInstanceAs (Surjective (projectionOver f).left)

instance : EffectiveEpi (projection f).hom.hom.left := inferInstance

instance : Epi (projection f).hom.hom := Over.epi_of_epi_left _

instance : Epi (projection f) :=
  (Grp.forget (Over S)).epi_of_epi_map
    (inferInstanceAs (Epi (projection f).hom.hom))

/-- Equality on the actual image is detected by the original source. -/
theorem hom_ext {J : GroupScheme S} (a b : image f ⟶ J)
    (h : projection f ≫ a = projection f ≫ b) : a = b :=
  (cancel_epi (projection f)).mp h

/-- A homomorphism kills the actual image exactly when it kills the original map. -/
theorem inclusion_comp_eq_one_iff {J : GroupScheme S} [IsCommMonObj J.X] (g : H ⟶ J) :
    inclusion f ≫ g = 1 ↔ f ≫ g = 1 := by
  constructor
  · intro h
    rw [← projection_inclusion f, Category.assoc, h, MonObj.comp_one]
  · intro h
    apply hom_ext f
    rw [← Category.assoc, projection_inclusion, h, MonObj.comp_one]

end Langlands.GroupScheme.FiniteEtaleImage

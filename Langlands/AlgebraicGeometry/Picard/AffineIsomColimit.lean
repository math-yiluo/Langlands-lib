import Langlands.AlgebraicGeometry.Picard.AffineIsomSubalgebraDescent
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentability
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Filtered colimits of actual Picard isomorphisms over subalgebras -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The directed category of finitely generated subalgebras of an algebra. -/
def AffineAlgebraStage := {B : Subalgebra R A // B.FG}
  deriving PartialOrder

instance : IsFiltered (AffineAlgebraStage R A) where
  nonempty := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  cocone_objs B C := ⟨⟨B.val ⊔ C.val, B.property.sup C.property⟩,
    homOfLE (show B.val ≤ B.val ⊔ C.val from le_sup_left),
    homOfLE (show C.val ≤ B.val ⊔ C.val from le_sup_right), trivial⟩
  cocone_maps _ C _ _ := ⟨C, 𝟙 C, Subsingleton.elim _ _⟩

variable {R A}

/-- The scheme arrow induced by an inclusion of subalgebras. -/
def affineAlgebraStageMap {B C : Subalgebra R A} (h : B ≤ C) :
    affineBase R C ⟶ affineBase R B :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    dsimp only [affineBase, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)

@[simp]
lemma affineAlgebraStageMap_id (B : Subalgebra R A) :
    affineAlgebraStageMap (le_refl B) = 𝟙 (affineBase R B) := by
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [Spec.map_eq_id]
  rfl

@[simp, reassoc]
lemma affineAlgebraStageMap_comp {B C D : Subalgebra R A}
    (hBC : B ≤ C) (hCD : C ≤ D) :
    affineAlgebraStageMap hCD ≫ affineAlgebraStageMap hBC =
      affineAlgebraStageMap (hBC.trans hCD) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

@[simp, reassoc]
lemma affineAlgebraStageMap_restrict {B C : Subalgebra R A} (h : B ≤ C) :
    affineSubalgebraMap C ≫ affineAlgebraStageMap h = affineSubalgebraMap B := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable (R A)

/-- The inverse system of affine schemes for the finite subalgebras. -/
def affineAlgebraStageScheme : (AffineAlgebraStage R A)ᵒᵖ ⥤
    Over (Spec (CommRingCat.of R)) where
  obj B := affineBase R B.unop.val
  map h := affineAlgebraStageMap (leOfHom h.unop)
  map_id B := affineAlgebraStageMap_id B.unop.val
  map_comp h g := (affineAlgebraStageMap_comp (leOfHom g.unop) (leOfHom h.unop)).symm

variable (F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of R)))

/-- Sections on finite subalgebra stages, with their actual restriction maps. -/
def affineAlgebraStageSections : AffineAlgebraStage R A ⥤ Type (u + 1) :=
  (affineAlgebraStageScheme R A).rightOp ⋙ F

/-- The canonical restriction cocone with value on the whole algebra. -/
def affineAlgebraStageSectionsCocone : Cocone (affineAlgebraStageSections R A F) where
  pt := F.obj (op (affineBase R A))
  ι :=
    { app B := F.map (affineSubalgebraMap B.val).op
      naturality B C h := by
        change F.map (affineAlgebraStageMap (leOfHom h)).op ≫
          F.map (affineSubalgebraMap C.val).op = _
        rw [← F.map_comp, ← op_comp, affineAlgebraStageMap_restrict]
        simp }

variable {R A F}

/-- Maps to an affine scheme are detected after an injective algebra extension. -/
lemma affinePoint_subalgebra_restrict_injective
    (I : Over (Spec (CommRingCat.of R))) [IsAffine I.left] (B : Subalgebra R A) :
    Function.Injective
      (fun p : affineBase R B ⟶ I ↦ affineSubalgebraMap B ≫ p) := by
  intro p q hpq
  apply Over.OverMorphism.ext
  apply (cancel_mono I.left.isoSpec.hom).mp
  apply Spec.preimage_injective
  let j : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap B A)
  have : Mono j := ConcreteCategory.mono_of_injective j Subtype.val_injective
  apply (cancel_mono j).mp
  have h : Spec.map j ≫ (p.left ≫ I.left.isoSpec.hom) =
      Spec.map j ≫ (q.left ≫ I.left.isoSpec.hom) := by
    simpa only [Over.comp_left, Category.assoc, affineSubalgebraMap,
      Over.homMk_left, j] using
      congrArg (fun z ↦ z.left ≫ I.left.isoSpec.hom) hpq
  simpa only [Spec.preimage_comp, Spec.preimage_map] using congrArg Spec.preimage h

/-- Affine representation detects a section at any subalgebra stage. -/
theorem affineSubalgebraRestriction_injective_of_representable
    (hF : AlgebraicSpace.IsAffineFinitePresentationRepresentable F)
    (B : Subalgebra R A) :
    Function.Injective (F.map (affineSubalgebraMap B).op) := by
  obtain ⟨I, ⟨e⟩, hI, _⟩ := hF
  have : IsAffineHom I.hom := hI
  have : IsAffine I.left := isAffine_of_isAffineHom I.hom
  intro x y hxy
  let p : affineBase R B ⟶ I := (e.inv.app _ x).down
  let q : affineBase R B ⟶ I := (e.inv.app _ y).down
  have hx : (e.inv.app _ (F.map (affineSubalgebraMap B).op x)).down =
      affineSubalgebraMap B ≫ p :=
    congrArg ULift.down (types_congr_hom (e.inv.naturality
      (affineSubalgebraMap B).op) x)
  have hy : (e.inv.app _ (F.map (affineSubalgebraMap B).op y)).down =
      affineSubalgebraMap B ≫ q :=
    congrArg ULift.down (types_congr_hom (e.inv.naturality
      (affineSubalgebraMap B).op) y)
  have hpq : p = q := affinePoint_subalgebra_restrict_injective I B
    (hx.symm.trans ((congrArg (fun z ↦ (e.inv.app _ z).down) hxy).trans hy))
  apply (e.app (op (affineBase R B))).toEquiv.symm.injective
  apply ULift.ext
  exact hpq

/-- The finite-stage sections of an affine finitely presented presheaf form a
colimit with their actual restriction cocone. -/
def affineAlgebraStageSectionsIsColimit_of_representable
    (hF : AlgebraicSpace.IsAffineFinitePresentationRepresentable F) :
    IsColimit (affineAlgebraStageSectionsCocone R A F) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ by
      obtain ⟨B, hB, _, y, hy⟩ :=
        hasAffineSubalgebraSectionDescent_of_representable hF A x ∅
      exact ⟨⟨B, hB⟩, y, hy.symm⟩)
    (fun B x y hxy ↦ by
      have h : x = y := affineSubalgebraRestriction_injective_of_representable hF B.val hxy
      exact ⟨B, 𝟙 B, congrArg _ h⟩)

namespace PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable (t : Spec (CommRingCat.of R) ⟶ S)
variable (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t)))

/-- Under precisely properness, flatness and local finite presentation, the
specified relative Isom sections on an arbitrary algebra are the filtered
colimit of their sections on finitely generated subalgebras. -/
def affineIsomSectionsIsColimit
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    IsColimit (affineAlgebraStageSectionsCocone R A (relativeIsomPresheaf f L M)) :=
  affineAlgebraStageSectionsIsColimit_of_representable
    (properLineBundleIsomRepresentability_of_hom properLineBundleHomRepresentability
      S X f hf hflat hfp (Over.mk t) L M)

variable (R A)

/-- The canonical finite-subalgebra restriction cocone for the actual relative
Isom presheaf has its categorical colimit universal property. -/
def HasAffineIsomSectionsColimit : Prop :=
  Nonempty (IsColimit
    (affineAlgebraStageSectionsCocone R A (relativeIsomPresheaf f L M)))

/-- Properness, flatness and local finite presentation imply the actual
finite-subalgebra Isom-section colimit property. -/
theorem hasAffineIsomSectionsColimit
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    HasAffineIsomSectionsColimit R A f t L M :=
  ⟨affineIsomSectionsIsColimit (A := A) f t L M hf hflat hfp⟩

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard

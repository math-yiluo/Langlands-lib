import Langlands.AlgebraicGeometry.Picard.AffineStageEnlargement

/-! # Sections on finite stages containing a chosen base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The actual `B`-slice test associated to an `R`-subalgebra containing `B`. -/
def affineAlgebraStageAboveTest {B : Subalgebra R A} (C : AffineAlgebraStageAbove B) :
    Over (affineBase R B) :=
  Over.mk (affineAlgebraStageMap C.property)

/-- The canonical map from the whole algebra to a finite enlargement of `B`. -/
def affineAlgebraStageAboveRestriction {B : Subalgebra R A}
    (C : AffineAlgebraStageAbove B) :
    Over.mk (affineSubalgebraMap B) ⟶ affineAlgebraStageAboveTest C :=
  Over.homMk (affineSubalgebraMap C.val.val)
    (affineAlgebraStageMap_restrict C.property)

/-- The actual affine inverse system in the slice above the chosen base. -/
def affineAlgebraStageAboveScheme (B : Subalgebra R A) :
    (AffineAlgebraStageAbove B)ᵒᵖ ⥤ Over (affineBase R B) where
  obj C := affineAlgebraStageAboveTest C.unop
  map h := Over.homMk (affineAlgebraStageMap (leOfHom h.unop))
    (affineAlgebraStageMap_comp _ _)
  map_id C := by
    apply Over.OverMorphism.ext
    exact affineAlgebraStageMap_id C.unop.val.val
  map_comp h g := by
    apply Over.OverMorphism.ext
    exact (affineAlgebraStageMap_comp _ _).symm

/-- The comparison of structure morphisms before taking the further slice. -/
def affineAlgebraStageAboveBaseIso {B : Subalgebra R A}
    (C : AffineAlgebraStageAbove B) :
    (Over.map (affineBase R B).hom).obj
      (affineBase B (subalgebraOver C.property)) ≅ affineBase R C.val.val := by
  refine Over.isoMk (Iso.refl (Spec (CommRingCat.of C.val.val))) ?_
  change (𝟙 (Spec (CommRingCat.of C.val.val))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C.val.val)) =
    Spec.map (CommRingCat.ofHom (algebraMap B (subalgebraOver C.property))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B))
  rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Comparison with the same affine test regarded directly as a `B`-algebra. -/
def affineAlgebraStageAboveTestIso {B : Subalgebra R A}
    (C : AffineAlgebraStageAbove B) :
    (affineBase R B).iteratedSliceBackward.obj
      (affineBase B (subalgebraOver C.property)) ≅ affineAlgebraStageAboveTest C := by
  refine Over.isoMk (affineAlgebraStageAboveBaseIso C) ?_
  apply Over.OverMorphism.ext
  change (𝟙 (Spec (CommRingCat.of C.val.val))) ≫
      (affineAlgebraStageMap C.property).left =
    Spec.map (CommRingCat.ofHom (algebraMap B (subalgebraOver C.property)))
  rw [Category.id_comp]
  rfl

/-- The same affine comparison at the whole algebra. -/
def affineAlgebraStageAboveWholeIso (B : Subalgebra R A) :
    (affineBase R B).iteratedSliceBackward.obj (affineBase B A) ≅
      Over.mk (affineSubalgebraMap B) := by
  refine Over.isoMk (affineBaseTowerIso B) ?_
  apply Over.OverMorphism.ext
  change (𝟙 (Spec (CommRingCat.of A))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B A)) =
    Spec.map (CommRingCat.ofHom (algebraMap B A))
  exact Category.id_comp _

/-- The affine test comparisons commute with restriction to the whole algebra. -/
lemma affineAlgebraStageAboveTestIso_restrict {B : Subalgebra R A}
    (C : AffineAlgebraStageAbove B) :
    (affineBase R B).iteratedSliceBackward.map
        (affineSubalgebraMap (subalgebraOver C.property)) ≫
      (affineAlgebraStageAboveTestIso C).hom =
    (affineAlgebraStageAboveWholeIso B).hom ≫ affineAlgebraStageAboveRestriction C := by
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap (subalgebraOver C.property) A)) ≫
      (𝟙 (Spec (CommRingCat.of C.val.val))) =
    (𝟙 (Spec (CommRingCat.of A))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C.val.val A))
  simp only [Category.id_comp]
  rfl

variable (B : Subalgebra R A)
variable (G : (Over (affineBase R B))ᵒᵖ ⥤ Type (u + 1))

/-- Sections on finite enlargements, using the canonical inclusion maps. -/
def affineAlgebraStageAboveSections : AffineAlgebraStageAbove B ⥤ Type (u + 1) :=
  (affineAlgebraStageAboveScheme B).rightOp ⋙ G

/-- The canonical restriction cocone, in the original `R`-slice. -/
def affineAlgebraStageAboveSectionsCocone :
    Cocone (affineAlgebraStageAboveSections B G) where
  pt := G.obj (op (Over.mk (affineSubalgebraMap B)))
  ι :=
    { app C := G.map (affineAlgebraStageAboveRestriction C).op
      naturality C D h := by
        change G.map (Over.homMk (affineAlgebraStageMap (leOfHom h))
            (affineAlgebraStageMap_comp C.property (leOfHom h))).op ≫
          G.map (affineAlgebraStageAboveRestriction D).op =
          G.map (affineAlgebraStageAboveRestriction C).op ≫ 𝟙 _
        rw [Category.comp_id, ← G.map_comp, ← op_comp]
        congr 1
        congr 1
        apply Over.OverMorphism.ext
        exact affineAlgebraStageMap_restrict (leOfHom h) }

/-- Regard a presheaf on the iterated slice as a presheaf on `Spec B`. -/
def affineAlgebraStageAbovePresheaf :
    AlgebraicSpace.Presheaf (Spec (CommRingCat.of B)) :=
  (affineBase R B).iteratedSliceBackward.op ⋙ G

/-- The test and whole-base section identifications preserve canonical restriction. -/
lemma affineAlgebraStageAboveSections_restrict
    (C : AffineAlgebraStageAbove B)
    (x : G.obj (op (affineAlgebraStageAboveTest C))) :
    G.map (affineAlgebraStageAboveWholeIso B).hom.op
        (G.map (affineAlgebraStageAboveRestriction C).op x) =
      (affineAlgebraStageAbovePresheaf B G).map
          (affineSubalgebraMap (subalgebraOver C.property)).op
        (G.map (affineAlgebraStageAboveTestIso C).hom.op x) := by
  change G.map (affineAlgebraStageAboveWholeIso B).hom.op
      (G.map (affineAlgebraStageAboveRestriction C).op x) =
    G.map ((affineBase R B).iteratedSliceBackward.map
        (affineSubalgebraMap (subalgebraOver C.property))).op
      (G.map (affineAlgebraStageAboveTestIso C).hom.op x)
  have h := congrArg (fun a ↦ G.map a.op)
    (affineAlgebraStageAboveTestIso_restrict C)
  simpa only [op_comp, G.map_comp, types_comp_apply] using
    (ConcreteCategory.congr_hom h x).symm

/-- Affine representation detects equality at each finite enlargement of `B`. -/
theorem affineAlgebraStageAboveRestriction_injective
    (hG : AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (affineAlgebraStageAbovePresheaf B G))
    (C : AffineAlgebraStageAbove B) :
    Function.Injective (G.map (affineAlgebraStageAboveRestriction C).op) := by
  intro x y hxy
  apply (G.mapIso (affineAlgebraStageAboveTestIso C).op).toEquiv.injective
  change G.map (affineAlgebraStageAboveTestIso C).hom.op x =
    G.map (affineAlgebraStageAboveTestIso C).hom.op y
  apply affineSubalgebraRestriction_injective_of_representable hG
    (subalgebraOver C.property)
  exact (affineAlgebraStageAboveSections_restrict B G C x).symm.trans
    ((congrArg (G.map (affineAlgebraStageAboveWholeIso B).hom.op) hxy).trans
      (affineAlgebraStageAboveSections_restrict B G C y))

/-- Each specified section descends to an actual finite `R`-stage containing `B`. -/
theorem exists_affineAlgebraStageAbove_section
    (hB : B.FG)
    (hG : AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (affineAlgebraStageAbovePresheaf B G))
    (x : G.obj (op (Over.mk (affineSubalgebraMap B)))) :
    ∃ (C : AffineAlgebraStageAbove B)
      (y : G.obj (op (affineAlgebraStageAboveTest C))),
      G.map (affineAlgebraStageAboveRestriction C).op y = x := by
  let x' := G.map (affineAlgebraStageAboveWholeIso B).hom.op x
  obtain ⟨D, hD, _, y, hy⟩ :=
    hasAffineSubalgebraSectionDescent_of_representable hG A x' ∅
  let C : AffineAlgebraStageAbove B :=
    affineAlgebraStageEnlargementOrderIso B hB ⟨D, hD⟩
  let y' : G.obj (op (affineAlgebraStageAboveTest C)) :=
    G.map (affineAlgebraStageAboveTestIso C).inv.op y
  have hyy : G.map (affineAlgebraStageAboveTestIso C).hom.op y' = y :=
    (G.mapIso (affineAlgebraStageAboveTestIso C).op).toEquiv.apply_symm_apply y
  have hy' : (affineAlgebraStageAbovePresheaf B G).map
        (affineSubalgebraMap (subalgebraOver C.property)).op y =
      G.map (affineAlgebraStageAboveWholeIso B).hom.op x := hy
  refine ⟨C, y', ?_⟩
  apply (G.mapIso (affineAlgebraStageAboveWholeIso B).op).toEquiv.injective
  change G.map (affineAlgebraStageAboveWholeIso B).hom.op
      (G.map (affineAlgebraStageAboveRestriction C).op y') =
    G.map (affineAlgebraStageAboveWholeIso B).hom.op x
  exact (affineAlgebraStageAboveSections_restrict B G C y').trans
    ((congrArg ((affineAlgebraStageAbovePresheaf B G).map
      (affineSubalgebraMap (subalgebraOver C.property)).op) hyy).trans hy')

/-- Canonical sections on the finite enlargements form a colimit in the original slice. -/
def affineAlgebraStageAboveSectionsIsColimit_of_representable
    (hB : B.FG)
    (hG : AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (affineAlgebraStageAbovePresheaf B G)) :
    IsColimit (affineAlgebraStageAboveSectionsCocone B G) := by
  have : IsFiltered (AffineAlgebraStageAbove B) :=
    IsFiltered.of_equivalence (affineAlgebraStageEnlargementOrderIso B hB).equivalence
  exact Types.FilteredColimit.isColimitOf'
    (affineAlgebraStageAboveSections B G) (affineAlgebraStageAboveSectionsCocone B G)
    (fun x ↦ by
      obtain ⟨C, y, hy⟩ := exists_affineAlgebraStageAbove_section B G hB hG x
      exact ⟨C, y, hy.symm⟩)
    (fun C x y hxy ↦ by
      have h : x = y := affineAlgebraStageAboveRestriction_injective B G hG C hxy
      exact ⟨C, 𝟙 C, congrArg _ h⟩)

namespace PicardGroupoid

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (L M : PicardGroupoid ((relativeSpace f).obj (affineBase R B)))

/-- The relative Isom presheaf on the iterated slice before identifying its base scheme. -/
def affineEnlargementIsomPresheaf :
    (Over (affineBase R B))ᵒᵖ ⥤ Type (u + 1) :=
  (relative f).presheafHom L M ⋙ uliftFunctor.{u + 1}

/-- The actual Isom sections form a colimit over the finite stages containing `B`. -/
def affineEnlargementIsomSectionsIsColimit (hB : B.FG)
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    IsColimit (affineAlgebraStageAboveSectionsCocone B
      (affineEnlargementIsomPresheaf B f L M)) :=
  affineAlgebraStageAboveSectionsIsColimit_of_representable B _ hB
    (properLineBundleIsomRepresentability_of_hom properLineBundleHomRepresentability
      _ _ f hf hflat hfp (affineBase R B) L M)

/-- The canonical enlargement diagram of actual Isom sections has its colimit property. -/
def HasAffineEnlargementIsomSectionsColimit : Prop :=
  Nonempty (IsColimit (affineAlgebraStageAboveSectionsCocone B
    (affineEnlargementIsomPresheaf B f L M)))

/-- Properness, flatness and local finite presentation imply the enlargement Isom colimit. -/
theorem hasAffineEnlargementIsomSectionsColimit (hB : B.FG)
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    HasAffineEnlargementIsomSectionsColimit B f L M :=
  ⟨affineEnlargementIsomSectionsIsColimit B f L M hB hf hflat hfp⟩

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard

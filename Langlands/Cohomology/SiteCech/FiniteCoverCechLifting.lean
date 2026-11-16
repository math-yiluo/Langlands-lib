import Langlands.Cohomology.SiteCech.FiniteCoverLifting
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Degree-zero presentations and local lifting for free Čech complexes -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w a

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {ι : Type a} (B : ι → C)
variable [LocallySmall.{w} C]

/-- The presheaf arrow of a finite basis cover, with the representable
presheaves valued in the specified coefficient universe. -/
def FiniteBasisCover.presheafArrow {U : C} (c : FiniteBasisCover J B U) :
    Arrow (Cᵒᵖ ⥤ Type w) :=
  Arrow.mk (Sigma.desc (fun j => shrinkYoneda.{w}.map (c.arrow j)))

/-- The degree-zero presheaf Čech object is the source of its arrow. -/
def presheafCechZeroIso (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    f.cechNerve.obj (op ⦋0⦌) ≅ f.left where
  hom := WidePullback.π (fun _ : Fin 1 => f.hom) 0
  inv := WidePullback.lift f.hom (fun _ : Fin 1 => 𝟙 _) (by intro j; simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      change Fin 1 at j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [WidePullback.lift_π]
    · simp [WidePullback.lift_base]
  inv_hom_id := by simp [WidePullback.lift_π]

variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]

/-- The degree-zero free Čech sheaf is the free sheaf on the arrow source. -/
def freeCechZeroIso (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    (freeCechChainComplex J R f).X 0 ≅ (freeSheafFunctor J R).obj f.left :=
  (freeSheafFunctor J R).mapIso (presheafCechZeroIso f)

omit [LocallySmall.{w} C] in
/-- The degree-zero comparison respects the actual Čech augmentation. -/
theorem freeCechZeroIso_hom_augmentation (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    (freeCechZeroIso J R f).hom ≫ (freeSheafFunctor J R).map f.hom =
      (freeCechAugmentation J R f).f 0 := by
  change (freeSheafFunctor J R).map
      (WidePullback.π (fun _ : Fin 1 => f.hom) 0) ≫
      (freeSheafFunctor J R).map f.hom =
    (freeSheafFunctor J R).map (WidePullback.base (fun _ : Fin 1 => f.hom))
  rw [← Functor.map_comp, WidePullback.π_arrow]

instance freeSheafFunctor_isLeftAdjoint : (freeSheafFunctor J R).IsLeftAdjoint :=
  (freeSheafAdjunction J R).isLeftAdjoint

/-- The degree-zero free Čech term of a finite basis cover is the finite
coproduct of free representable sheaves on its domains. -/
def FiniteBasisCover.freeCechZeroIso {U : C} (c : FiniteBasisCover J B U) :
    (freeCechChainComplex J R (c.presheafArrow J B)).X 0 ≅ c.freeSource J B R :=
  _root_.Langlands.Cohomology.SiteCech.freeCechZeroIso J R (c.presheafArrow J B) ≪≫
    PreservesCoproduct.iso (freeSheafFunctor J R)
      (fun j => shrinkYoneda.{w}.obj (B (c.index j)))

/-- The finite coproduct presentation identifies the two augmentations. -/
theorem FiniteBasisCover.freeCechZeroIso_hom_augmentation
    {U : C} (c : FiniteBasisCover J B U) :
    (c.freeCechZeroIso J B R).hom ≫ c.freeAugmentation J B R =
      (freeCechAugmentation J R (c.presheafArrow J B)).f 0 := by
  have h :
      (PreservesCoproduct.iso (freeSheafFunctor J R)
        (fun j => shrinkYoneda.{w}.obj (B (c.index j)))).hom ≫
          c.freeAugmentation J B R =
        (freeSheafFunctor J R).map (c.presheafArrow J B).hom := by
    dsimp only [FiniteBasisCover.freeSource, FiniteBasisCover.freeAugmentation,
      FiniteBasisCover.presheafArrow, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← cancel_epi (sigmaComparison (freeSheafFunctor J R)
      (fun j => shrinkYoneda.{w}.obj (B (c.index j))))]
    simp only [← PreservesCoproduct.inv_hom, Iso.inv_hom_id_assoc]
    apply Sigma.hom_ext
    intro j
    simp [sigmaComparison, ← Functor.map_comp]
  dsimp only [FiniteBasisCover.freeCechZeroIso, FiniteBasisCover.freeSource,
    FiniteBasisCover.freeAugmentation, FiniteBasisCover.presheafArrow,
    Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] at h ⊢
  rw [Iso.trans_hom]
  rw [Category.assoc, h]
  exact _root_.Langlands.Cohomology.SiteCech.freeCechZeroIso_hom_augmentation J R _

variable [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- Finite basis refinements give local lifting over the degree-zero
augmentation of the actual free Čech chain complex. -/
theorem exists_finiteBasisCover_cech_lift
    (hB : HasFiniteBasisCoverRefinements J B)
    (S : ShortComplex (Sheaf J (ModuleCat.{w} R))) (hS : S.ShortExact)
    (i : ι)
    (s : (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (B i)) ⟶ S.X₃) :
    ∃ (c : FiniteBasisCover J B (B i))
      (t : (freeCechChainComplex J R (c.presheafArrow J B)).X 0 ⟶ S.X₂),
      t ≫ S.g = (freeCechAugmentation J R (c.presheafArrow J B)).f 0 ≫ s := by
  obtain ⟨c, t, ht⟩ := exists_finiteBasisCover_lift_of_shortExact J B R hB S hS i s
  refine ⟨c, (c.freeCechZeroIso J B R).hom ≫ t, ?_⟩
  rw [Category.assoc, ht, ← Category.assoc,
    FiniteBasisCover.freeCechZeroIso_hom_augmentation]
  rfl

end Langlands.Cohomology.SiteCech

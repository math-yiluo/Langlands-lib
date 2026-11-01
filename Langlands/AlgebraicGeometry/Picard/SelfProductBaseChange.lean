import Langlands.AlgebraicGeometry.Picard.MumfordBundle

/-! # Self-products commute with the actual base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S T X : Scheme.{u}} (p : X ⟶ S) (b : T ⟶ S)

/-- The map between the self-products induced by the actual base-change
projection on both factors. -/
def selfProductBaseChangeMap :
    pullback (pullback.snd p b) (pullback.snd p b) ⟶ pullback p p :=
  pullback.map _ _ _ _ (pullback.fst p b) (pullback.fst p b) b
    pullback.condition.symm pullback.condition.symm

/-- The self-product after base change is the base change of the
self-product, with its first-factor structure map. -/
def selfProductBaseChangeIso :
    pullback (pullback.snd p b) (pullback.snd p b) ≅
      pullback (pullback.fst p p ≫ p) b where
  hom := pullback.lift (selfProductBaseChangeMap p b)
    (pullback.fst _ _ ≫ pullback.snd p b) (by
      simp only [selfProductBaseChangeMap, pullback.map,
        Category.assoc, pullback.lift_fst_assoc]
      rw [pullback.condition])
  inv := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst p p) (pullback.snd _ _)
      (by simpa only [Category.assoc] using
        (pullback.condition (f := pullback.fst p p ≫ p) (g := b))))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd p p) (pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition]
          exact pullback.condition))
    (by simp only [pullback.lift_snd])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [selfProductBaseChangeMap, pullback.map, Category.assoc,
          pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc]
    · apply pullback.hom_ext <;>
        simp [selfProductBaseChangeMap, pullback.map, Category.assoc,
          pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.condition]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [selfProductBaseChangeMap, pullback.map, Category.assoc,
          pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [Category.assoc, pullback.lift_snd,
        pullback.lift_fst_assoc]

@[reassoc (attr := simp)]
theorem selfProductBaseChangeIso_hom_fst :
    (selfProductBaseChangeIso p b).hom ≫ pullback.fst _ _ =
      selfProductBaseChangeMap p b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem selfProductBaseChangeIso_hom_snd :
    (selfProductBaseChangeIso p b).hom ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd p b :=
  pullback.lift_snd _ _ _

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S T : Scheme.{u}} (A : AbelianScheme S) (b : T ⟶ S)

/-- Precisely the canonical map `q` in the two-axis extension statement. -/
abbrev mumfordProductBaseChangeMap :
    (mumfordProduct ((baseChange b).obj A)).left ⟶ (mumfordProduct A).left :=
  selfProductBaseChangeMap A.X.hom b

/-- The actual Mumford self-product commutes with arbitrary base change. -/
def mumfordProductBaseChangeIso :
    (mumfordProduct ((baseChange b).obj A)).left ≅
      pullback (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) b :=
  selfProductBaseChangeIso A.X.hom b

@[reassoc (attr := simp)]
theorem mumfordProductBaseChangeIso_hom_fst :
    (mumfordProductBaseChangeIso A b).hom ≫ pullback.fst _ _ =
      mumfordProductBaseChangeMap A b :=
  selfProductBaseChangeIso_hom_fst A.X.hom b

end Langlands.AbelianScheme

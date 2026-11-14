import Langlands.GroupScheme.SubgroupFunctor.KernelCell
import Langlands.GroupScheme.FiniteEtaleImage

/-! # Kernel saturation and inverse images of binary open cells -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor.KernelCell

variable {S : Scheme.{u}} {G H U V P R : GroupScheme S}
    (q : G ⟶ H) (i : U ⟶ G) (p : P ⟶ G)
    (κ : (kernel q).X ⟶ U.X ⊗ P.X)
    (hκ : κ ≫ cellMultiplication i p = (kernelι q).hom.hom)

include hκ in
/-- A binary cell containing the full kernel is stable under multiplication
on the right by every point of that kernel. -/
theorem exists_lift_mul_kernel {T : Over S}
    (a : T ⟶ U.X ⊗ P.X) (n : T ⟶ G.X) (hn : n ≫ q.hom.hom = 1) :
    ∃ b : T ⟶ U.X ⊗ P.X,
      b ≫ cellMultiplication i p = (a ≫ cellMultiplication i p) * n := by
  let v : T ⟶ G.X := (a ≫ snd U.X P.X ≫ p.hom.hom) * n *
    (a ≫ snd U.X P.X ≫ p.hom.hom)⁻¹
  have hv : v ≫ q.hom.hom = 1 := by
    simp only [v, MonObj.mul_comp, GrpObj.inv_comp, hn, mul_one, mul_inv_cancel]
  let t : T ⟶ (kernel q).X := (kernelPointsEquiv q T).symm ⟨v, hv⟩
  let b : T ⟶ U.X ⊗ P.X := t ≫ κ
  have hb : b ≫ cellMultiplication i p = v := by
    rw [show b = t ≫ κ from rfl, Category.assoc, hκ]
    exact congrArg Subtype.val ((kernelPointsEquiv q T).apply_symm_apply ⟨v, hv⟩)
  have hab : (b ≫ fst U.X P.X ≫ i.hom.hom) *
      (b ≫ snd U.X P.X ≫ p.hom.hom) = v := by
    simpa only [cellMultiplication, MonObj.comp_mul, Category.assoc] using hb
  refine ⟨lift ((a ≫ fst U.X P.X) * (b ≫ fst U.X P.X))
    ((b ≫ snd U.X P.X) * (a ≫ snd U.X P.X)), ?_⟩
  simp only [lift_cellMultiplication, MonObj.mul_comp, Category.assoc]
  calc
    _ = (a ≫ fst U.X P.X ≫ i.hom.hom) *
        ((b ≫ fst U.X P.X ≫ i.hom.hom) *
          (b ≫ snd U.X P.X ≫ p.hom.hom)) *
        (a ≫ snd U.X P.X ≫ p.hom.hom) := by simp only [mul_assoc]
    _ = (a ≫ fst U.X P.X ≫ i.hom.hom) * v *
        (a ≫ snd U.X P.X ≫ p.hom.hom) := by rw [hab]
    _ = _ := by
      simp only [v, cellMultiplication, MonObj.comp_mul, mul_assoc,
        inv_mul_cancel, mul_one]

variable (f : U ⟶ V) (g : P ⟶ R) (j : V ⟶ H) (r : R ⟶ H)
    (hi : i ≫ q = f ≫ j) (hp : p ≫ q = g ≫ r)
    [Surjective f.hom.hom.left] [Surjective g.hom.hom.left]
    [IsOpenImmersion (cellMultiplication i p).left]

include hκ hi hp in
/-- Compatible quotient cells with surjective factor maps and full kernel
coverage have exactly the same inverse image on every test scheme. -/
theorem exists_lift_iff {T : Over S} (x : T ⟶ G.X) :
    (∃ a : T ⟶ U.X ⊗ P.X, a ≫ cellMultiplication i p = x) ↔
      ∃ b : T ⟶ V.X ⊗ R.X, b ≫ cellMultiplication j r = x ≫ q.hom.hom := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a ≫ (f.hom.hom ⊗ₘ g.hom.hom), ?_⟩
    rw [Category.assoc, ← chart_square q f g i p j r hi hp, ← Category.assoc]
  · rintro ⟨b, hb⟩
    let c := f.hom.hom ⊗ₘ g.hom.hom
    have : Surjective c.left := by
      let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
        ⟨fun _ _ hf hg => ⟨hg.surj.comp hf.surj⟩⟩
      exact MorphismProperty.pullbackMap (P := @Surjective.{u})
        inferInstance inferInstance (Over.w f.hom.hom).symm (Over.w g.hom.hom).symm
    let W : Over S := Over.mk (pullback.fst b.left c.left ≫ T.hom)
    let a : W ⟶ T := Over.homMk (pullback.fst b.left c.left) rfl
    let z : W ⟶ U.X ⊗ P.X := Over.homMk (pullback.snd b.left c.left) (by
      rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w b]
      rfl)
    have haz : a ≫ b = z ≫ c := Over.OverMorphism.ext pullback.condition
    have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
    have he : (a ≫ x) ≫ q.hom.hom =
        (z ≫ cellMultiplication i p) ≫ q.hom.hom := by
      rw [Category.assoc, ← hb, ← Category.assoc, haz, Category.assoc]
      rw [show c = f.hom.hom ⊗ₘ g.hom.hom from rfl,
        ← chart_square q f g i p j r hi hp, ← Category.assoc]
    let n : W ⟶ G.X := (z ≫ cellMultiplication i p)⁻¹ * (a ≫ x)
    have hn : n ≫ q.hom.hom = 1 := by
      dsimp only [n]
      rw [MonObj.mul_comp, GrpObj.inv_comp, he, inv_mul_cancel]
    obtain ⟨d, hd⟩ := exists_lift_mul_kernel q i p κ hκ z n hn
    have hd' : d ≫ cellMultiplication i p = a ≫ x := by
      simpa only [n, mul_inv_cancel_left] using hd
    have hrange := FiniteEtaleImage.range_subset_of_surjective_factor
      (cellMultiplication i p) x a d hd'
    exact ⟨FiniteEtaleImage.liftOver (cellMultiplication i p) x hrange,
      FiniteEtaleImage.liftOver_fac _ _ _⟩

/-- Coordinates in the source cell of a point whose quotient lies in the
target cell. -/
def quotientCellLift {T : Over S} (x : T ⟶ G.X) (b : T ⟶ V.X ⊗ R.X)
    (hb : b ≫ cellMultiplication j r = x ≫ q.hom.hom) : T ⟶ U.X ⊗ P.X :=
  ((exists_lift_iff q i p κ hκ f g j r hi hp x).mpr ⟨b, hb⟩).choose

@[reassoc]
theorem quotientCellLift_comp {T : Over S} (x : T ⟶ G.X) (b : T ⟶ V.X ⊗ R.X)
    (hb : b ≫ cellMultiplication j r = x ≫ q.hom.hom) :
    quotientCellLift q i p κ hκ f g j r hi hp x b hb ≫ cellMultiplication i p = x :=
  ((exists_lift_iff q i p κ hκ f g j r hi hp x).mpr ⟨b, hb⟩).choose_spec

end Langlands.GroupScheme.SubgroupFunctor.KernelCell

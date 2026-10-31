import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # The fibre of the first projection of a square along a section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {X S : Scheme.{u}} (s : X ⟶ S) (x : S ⟶ X) (hx : x ≫ s = 𝟙 S)

/-- The inclusion `{x} × X → X ×_S X`. -/
def squareFirstInclusion : X ⟶ pullback s s :=
  pullback.lift (s ≫ x) (𝟙 X) (by simp [Category.assoc, hx])

@[reassoc (attr := simp)]
lemma squareFirstInclusion_fst : squareFirstInclusion s x hx ≫ pullback.fst s s = s ≫ x := by
  simp only [squareFirstInclusion, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma squareFirstInclusion_snd : squareFirstInclusion s x hx ≫ pullback.snd s s = 𝟙 X := by
  simp only [squareFirstInclusion, pullback.lift_snd]

include hx

@[reassoc (attr := simp)]
lemma squareFirstFibre_structure :
    pullback.fst (pullback.fst s s) x ≫ pullback.snd s s ≫ s =
      pullback.snd (pullback.fst s s) x := by
  rw [← pullback.condition (f := s) (g := s), pullback.condition_assoc]
  simp [hx]

@[reassoc (attr := simp)]
lemma squareFirstFibre_inclusion :
    (pullback.fst (pullback.fst s s) x ≫ pullback.snd s s) ≫
      squareFirstInclusion s x hx = pullback.fst (pullback.fst s s) x := by
  apply pullback.hom_ext
  · simp only [Category.assoc, squareFirstInclusion_fst, squareFirstFibre_structure_assoc s x hx]
    exact (pullback.condition (f := pullback.fst s s) (g := x)).symm
  · simp

/-- The first-projection fibre over the section `x` is the second copy of `X`. -/
def squareFirstFibreIso : pullback (pullback.fst s s) x ≅ X where
  hom := pullback.fst (pullback.fst s s) x ≫ pullback.snd s s
  inv := pullback.lift (squareFirstInclusion s x hx) s (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, Category.id_comp] using squareFirstFibre_inclusion s x hx
    · simpa only [Category.assoc, pullback.lift_snd, Category.id_comp] using squareFirstFibre_structure s x hx
  inv_hom_id := by
    simp only [← Category.assoc, pullback.lift_fst, squareFirstInclusion_snd]

/-- The actual first-projection fibre cohomology is the cohomology of the section inclusion. -/
def squareFirstFibreCohomologyIso {R : CommRingCat.{u}} (s : X ⟶ Spec R)
    (x : Spec R ⟶ X) (hx : x ≫ s = 𝟙 (Spec R))
    (M : (pullback s s).Modules) (n : ℕ) :
    (Modules.DerivedSections.relativeCohomology (pullback.snd (pullback.fst s s) x) n).obj
      ((Scheme.Modules.pullback (pullback.fst (pullback.fst s s) x)).obj M) ≅
    (Modules.DerivedSections.relativeCohomology s n).obj
      ((Scheme.Modules.pullback (squareFirstInclusion s x hx)).obj M) := by
  let e := squareFirstFibreIso s x hx
  have hs : e.hom ≫ s = pullback.snd (pullback.fst s s) x :=
    squareFirstFibre_structure s x hx
  have hi : e.hom ≫ squareFirstInclusion s x hx = pullback.fst (pullback.fst s s) x :=
    squareFirstFibre_inclusion s x hx
  let eM : (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback (squareFirstInclusion s x hx)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.fst s s) x)).obj M :=
    (Scheme.Modules.pullbackComp e.hom (squareFirstInclusion s x hx)).app M ≪≫
      (Scheme.Modules.pullbackCongr hi).app M
  rw [← hs]
  exact (Modules.DerivedSections.relativeCohomology (e.hom ≫ s) n).mapIso eM.symm ≪≫
    Modules.DerivedSections.relativeCohomologyPullbackIso e s _ n

end Langlands.AlgebraicGeometry.Picard

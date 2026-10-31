import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # The fibre of the second projection of a square along a section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {X S : Scheme.{u}} (s : X ⟶ S) (x : S ⟶ X) (hx : x ≫ s = 𝟙 S)

/-- The inclusion `X × {x} → X ×_S X`. -/
def squareSecondInclusion : X ⟶ pullback s s :=
  pullback.lift (𝟙 X) (s ≫ x) (by simp [Category.assoc, hx])

@[reassoc (attr := simp)]
lemma squareSecondInclusion_fst : squareSecondInclusion s x hx ≫ pullback.fst s s = 𝟙 X := by
  simp only [squareSecondInclusion, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma squareSecondInclusion_snd : squareSecondInclusion s x hx ≫ pullback.snd s s = s ≫ x := by
  simp only [squareSecondInclusion, pullback.lift_snd]

include hx

@[reassoc (attr := simp)]
lemma squareSecondFibre_structure :
    pullback.fst (pullback.snd s s) x ≫ pullback.fst s s ≫ s =
      pullback.snd (pullback.snd s s) x := by
  rw [pullback.condition (f := s) (g := s), pullback.condition_assoc]
  simp [hx]

@[reassoc (attr := simp)]
lemma squareSecondFibre_inclusion :
    (pullback.fst (pullback.snd s s) x ≫ pullback.fst s s) ≫
      squareSecondInclusion s x hx = pullback.fst (pullback.snd s s) x := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, squareSecondInclusion_snd, squareSecondFibre_structure_assoc s x hx]
    exact (pullback.condition (f := pullback.snd s s) (g := x)).symm

/-- The second-projection fibre over the section `x` is the first copy of `X`. -/
def squareSecondFibreIso : pullback (pullback.snd s s) x ≅ X where
  hom := pullback.fst (pullback.snd s s) x ≫ pullback.fst s s
  inv := pullback.lift (squareSecondInclusion s x hx) s (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, Category.id_comp] using squareSecondFibre_inclusion s x hx
    · simpa only [Category.assoc, pullback.lift_snd, Category.id_comp] using squareSecondFibre_structure s x hx
  inv_hom_id := by
    simp only [← Category.assoc, pullback.lift_fst, squareSecondInclusion_fst]

/-- Actual second-projection fibre cohomology equals the cohomology of its section inclusion. -/
def squareSecondFibreCohomologyIso {R : CommRingCat.{u}} (s : X ⟶ Spec R)
    (x : Spec R ⟶ X) (hx : x ≫ s = 𝟙 (Spec R))
    (M : (pullback s s).Modules) (n : ℕ) :
    (Modules.DerivedSections.relativeCohomology (pullback.snd (pullback.snd s s) x) n).obj
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd s s) x)).obj M) ≅
    (Modules.DerivedSections.relativeCohomology s n).obj
      ((Scheme.Modules.pullback (squareSecondInclusion s x hx)).obj M) := by
  let e := squareSecondFibreIso s x hx
  have hs : e.hom ≫ s = pullback.snd (pullback.snd s s) x :=
    squareSecondFibre_structure s x hx
  have hi : e.hom ≫ squareSecondInclusion s x hx = pullback.fst (pullback.snd s s) x :=
    squareSecondFibre_inclusion s x hx
  let eM : (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback (squareSecondInclusion s x hx)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd s s) x)).obj M :=
    (Scheme.Modules.pullbackComp e.hom (squareSecondInclusion s x hx)).app M ≪≫
      (Scheme.Modules.pullbackCongr hi).app M
  rw [← hs]
  exact (Modules.DerivedSections.relativeCohomology (e.hom ≫ s) n).mapIso eM.symm ≪≫
    Modules.DerivedSections.relativeCohomologyPullbackIso e s _ n

end Langlands.AlgebraicGeometry.Picard

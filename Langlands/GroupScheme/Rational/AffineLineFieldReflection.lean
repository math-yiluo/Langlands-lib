import Langlands.GroupScheme.Rational.AffineLineExtensions
import Langlands.GroupScheme.Rational.PointedFamilyFieldExtension

/-! # Reflection of affine-line constancy through field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

/-- Extend an actual affine-line morphism, using the canonical affine-line source. -/
def baseChangeMap {B B' : Scheme.{u}} (b : B' ⟶ B) {X : Over B}
    (a : scheme B ⟶ X) : scheme B' ⟶ (Over.pullback b).obj X :=
  (baseChangeIso b).hom ≫ (Over.pullback b).map a

end AffineLine

namespace HasConstantAffineLineMaps

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Constancy of all actual affine-line maps reflects through any field extension. -/
theorem of_fieldExtension
    (hG : HasConstantAffineLineMaps
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    HasConstantAffineLineMaps G := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc k K
  let : Surjective b := hb₁
  let : Flat b := hb₂
  let : QuasiCompact b := hb₃
  intro a
  refine ⟨AffineLine.zeroSection _ ≫ a, ?_⟩
  apply (Over.pullback b).map_injective
  apply (cancel_epi (AffineLine.baseChangeIso b).hom).mp
  have ha := hG.eq_to_zeroSection (AffineLine.baseChangeMap b a)
  dsimp only [AffineLine.baseChangeMap] at ha
  calc
    _ = toUnit _ ≫
        (AffineLine.zeroSection _ ≫ (AffineLine.baseChangeIso b).hom) ≫
          (Over.pullback b).map a := by simpa only [Category.assoc] using ha
    _ = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback b) ≫
        (Over.pullback b).map (AffineLine.zeroSection _) ≫
          (Over.pullback b).map a := by
      rw [← AffineLine.zeroSection_baseChange, Category.assoc]
    _ = (AffineLine.baseChangeIso b).hom ≫
        (Over.pullback b).map (toUnit _) ≫
          (Over.pullback b).map (AffineLine.zeroSection _) ≫
            (Over.pullback b).map a := by
      rw [← Functor.Monoidal.toUnit_ε]
      simp only [← Category.assoc, comp_toUnit]
    _ = _ := by simp only [Functor.map_comp]

end HasConstantAffineLineMaps

end Langlands.GroupScheme

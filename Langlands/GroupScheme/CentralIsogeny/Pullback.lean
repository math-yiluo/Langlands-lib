import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Central isogenies in Cartesian squares of group schemes -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {A B P G : GroupScheme S}

/-- A pullback of a central isogeny along a group-scheme homomorphism is a
central isogeny. The square is required on the underlying schemes over the base. -/
theorem IsCentralIsogeny.of_isPullback
    {e : A ⟶ P} {v : A ⟶ B} {i : P ⟶ G} {f : B ⟶ G}
    (hf : IsCentralIsogeny f)
    (h : IsPullback e.hom.hom v.hom.hom i.hom.hom f.hom.hom) :
    IsCentralIsogeny e := by
  have hs := h.map (Over.forget S)
  refine ⟨MorphismProperty.of_isPullback (P := isogenyProperty) hs.flip hf.isIsogeny,
    MorphismProperty.of_isPullback hs.flip hf.locallyOfFinitePresentation, ?_⟩
  apply (isCentral_kernelι_iff e).mpr
  intro T x hx
  rw [mem_center]
  intro T' a y
  have he : (a ≫ x) ≫ e.hom.hom = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  have hv : ((a ≫ x) ≫ v.hom.hom) ≫ f.hom.hom = 1 := by
    rw [Category.assoc, ← h.w, ← Category.assoc, he, MonObj.one_comp]
  have hc := mem_center.mp (hf.mem_center_of_comp_eq_one hv)
    T' (𝟙 T') (y ≫ v.hom.hom)
  rw [Category.id_comp] at hc
  change (a ≫ x) * y = y * (a ≫ x)
  apply h.hom_ext
  · rw [MonObj.mul_comp, MonObj.mul_comp, he, one_mul, mul_one]
  · rw [MonObj.mul_comp, MonObj.mul_comp]
    exact hc.eq

end Langlands.GroupScheme

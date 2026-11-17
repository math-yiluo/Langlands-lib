import Langlands.GroupScheme.LocalSubgroupConjugacy
import Langlands.GroupScheme.CocycleTorsor

/-! # Global subgroup conjugacy from a trivial difference cocycle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G B B' : GroupScheme S}
  (i : B ⟶ G) (i' : B' ⟶ G) [Mono i.hom.hom] [Mono i'.hom.hom]
  {U : Over S} [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]
  (g : U ⟶ G.X) (hg : IsConjugatingPoint (range i) (range i') g)
  (hself : (range i).normalizer = range i)

/-- Triviality of the actual subgroup-valued difference cocycle gives an
actual conjugating section over the original base. -/
theorem IsConjugatingPoint.exists_base_of_isTrivial
    (hξ : ((Cocycle.coboundary g⁻¹).lift i
      (hg.coboundary_inv_lifts i i' hself)).IsTrivial) :
    ∃ s : Over.mk (𝟙 S) ⟶ G.X, IsConjugatingPoint (range i) (range i') s := by
  let ξ := (Cocycle.coboundary g⁻¹).lift i (hg.coboundary_inv_lifts i i' hself)
  obtain ⟨f, hf⟩ := hξ
  let J := f ≫ i.hom.hom
  have hJ {Z : Over S} (a b : Z ⟶ U) :
      (a ≫ J) * (b ≫ J)⁻¹ = (a ≫ g)⁻¹ * (b ≫ g) := by
    have h := (Cocycle.coboundary g⁻¹).lift_toFun i
      (hg.coboundary_inv_lifts i i' hself) a b
    rw [hf a b, MonObj.mul_comp, GrpObj.inv_comp] at h
    simpa only [Cocycle.coboundary, GrpObj.comp_inv, inv_inv, J, Category.assoc] using h
  let P := g * J
  have hP {Z : Over S} (a b : Z ⟶ U) : a ≫ P = b ≫ P := by
    simp only [P, MonObj.comp_mul]
    calc
      (a ≫ g) * (a ≫ J) =
          (a ≫ g) * ((a ≫ J) * (b ≫ J)⁻¹) * (b ≫ J) := by group
      _ = (a ≫ g) * ((a ≫ g)⁻¹ * (b ≫ g)) * (b ≫ J) := by rw [hJ]
      _ = (b ≫ g) * (b ≫ J) := by group
  let p : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom (by simp)
  let : QuasiCompact p.left := inferInstanceAs (QuasiCompact U.hom)
  let : Flat p.left := inferInstanceAs (Flat U.hom)
  let : Surjective p.left := inferInstanceAs (Surjective U.hom)
  let : EffectiveEpi p.left := inferInstanceAs (EffectiveEpi U.hom)
  obtain ⟨s, hs⟩ := CocycleTorsor.exists_desc p P (fun a b _ => hP a b)
  refine ⟨s, ?_⟩
  apply IsConjugatingPoint.of_cover (hasFpqcMembershipDescent_range i)
    (hasFpqcMembershipDescent_range i') p
  rw [hs]
  exact hg.mul_of_mem_normalizer
    (le_def.mp (le_normalizer (range i)) U (mem_range.mpr ⟨f, rfl⟩))

/-- A chosen global conjugating section obtained from vanishing of the actual
source-subgroup difference cocycle. -/
def globalConjugatingPoint
    (hξ : ((Cocycle.coboundary g⁻¹).lift i
      (hg.coboundary_inv_lifts i i' hself)).IsTrivial) : Over.mk (𝟙 S) ⟶ G.X :=
  Classical.choose (hg.exists_base_of_isTrivial i i' g hself hξ)

/-- The chosen section conjugates the complete represented subgroup functors. -/
theorem globalConjugatingPoint_spec
    (hξ : ((Cocycle.coboundary g⁻¹).lift i
      (hg.coboundary_inv_lifts i i' hself)).IsTrivial) :
    range (i ≫ (G.innerIso (globalConjugatingPoint i i' g hg hself hξ)).hom) = range i' :=
  (isConjugatingPoint_iff_range_innerIso i i' _).mp
    (Classical.choose_spec (hg.exists_base_of_isTrivial i i' g hself hξ))

end SubgroupFunctor

end Langlands.GroupScheme

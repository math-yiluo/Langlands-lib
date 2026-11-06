import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.RepresentedSubgroup

/-! # The full kernel of commuting subgroup multiplication -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H K G Z : GroupScheme S}
variable (j : H ⟶ G) (i : K ⟶ G)
variable (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

/-- Each first coordinate of the full multiplication kernel is central in the
first factor, on every test scheme and after every restriction. -/
theorem commutingSubgroupMultiplication_left_mem_center [Mono j.hom.hom]
    {T : Over S} (x : T ⟶ (H ⊗ K).X)
    (hx : x ≫ (commutingSubgroupMultiplicationHom j i hc).hom.hom = 1) :
    x ≫ fst H.X K.X ∈ (center H).carrier T := by
  have hrel : (x ≫ fst H.X K.X) ≫ j.hom.hom =
      ((x ≫ snd H.X K.X) ≫ i.hom.hom)⁻¹ := by
    apply mul_eq_one_iff_eq_inv.mp
    simpa only [commutingSubgroupMultiplicationHom_hom, subgroupMultiplication,
      MonObj.comp_mul, ← Category.assoc] using hx
  intro T' a y
  apply (cancel_mono j.hom.hom).mp
  simp only [MonObj.mul_comp]
  have hres : ((a ≫ x) ≫ fst H.X K.X) ≫ j.hom.hom =
      (((a ≫ x) ≫ snd H.X K.X) ≫ i.hom.hom)⁻¹ := by
    simpa only [Category.assoc, GrpObj.comp_inv] using congrArg (a ≫ ·) hrel
  simp only [Category.assoc] at hres ⊢
  rw [hres]
  simpa only [Category.assoc] using
    (hc T' y ((a ≫ x) ≫ snd H.X K.X)).inv_right.symm.eq

/-- Each second coordinate of the full multiplication kernel is central in the
second factor, on every test scheme and after every restriction. -/
theorem commutingSubgroupMultiplication_right_mem_center [Mono i.hom.hom]
    {T : Over S} (x : T ⟶ (H ⊗ K).X)
    (hx : x ≫ (commutingSubgroupMultiplicationHom j i hc).hom.hom = 1) :
    x ≫ snd H.X K.X ∈ (center K).carrier T := by
  have hrel : (x ≫ snd H.X K.X) ≫ i.hom.hom =
      ((x ≫ fst H.X K.X) ≫ j.hom.hom)⁻¹ := by
    apply mul_eq_one_iff_eq_inv'.mp
    simpa only [commutingSubgroupMultiplicationHom_hom, subgroupMultiplication,
      MonObj.comp_mul, ← Category.assoc] using hx
  intro T' a y
  apply (cancel_mono i.hom.hom).mp
  simp only [MonObj.mul_comp]
  have hres : ((a ≫ x) ≫ snd H.X K.X) ≫ i.hom.hom =
      (((a ≫ x) ≫ fst H.X K.X) ≫ j.hom.hom)⁻¹ := by
    simpa only [Category.assoc, GrpObj.comp_inv] using congrArg (a ≫ ·) hrel
  simp only [Category.assoc] at hres ⊢
  rw [hres]
  simpa only [Category.assoc] using
    (hc T' ((a ≫ x) ≫ fst H.X K.X) y).inv_left.eq

/-- Monomorphic commuting factors have a central full scheme-theoretic
multiplication kernel, without any smoothness or reducedness assumption. -/
theorem isCentral_kernelι_commutingSubgroupMultiplicationHom
    [Mono j.hom.hom] [Mono i.hom.hom] :
    IsCentral (kernelι (commutingSubgroupMultiplicationHom j i hc)) := by
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx T' a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (commutingSubgroupMultiplication_left_mem_center j i hc x hx
      T' a (y ≫ fst H.X K.X)).eq
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (commutingSubgroupMultiplication_right_mem_center j i hc x hx
      T' a (y ≫ snd H.X K.X)).eq

/-- The first coordinate gives an actual map from the full multiplication
kernel into any representative of the full centre of the first factor. -/
def commutingMultiplicationKernelLeftCenterMap [Mono j.hom.hom]
    (z : Z ⟶ H) (hz : IsSchemeTheoreticCenter z) :
    kernel (commutingSubgroupMultiplicationHom j i hc) ⟶ Z :=
  hz.isRepresentedBy.factorHom
    (kernelι (commutingSubgroupMultiplicationHom j i hc) ≫ fst H K) (by
      intro T x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      change (y ≫ (kernelι (commutingSubgroupMultiplicationHom j i hc)).hom.hom) ≫
        fst H.X K.X ∈ (center H).carrier T
      apply commutingSubgroupMultiplication_left_mem_center j i hc
      exact (kernelPointsEquiv _ T y).property)

/-- The centre factorization retains the original first-coordinate map. -/
theorem commutingMultiplicationKernelLeftCenterMap_comp [Mono j.hom.hom]
    (z : Z ⟶ H) (hz : IsSchemeTheoreticCenter z) :
    commutingMultiplicationKernelLeftCenterMap j i hc z hz ≫ z =
      kernelι (commutingSubgroupMultiplicationHom j i hc) ≫ fst H K :=
  hz.isRepresentedBy.factorHom_comp _ _

end Langlands.GroupScheme

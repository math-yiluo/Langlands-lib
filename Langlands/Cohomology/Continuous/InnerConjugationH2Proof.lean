import Langlands.Cohomology.Continuous.InnerConjugationH2Statement
import Langlands.Cohomology.Continuous.InnerConjugationPrism
import Mathlib.Tactic.Abel

open CategoryTheory

namespace Langlands.Continuous

universe u v w

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : TopRep.{max v w} k G)

/-- The degree-two inner-conjugation cochain map is simultaneous right translation. -/
theorem innerConjugationCochains_two_apply (a : G)
    (f : (TopRep.homogeneousCochains A).X 2) (x y z : G) :
    ((((innerConjugationCochains A a).f 2).hom f).1 x y z) =
      f.1 (x * a⁻¹) (y * a⁻¹) (z * a⁻¹) := by
  have h := congrArg (fun F : TopRep.resolutionX A 3 =>
    F (x * a⁻¹) (y * a⁻¹) (z * a⁻¹)) (f.property a⁻¹)
  change A.ρ a⁻¹ (f.1 (a * x * a⁻¹) (a * y * a⁻¹) (a * z * a⁻¹)) = _
  change A.ρ a⁻¹ (f.1 (a⁻¹⁻¹ * (x * a⁻¹)) (a⁻¹⁻¹ * (y * a⁻¹))
    (a⁻¹⁻¹ * (z * a⁻¹))) = _ at h
  simpa only [inv_inv, mul_assoc] using h

/-- The four-term identity for an actual homogeneous continuous two-cocycle. -/
theorem homogeneousTwoCocycle_identity (f : (TopRep.homogeneousCochains A).X 2)
    (hf : ((TopRep.homogeneousCochains A).d 2 3).hom f = 0)
    (x y z q : G) :
    f.1 y z q - (f.1 x z q - (f.1 x y q - f.1 x y z)) = 0 := by
  have h := congrArg (fun F : (TopRep.homogeneousCochains A).X 3 =>
    F.1 x y z q) hf
  change ((TopRep.d A 3).hom f.1) x y z q = 0 at h
  exact h

/-- The elementary prism identity, expressed only by its pointwise formula. -/
theorem homogeneousTwoCocycle_prism_identity
    (f : (TopRep.homogeneousCochains A).X 2)
    (hf : ((TopRep.homogeneousCochains A).d 2 3).hom f = 0)
    (t x y z : G) :
    (f.1 y (y*t) (z*t) - f.1 y z (z*t)) -
      ((f.1 x (x*t) (z*t) - f.1 x z (z*t)) -
        (f.1 x (x*t) (y*t) - f.1 x y (y*t))) =
      f.1 (x*t) (y*t) (z*t) - f.1 x y z := by
  have h₁ := homogeneousTwoCocycle_identity A f hf x (x*t) (y*t) (z*t)
  have h₂ := homogeneousTwoCocycle_identity A f hf x y (y*t) (z*t)
  have h₃ := homogeneousTwoCocycle_identity A f hf x y z (z*t)
  calc
    _ = (f.1 (x*t) (y*t) (z*t) - f.1 x y z) -
        (f.1 (x*t) (y*t) (z*t) -
          (f.1 x (y*t) (z*t) - (f.1 x (x*t) (z*t) - f.1 x (x*t) (y*t)))) +
        (f.1 y (y*t) (z*t) -
          (f.1 x (y*t) (z*t) - (f.1 x y (z*t) - f.1 x y (y*t)))) -
        (f.1 y z (z*t) - (f.1 x z (z*t) - (f.1 x y (z*t) - f.1 x y z))) := by abel
    _ = _ := by rw [h₁, h₂, h₃]; abel

/-- Descent of pointwise boundary witnesses through the actual homology projection. -/
theorem homologyMap_two_eq_id_of_boundaries
    (C : CochainComplex (TopModuleCat.{w} k) ℕ) (φ : C ⟶ C)
    (h : ∀ f : C.X 2, (C.d 2 3).hom f = 0 →
      ∃ s : C.X 1, (C.d 1 2).hom s = (φ.f 2).hom f - f) :
    HomologicalComplex.homologyMap φ 2 = 𝟙 (C.homology 2) := by
  rw [← cancel_epi (C.homologyπ 2), Category.comp_id,
    HomologicalComplex.homologyπ_naturality]
  ext c
  have hc : (C.d 2 3).hom ((C.iCycles 2).hom c) = 0 :=
    ConcreteCategory.congr_hom (C.iCycles_d 2 3) c
  obtain ⟨s, hs⟩ := h ((C.iCycles 2).hom c) hc
  have he : (HomologicalComplex.cyclesMap φ 2).hom c - c =
      (C.toCycles 1 2).hom s := by
    apply (ModuleCat.mono_iff_injective
      ((forget₂ (TopModuleCat k) (ModuleCat k)).map (C.iCycles 2))).mp inferInstance
    rw [map_sub]
    have hmap := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ 2) c
    have hd := ConcreteCategory.congr_hom (C.toCycles_i 1 2) s
    exact (congrArg (fun b => b - (C.iCycles 2).hom c) hmap).trans (hs.symm.trans hd.symm)
  apply sub_eq_zero.mp
  change (C.homologyπ 2).hom ((HomologicalComplex.cyclesMap φ 2).hom c) -
      (C.homologyπ 2).hom c = 0
  rw [← map_sub, he]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) s

/-- The actual degree-two cohomology map is trivial once its continuous prism is supplied. -/
theorem innerConjugationH2_eq_of_prism (a : G)
    (s : (TopRep.homogeneousCochains A).X 2 → (TopRep.homogeneousCochains A).X 1)
    (hs : ∀ f x y, (s f).1 x y =
      f.1 x (x * a⁻¹) (y * a⁻¹) - f.1 x y (y * a⁻¹)) :
    innerConjugationMap A a 2 = 𝟙 (continuousCohomology 2 A) := by
  apply homologyMap_two_eq_id_of_boundaries
  intro f hf
  refine ⟨s f, ?_⟩
  apply Subtype.ext
  ext x y z
  change (s f).1 y z - ((s f).1 x z - (s f).1 x y) =
    (((innerConjugationCochains A a).f 2).hom f).1 x y z - f.1 x y z
  rw [hs, hs, hs, innerConjugationCochains_two_apply]
  exact homogeneousTwoCocycle_prism_identity A f hf a⁻¹ x y z

/-- Inner conjugation acts trivially on the actual continuous degree-two cohomology. -/
theorem innerConjugationH2Triviality : InnerConjugationH2Triviality.{u,v,w} := by
  intro k G _ _ _ _ _ _ _ A a
  exact innerConjugationH2_eq_of_prism A a
    (innerConjugationPrism A a⁻¹) (innerConjugationPrism_apply A a⁻¹)

end Langlands.Continuous

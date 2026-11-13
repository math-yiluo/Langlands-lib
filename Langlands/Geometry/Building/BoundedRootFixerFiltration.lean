import Langlands.Geometry.Building.IntegerValuationBuildingData
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # A bounded root fixer is one filtration level -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

private theorem coe_csSup_le_iff {s : Set ℝ} (hne : s.Nonempty)
    (hb : BddAbove s) (z : WithTop ℝ) :
    ((sSup s : ℝ) : WithTop ℝ) ≤ z ↔ ∀ r ∈ s, (r : WithTop ℝ) ≤ z := by
  cases z using WithTop.recTopCoe with
  | top => simp
  | coe z => simpa only [WithTop.coe_le_coe] using csSup_le_iff hb hne

/-- The real level at a reference point needed to fix all points of `Ω`
in the relative-root subgroup. -/
def rootFixerDepth (a : relativeRoots i) (x : D.Apartment) (Ω : Set D.Apartment) : ℝ :=
  sSup ((fun y => -D.affineFunctional a x 0 y) '' Ω)

/-- A nonempty root fixer with bounded affine thresholds is the single
filtration level given by their real supremum. -/
theorem rootFixer_eq_filtration_csSup (a : relativeRoots i) (x : D.Apartment)
    {Ω : Set D.Apartment} (hne : Ω.Nonempty)
    (hb : BddAbove ((fun y => -D.affineFunctional a x 0 y) '' Ω)) :
    D.rootFixer a Ω = D.filtration x a (D.rootFixerDepth a x Ω) := by
  have hlevel (y : D.Apartment) :
      D.filtration y a 0 = D.filtration x a (-D.affineFunctional a x 0 y) := by
    calc
      D.filtration y a 0 = D.filtration ((y -ᵥ x) +ᵥ x) a 0 := by
        rw [vsub_vadd]
      _ = D.filtration x a (-D.affineFunctional a x 0 y) := by
        rw [D.filtration_vadd]
        simp only [affineFunctional_apply, add_zero, zero_sub]
  apply Subgroup.ext
  intro g
  rw [mem_rootFixer, mem_filtration]
  constructor
  · rintro ⟨hg, hΩg⟩
    refine ⟨hg, (coe_csSup_le_iff (hne.image _) hb _).mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_filtration.mp (hlevel y ▸ hΩg y hy)).2
  · rintro ⟨hg, hdepth⟩
    refine ⟨hg, fun y hy => ?_⟩
    rw [hlevel y, mem_filtration]
    exact ⟨hg, (coe_csSup_le_iff (hne.image _) hb _).mp hdepth _
      ⟨y, hy, rfl⟩⟩

/-- Affine boundedness supplies a single filtration level for each relative
root, at any chosen reference point of the apartment. -/
theorem rootFixer_eq_filtration_of_bounded (a : relativeRoots i) (x : D.Apartment)
    {Ω : Set D.Apartment} (hne : Ω.Nonempty)
    (hb : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    D.rootFixer a Ω = D.filtration x a (D.rootFixerDepth a x Ω) :=
  D.rootFixer_eq_filtration_csSup a x hne (hb (-D.affineFunctional a x 0))

end Langlands.Geometry.Building.KPApartmentData

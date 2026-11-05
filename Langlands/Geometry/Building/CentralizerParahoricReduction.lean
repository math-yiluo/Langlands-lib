import Langlands.Geometry.Building.CentralizerParahoricStatement
import Langlands.Geometry.Building.KPParahoricProduct

/-!
# Reduction of the centralizer part to singleton sharp fixers

These are algebraic reductions of KP Lemma 7.4.3. The singleton sharp
intersection inclusion remains a mathematical obligation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual image of `Z(F)^0` consists of centralizer points. -/
theorem map_centralizerZero_le_centralizerPoints :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      centralizerPoints P.i := by
  rintro g ⟨z, _, rfl⟩
  exact map_mem_centralizerPoints P.centralizer.isRepresentedBy z

/-- The immediate inclusion in KP Lemma 7.4.3, valid for every subset. -/
theorem map_centralizerZero_le_centralizer_inf_parahoric (Ω : Set P.Apartment) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      centralizerPoints P.i ⊓ P.parahoric Ω :=
  le_inf P.map_centralizerZero_le_centralizerPoints
    (P.map_centralizerZero_le_parahoric Ω)

/-- The full intersection equality is equivalent to the sharp intersection
inclusion, using the actual centralizer-sharp product. -/
theorem centralizer_inf_parahoric_eq_iff (Ω : Set P.Apartment) :
    centralizerPoints P.i ⊓ P.parahoric Ω =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) ↔
      centralizerPoints P.i ⊓ P.sharpFixer Ω ≤
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  constructor
  · intro heq
    exact (inf_le_inf_left _ (P.sharpFixer_le_parahoric Ω)).trans heq.le
  · intro hsharp
    apply le_antisymm _ (P.map_centralizerZero_le_centralizer_inf_parahoric Ω)
    rintro g ⟨hgZ, hgP⟩
    obtain ⟨z, hz, h, hh, rfl⟩ := P.mem_parahoric_iff.mp hgP
    have hzZ := map_mem_centralizerPoints P.centralizer.isRepresentedBy z
    have hhZ : h ∈ centralizerPoints P.i := by
      have hm := (centralizerPoints P.i).mul_mem
        ((centralizerPoints P.i).inv_mem hzZ) hgZ
      simpa only [inv_mul_cancel_left] using hm
    exact Subgroup.mul_mem _ ⟨z, hz, rfl⟩ (hsharp ⟨hhZ, hh⟩)

/-- A sharp intersection inclusion at one point implies the corresponding
inclusion for every subset containing that point. -/
theorem centralizer_inf_sharpFixer_le_of_mem {Ω : Set P.Apartment}
    {x : P.Apartment} (hx : x ∈ Ω)
    (hsharp : centralizerPoints P.i ⊓ P.sharpFixer {x} ≤
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    centralizerPoints P.i ⊓ P.sharpFixer Ω ≤
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  (inf_le_inf_left _
    (P.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hx))).trans hsharp

/-- The exact published target is equivalent to proving only the singleton
sharp-centralizer inclusions under its unchanged apartment premise. -/
def CentralizerParahoricReductionStatement : Prop :=
  P.CentralizerParahoricIntersectionStatement ↔
    (P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ x : P.Apartment, centralizerPoints P.i ⊓ P.sharpFixer {x} ≤
        P.centralizerZero.map (rationalPoints.map P.centralizer.j))

/-- Algebraic and antitonicity reduction; it does not discharge the singleton
sharp-centralizer inclusions. -/
theorem centralizerParahoricReduction : P.CentralizerParahoricReductionStatement := by
  constructor
  · intro h hax x
    exact (P.centralizer_inf_parahoric_eq_iff {x}).mp
      (h hax {x} (Set.singleton_nonempty x))
  · intro h hax Ω hΩ
    apply (P.centralizer_inf_parahoric_eq_iff Ω).mpr
    obtain ⟨x, hx⟩ := hΩ
    exact P.centralizer_inf_sharpFixer_le_of_mem hx (h hax x)

end Langlands.Geometry.Building.ParahoricBuildingData

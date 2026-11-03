import Langlands.GroupScheme.ImageGenerationProducts
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Identifying a generated group from a dominant product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A factorization through a closed immersion descends along a schematically
 dominant precomposition, as a morphism over the original base. -/
theorem exists_over_factor_of_schematic_precomp
    {B : Scheme.{u}} {X Y Z W : Over B}
    (i : X ⟶ W) [IsClosedImmersion i.left]
    (p : Z ⟶ Y) [IsSchemeTheoreticallyDominant p.left]
    (g : Y ⟶ W) (h : Z ⟶ X) (he : p ≫ g = h ≫ i) :
    ∃ a : Y ⟶ X, a ≫ i = g := by
  have hker : i.left.ker ≤ g.left.ker := by
    have hh := h.left.le_ker_comp i.left
    have he' := congrArg Over.Hom.left he
    change p.left ≫ g.left = h.left ≫ i.left at he'
    rw [← he', Scheme.Hom.ker_comp, p.left.ker_eq_bot,
      Scheme.IdealSheafData.map_bot] at hh
    exact hh
  let a := IsClosedImmersion.lift i.left g.left hker
  have ha : a ≫ i.left = g.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
  rw [← i.w, ← Category.assoc, ha]
  exact g.w

variable {B : Scheme.{u}} {G H : GroupScheme B} {V : Over B} {f : V ⟶ G.X}

/-- A closed subgroup receiving `f` is its fixed envelope if an ordered product
 of the source is schematically dominant onto that subgroup. -/
theorem range_eq_closedImageEnvelope_of_schematic_power
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : V ⟶ H.X) (hg : g ≫ i.hom.hom = f) (n : ℕ)
    [IsSchemeTheoreticallyDominant (orderedPowerMap g n).left] :
    SubgroupFunctor.range i = closedImageEnvelope f := by
  apply le_antisymm
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro K j hj hfj
    obtain ⟨q, hq⟩ := hfj
    let : IsClosedImmersion j.hom.hom.left := hj
    have he : orderedPowerMap g n ≫ i.hom.hom = orderedPowerMap q n ≫ j.hom.hom := by
      rw [orderedPowerMap_comp, orderedPowerMap_comp, hg, hq]
    obtain ⟨a, ha⟩ := exists_over_factor_of_schematic_precomp
      j.hom.hom (orderedPowerMap g n) i.hom.hom (orderedPowerMap q n) he
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ a, by rw [Category.assoc, ha]⟩
  · exact closedImageEnvelope_le f i hi ⟨g, hg⟩

namespace GeneratedImage

/-- Construct an actual representative of the fixed envelope from a closed
 subgroup and a schematically dominant ordered product. -/
def ofSchematicPower (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : V ⟶ H.X) (hg : g ≫ i.hom.hom = f) (n : ℕ)
    [IsSchemeTheoreticallyDominant (orderedPowerMap g n).left] : GeneratedImage f := by
  letI : IsClosedImmersion i.hom.hom.left := hi
  exact
    { group := H
      inclusion := i
      closed := hi
      represents := ⟨Over.mono_of_mono_left _,
        range_eq_closedImageEnvelope_of_schematic_power i hi g hg n⟩ }

/-- Reducedness makes ordinary dominance sufficient; no separability of the
 source morphism or reducedness of competing closed subgroups is required. -/
def ofDominantPower (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : V ⟶ H.X) (hg : g ≫ i.hom.hom = f) (n : ℕ)
    [IsReduced H.X.left] [IsDominant (orderedPowerMap g n).left] : GeneratedImage f := by
  letI := IsSchemeTheoreticallyDominant.of_isDominant (orderedPowerMap g n).left
  exact ofSchematicPower i hi g hg n

/-- The canonical factor of the constructed representative is the given map. -/
theorem ofDominantPower_factor (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : V ⟶ H.X) (hg : g ≫ i.hom.hom = f) (n : ℕ)
    [IsReduced H.X.left] [IsDominant (orderedPowerMap g n).left] :
    (ofDominantPower i hi g hg n).factor = g := by
  exact ((ofDominantPower i hi g hg n).factor_unique g hg).symm

/-- The actual ordered products are preserved by the envelope identification. -/
theorem ofDominantPower_powerMap (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (g : V ⟶ H.X) (hg : g ≫ i.hom.hom = f) (n : ℕ)
    [IsReduced H.X.left] [IsDominant (orderedPowerMap g n).left] (m : ℕ) :
    (ofDominantPower i hi g hg n).powerMap m = orderedPowerMap g m := by
  rw [powerMap, ofDominantPower_factor]
  rfl

end GeneratedImage

end Langlands.GroupScheme

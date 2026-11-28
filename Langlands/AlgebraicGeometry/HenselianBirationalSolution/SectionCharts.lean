import Langlands.AlgebraicGeometry.HenselianBirationalSolution.GlueSeparated
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Generic
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Slice
import Langlands.AlgebraicGeometry.SmoothReducedBase

/-! # The scheme glued from the translates of `Y` by all sections

The charts are indexed by `Option (Sect g)`: the index `none` is `Y` itself and `some c` is the
left translate of `Y` by the section `c`. On the domain of the translation `τ_c` the chart of
index `some c` is the chart of index `none` composed with `τ_c` (`dom_chart`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

section OfSection

variable (hs : IsStrictDomain m) (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) {T : Scheme.{u}}

theorem Translation.ofSection_dom :
    (Translation.ofSection m hs c hc).dom = sectionPair c hc ⁻¹ᵁ m.domain := rfl

theorem Translation.ofSection_map :
    (Translation.ofSection m hs c hc).map = (sectionPair c hc ∣_ m.domain) ≫ m.mul := rfl

@[reassoc]
theorem sectionPair_comp (y : T ⟶ Y) :
    y ≫ sectionPair c hc = pullback.lift (y ≫ g ≫ c) y
      (by rw [Category.assoc, Category.assoc, hc, Category.comp_id]) := by
  apply pullback.hom_ext <;> simp

include hc in
theorem section_comp_g (y : T ⟶ Y) : (y ≫ g ≫ c) ≫ g = y ≫ g := by
  rw [Category.assoc, Category.assoc, hc, Category.comp_id]

theorem sectionPair_defined (a : T ⟶ (sectionPair c hc ⁻¹ᵁ m.domain).toScheme) :
    m.Defined ((a ≫ (sectionPair c hc ⁻¹ᵁ m.domain).ι) ≫ g ≫ c)
      (a ≫ (sectionPair c hc ⁻¹ᵁ m.domain).ι) (section_comp_g c hc _) := by
  rintro _ ⟨t, rfl⟩
  rw [← sectionPair_comp c hc, Scheme.Hom.comp_apply]
  exact (a t).2

theorem sectionPair_restrict_mul (a : T ⟶ (sectionPair c hc ⁻¹ᵁ m.domain).toScheme) :
    a ≫ (sectionPair c hc ∣_ m.domain) ≫ m.mul =
      m.mulPt ((a ≫ (sectionPair c hc ⁻¹ᵁ m.domain).ι) ≫ g ≫ c)
        (a ≫ (sectionPair c hc ⁻¹ᵁ m.domain).ι) (section_comp_g c hc _)
        (sectionPair_defined c hc a) := by
  rw [BirationalGroupLaw.mulPt, ← Category.assoc]
  congr 1
  apply m.liftDom_eq
  · rw [Category.assoc, morphismRestrict_ι_assoc, ← Category.assoc a, sectionPair_comp_assoc,
      pullback.lift_fst]
  · rw [Category.assoc, morphismRestrict_ι_assoc, ← Category.assoc a, sectionPair_comp_assoc,
      pullback.lift_snd]

/-- A point lies in the domain of the translation by `c` iff `(c, y)` lies in the domain. -/
theorem Translation.ofSection_defined (a : T ⟶ (Translation.ofSection m hs c hc).dom.toScheme) :
    m.Defined ((a ≫ (Translation.ofSection m hs c hc).dom.ι) ≫ g ≫ c)
      (a ≫ (Translation.ofSection m hs c hc).dom.ι) (section_comp_g c hc _) :=
  sectionPair_defined c hc a

theorem Translation.range_subset_ofSection_dom (y : T ⟶ Y)
    (hd : m.Defined (y ≫ g ≫ c) y (section_comp_g c hc y)) :
    Set.range y ⊆ (Translation.ofSection m hs c hc).dom := by
  rintro _ ⟨t, rfl⟩
  change sectionPair c hc (y t) ∈ m.domain
  rw [← Scheme.Hom.comp_apply, sectionPair_comp c hc]
  exact hd ⟨t, rfl⟩

/-- The translation by `c` on points: `τ_c y = c y`. -/
theorem Translation.ofSection_map_eq (a : T ⟶ (Translation.ofSection m hs c hc).dom.toScheme) :
    a ≫ (Translation.ofSection m hs c hc).map =
      m.mulPt ((a ≫ (Translation.ofSection m hs c hc).dom.ι) ≫ g ≫ c)
        (a ≫ (Translation.ofSection m hs c hc).dom.ι) (section_comp_g c hc _)
        (Translation.ofSection_defined hs c hc a) :=
  sectionPair_restrict_mul c hc a

end OfSection

variable (H : GlueHyp m)

/-- The family of translations: the identity and the translations by all sections. -/
def secTrans : Option (Sect g) → Translation m
  | none => Translation.id
  | some c => Translation.ofSection m H.strict c.1 c.2

section SecTrans

variable {T : Scheme.{u}} (c : Sect g)

theorem secTrans_defined (a : T ⟶ (secTrans H (some c)).dom.toScheme) :
    m.Defined ((a ≫ (secTrans H (some c)).dom.ι) ≫ g ≫ c.1)
      (a ≫ (secTrans H (some c)).dom.ι) (section_comp_g c.1 c.2 _) :=
  Translation.ofSection_defined H.strict c.1 c.2 a

theorem secTrans_map_eq (a : T ⟶ (secTrans H (some c)).dom.toScheme) :
    a ≫ (secTrans H (some c)).map =
      m.mulPt ((a ≫ (secTrans H (some c)).dom.ι) ≫ g ≫ c.1)
        (a ≫ (secTrans H (some c)).dom.ι) (section_comp_g c.1 c.2 _)
        (secTrans_defined H c a) :=
  Translation.ofSection_map_eq H.strict c.1 c.2 a

theorem range_subset_secTrans_dom (y : T ⟶ Y)
    (hd : m.Defined (y ≫ g ≫ c.1) y (section_comp_g c.1 c.2 y)) :
    Set.range y ⊆ (secTrans H (some c)).dom :=
  Translation.range_subset_ofSection_dom H.strict c.1 c.2 y hd

end SecTrans

variable [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g]

/-- The glued scheme. -/
abbrev Gl : Scheme.{u} := Glue.glued H (secTrans H)

/-- The chart of index `i`. -/
abbrev ch (i : Option (Sect g)) : Y ⟶ Gl H := Glue.chart H (secTrans H) i

/-- The structure morphism of the glued scheme. -/
abbrev toS : Gl H ⟶ S := Glue.toBase H (secTrans H)

theorem ch_toS (i : Option (Sect g)) : ch H i ≫ toS H = g := Glue.chart_toBase H _ i

/-- On the overlap of `τ_i` and `τ_k`, the chart `i` is the chart `k` composed with
`τ_k⁻¹ ∘ τ_i`. -/
theorem overlap_chart {ι : Type u} (τ : ι → Translation m) (i k : ι) :
    (Translation.overlap (τ i) (τ k)).ι ≫ Glue.chart H τ i =
      Translation.trans (τ i) (τ k) ≫ Glue.chart H τ k := by
  rw [← Scheme.homOfLE_ι Y (Translation.overlap_le_chartOverlap (τ i) (τ k) H), Category.assoc,
    ← Glue.ψ_chart, ← Category.assoc, Translation.homOfLE_chartTrans]

/-- **Chart relation.** On the domain of `τ_i`, the chart `i` is the chart `none` composed with
`τ_i`. -/
theorem dom_chart {T : Scheme.{u}} (i : Option (Sect g))
    (a : T ⟶ (secTrans H i).dom.toScheme) :
    (a ≫ (secTrans H i).dom.ι) ≫ ch H i = (a ≫ (secTrans H i).map) ≫ ch H none := by
  have hr : Set.range (a ≫ (secTrans H i).dom.ι) ⊆
      Set.range (Translation.overlap (secTrans H i) (secTrans H none)).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨a t, by simp [secTrans, Translation.id]; trivial, rfl⟩
  set b := IsOpenImmersion.lift _ _ hr
  have hb : b ≫ (Translation.overlap (secTrans H i) (secTrans H none)).ι =
      a ≫ (secTrans H i).dom.ι := IsOpenImmersion.lift_fac _ _ _
  have hba : b ≫ Translation.overlapIncl (secTrans H i) (secTrans H none) = a := by
    rw [← cancel_mono (secTrans H i).dom.ι, Category.assoc, Scheme.homOfLE_ι, hb]
  have htr : Translation.trans (secTrans H i) (secTrans H none) =
      Translation.overlapIncl (secTrans H i) (secTrans H none) ≫ (secTrans H i).map :=
    Translation.trans_map (secTrans H i) (secTrans H none)
  rw [← hb, Category.assoc, overlap_chart H (secTrans H) i none, ← Category.assoc, htr,
    ← Category.assoc, hba]

/-- The chart `none` composed with the translation by `c`, on points. -/
theorem dom_chart_some {T : Scheme.{u}} (c : Sect g)
    (a : T ⟶ (secTrans H (some c)).dom.toScheme) :
    (a ≫ (secTrans H (some c)).dom.ι) ≫ ch H (some c) =
      m.mulPt ((a ≫ (secTrans H (some c)).dom.ι) ≫ g ≫ c.1)
        (a ≫ (secTrans H (some c)).dom.ι) (section_comp_g c.1 c.2 _)
        (Translation.ofSection_defined H.strict c.1 c.2 a) ≫ ch H none := by
  rw [dom_chart]
  exact congrArg (· ≫ ch H none) (Translation.ofSection_map_eq H.strict c.1 c.2 a)

end Langlands.AlgebraicGeometry.HenselianBirationalSolution

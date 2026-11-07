import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Maps.Basic

/-! # Compatible open subdiagrams of colimits -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u v w

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TypeColimit

variable {J : Type v} [Category.{w} J]
variable {F G : J ⥤ Type u} (τ : F ⟶ G)
variable {cF : Cocone F} {cG : Cocone G}

/-- Extend the component map into a subdiagram's cocone by `none` off its range. -/
def partialSection (cF : Cocone F) (j : J) (y : G.obj j) : Option cF.pt := by
  classical
  exact if hy : y ∈ Set.range (τ.app j) then
    some (cF.ι.app j (Classical.choose hy)) else none

lemma partialSection_app (hinj : ∀ j, Function.Injective (τ.app j))
    (j : J) (x : F.obj j) :
    partialSection τ cF j (τ.app j x) = some (cF.ι.app j x) := by
  dsimp [partialSection]
  rw [dite_eq_left (Set.mem_range_self x)]
  congr 2
  exact hinj j (Classical.choose_spec
    (show ∃ z, τ.app j z = τ.app j x from ⟨x, rfl⟩))

/-- A cartesian subdiagram embeds in the colimit and has the expected saturated range. -/
lemma injective_and_range (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j, cF.ι.app j ≫ q = τ.app j ≫ cG.ι.app j)
    (hinj : ∀ j, Function.Injective (τ.app j))
    (hcart : ∀ {j k} (f : j ⟶ k),
      G.map f ⁻¹' Set.range (τ.app k) = Set.range (τ.app j)) :
    Function.Injective q ∧ ∀ j, Set.range (τ.app j) =
      cG.ι.app j ⁻¹' Set.range q := by
  let δ : G ⟶ (Functor.const J).obj (Option cF.pt) :=
    { app := fun j => ↾(partialSection τ cF j)
      naturality := fun {j k} f => by
        ext y
        change partialSection τ cF k (G.map f y) = partialSection τ cF j y
        by_cases hy : y ∈ Set.range (τ.app j)
        · rcases hy with ⟨x, rfl⟩
          have hn : G.map f (τ.app j x) = τ.app k (F.map f x) :=
            (ConcreteCategory.congr_hom (τ.naturality f) x).symm
          rw [hn, partialSection_app τ hinj, partialSection_app τ hinj]
          exact congrArg some (ConcreteCategory.congr_hom (cF.w f) x)
        · have hk : G.map f y ∉ Set.range (τ.app k) := by
            intro hk
            apply hy
            rw [← hcart f]
            exact hk
          simp only [partialSection, dite_eq_right hy, dite_eq_right hk] }
  let d : Cocone G := ⟨Option cF.pt, δ⟩
  let r : cG.pt ⟶ Option cF.pt := hcG.desc d
  have hrj (j : J) (y : G.obj j) : r (cG.ι.app j y) = partialSection τ cF j y :=
    ConcreteCategory.congr_hom (hcG.fac d j) y
  have hr (x : cF.pt) : r (q x) = some x := by
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hcF x
    have hw := ConcreteCategory.congr_hom (hq j) y
    change q (cF.ι.app j y) = cG.ι.app j (τ.app j y) at hw
    rw [hw, hrj, partialSection_app τ hinj]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply Option.some.inj
    rw [← hr x, ← hr y, hxy]
  · intro j
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨cF.ι.app j x, ConcreteCategory.congr_hom (hq j) x⟩
    · rintro ⟨x, hx⟩
      by_contra hy
      have hh := congrArg r hx
      rw [hr, hrj] at hh
      simp only [partialSection, dite_eq_right hy] at hh
      contradiction

end TypeColimit

namespace TopologicalColimit

variable {J : Type v} [Category.{w} J]
variable {F G : J ⥤ TopCat.{u}} (τ : F ⟶ G)
variable {cF : Cocone F} {cG : Cocone G}

/-- Saturation and componentwise openness detect an open embedding into a colimit. -/
lemma isOpenEmbedding_of_injective_of_range (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j, cF.ι.app j ≫ q = τ.app j ≫ cG.ι.app j)
    (hinj : Function.Injective q)
    (hopen : ∀ j, IsOpenEmbedding (τ.app j))
    (hrange : ∀ j, Set.range (τ.app j) = cG.ι.app j ⁻¹' Set.range q) :
    IsOpenEmbedding q := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨q.hom.continuous, hinj, ?_⟩
  intro S hS
  rw [TopCat.isOpen_iff_of_isColimit cG hcG]
  intro j
  have hw (x : F.obj j) : q (cF.ι.app j x) = cG.ι.app j (τ.app j x) :=
    ConcreteCategory.congr_hom (hq j) x
  have he : cG.ι.app j ⁻¹' (q '' S) = τ.app j '' (cF.ι.app j ⁻¹' S) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hy : y ∈ Set.range (τ.app j) := by
        rw [hrange j]
        exact ⟨x, hxy⟩
      rcases hy with ⟨z, rfl⟩
      refine ⟨z, ?_, rfl⟩
      have hz : cF.ι.app j z = x := hinj ((hw z).trans hxy.symm)
      change cF.ι.app j z ∈ S
      rw [hz]
      exact hx
    · rintro ⟨z, hz, rfl⟩
      exact ⟨cF.ι.app j z, hz, hw z⟩
  rw [he]
  exact (hopen j).isOpenMap _ (hS.preimage (cF.ι.app j).hom.continuous)

/-- A cartesian open subdiagram induces an open embedding on topological colimits. -/
lemma isOpenEmbedding_of_cartesian (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j, cF.ι.app j ≫ q = τ.app j ≫ cG.ι.app j)
    (hopen : ∀ j, IsOpenEmbedding (τ.app j))
    (hcart : ∀ {j k} (f : j ⟶ k),
      G.map f ⁻¹' Set.range (τ.app k) = Set.range (τ.app j)) :
    IsOpenEmbedding q ∧ ∀ j, Set.range (τ.app j) =
      cG.ι.app j ⁻¹' Set.range q := by
  obtain ⟨hinj, hrange⟩ := TypeColimit.injective_and_range
    (Functor.whiskerRight τ (forget TopCat))
    (isColimitOfPreserves (forget TopCat) hcF)
    (isColimitOfPreserves (forget TopCat) hcG)
    ((forget TopCat).map q)
    (fun j => (forget TopCat).congr_map (hq j))
    (fun j => (hopen j).injective) hcart
  exact ⟨isOpenEmbedding_of_injective_of_range τ hcG q hq hinj hopen hrange, hrange⟩

end TopologicalColimit

end Langlands.AlgebraicGeometry.IntegralSchemePushout

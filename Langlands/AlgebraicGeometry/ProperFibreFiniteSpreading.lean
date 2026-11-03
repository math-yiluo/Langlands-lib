import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Spreading finiteness from one fibre of a proper family -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- An open containing a whole fibre of a universally closed morphism contains
the inverse image of an affine neighbourhood of the base point. -/
theorem exists_affine_baseOpen_preimage_le
    {X S : Scheme.{u}} (p : X ⟶ S) [UniversallyClosed p]
    (s : S) (U : X.Opens) (hU : ∀ x : X, p x = s → x ∈ U) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧ p ⁻¹ᵁ V ≤ U := by
  let W : S.Opens :=
    ⟨(p '' (U : Set X)ᶜ)ᶜ, (p.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  have hsW : s ∈ W := by
    rintro ⟨x, hx, hxs⟩
    exact hx (hU x hxs)
  obtain ⟨V, hV, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset hsW
  refine ⟨V, hsV, hV, fun x hx ↦ ?_⟩
  by_contra hxU
  exact hVW hx ⟨x, hxU, rfl⟩

/-- A morphism in a proper family is finite near a base point if it is
quasi-finite at every point above that base point. -/
theorem exists_isFinite_morphismRestrict_of_quasiFiniteAt_fibre
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsProper (f ≫ g)] [IsSeparated g] (s : S)
    (h : ∀ x : X, (f ≫ g) x = s → f.QuasiFiniteAt x) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧ IsFinite (f ∣_ (g ⁻¹ᵁ V)) := by
  have : IsProper f := .of_comp f g
  obtain ⟨V, hsV, hV, hVU⟩ :=
    exists_affine_baseOpen_preimage_le (f ≫ g) s f.quasiFiniteLocus h
  refine ⟨V, hsV, hV, ?_⟩
  suffices LocallyQuasiFinite (f ∣_ (g ⁻¹ᵁ V)) from
    IsFinite.of_isProper_of_locallyQuasiFinite _
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  apply top_unique
  intro x _
  have hx : f.QuasiFiniteAt ((f ⁻¹ᵁ (g ⁻¹ᵁ V)).ι x) := hVU x.2
  rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
    ← morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff] at hx
  exact hx

/-- The morphism between scheme-theoretic fibres induced by a morphism over
the base. -/
def baseFibreMap {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    (f ≫ g).fiber s ⟶ g.fiber s :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem baseFibreMap_fiberι {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    baseFibreMap f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f := by
  simp [baseFibreMap, Scheme.Hom.fiberι]

/-- Finite fibres of the induced fibre map give finite fibres of the original
morphism at points lying above the specified base point. -/
theorem finite_preimage_singleton_of_baseFibreMap
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
    [LocallyQuasiFinite (baseFibreMap f g s)] [QuasiCompact (baseFibreMap f g s)]
    (y : Y) (hy : g y = s) :
    (f ⁻¹' {y}).Finite := by
  let z : g.fiber s := (g.fiberHomeo s).symm ⟨y, hy⟩
  have hz : g.fiberι s z = y := g.fiberι_fiberHomeo_symm s ⟨y, hy⟩
  apply ((baseFibreMap f g s).finite_preimage_singleton z).image
    ((f ≫ g).fiberι s) |>.subset
  intro x hx
  have hxs : (f ≫ g) x = s := by
    change g (f x) = s
    rw [Set.mem_singleton_iff.mp hx, hy]
  let a : (f ≫ g).fiber s := ((f ≫ g).fiberHomeo s).symm ⟨x, hxs⟩
  have ha : (f ≫ g).fiberι s a = x :=
    (f ≫ g).fiberι_fiberHomeo_symm s ⟨x, hxs⟩
  refine ⟨a, ?_, ha⟩
  apply (g.fiberι s).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, baseFibreMap_fiberι, Scheme.Hom.comp_apply, ha, hz]
  exact hx

/-- A finite induced fibre map in a proper family spreads to a finite morphism
over an affine neighbourhood of the base point. -/
theorem exists_isFinite_morphismRestrict_of_finite_baseFibreMap
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsProper (f ≫ g)] [IsSeparated g] (s : S)
    [IsFinite (baseFibreMap f g s)] :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧ IsFinite (f ∣_ (g ⁻¹ᵁ V)) := by
  have : IsProper f := .of_comp f g
  apply exists_isFinite_morphismRestrict_of_quasiFiniteAt_fibre f g s
  intro x hx
  have hf : (f ⁻¹' {f x}).Finite :=
    finite_preimage_singleton_of_baseFibreMap f g s (f x) hx
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr hf
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

end Langlands.AlgebraicGeometry

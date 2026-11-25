/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse

/-! # Flatness and ordinary identity self braiding of an etale line

Source: blueprint latest, second triangle even-shift computation.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
suppress_compilation
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
variable (A : Type (u + 1)) [CommRing A]
private lemma self_braiding_of_iso {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {X Z : C} (e : X ≅ Z) (h : (β_ Z Z).hom = 𝟙 _) :
    (β_ X X).hom = 𝟙 _ := by
  have : IsIso (e.hom ⊗ₘ e.hom) := inferInstance
  apply (cancel_mono (e.hom ⊗ₘ e.hom)).1
  simpa only [BraidedCategory.braiding_naturality, h, Category.comp_id,
    Category.id_comp] using BraidedCategory.braiding_naturality e.hom e.hom |>.symm

private lemma self_braiding_of_unit {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {X : C} (e : X ≅ 𝟙_ C) : (β_ X X).hom = 𝟙 _ := by
  apply self_braiding_of_iso e
  rw [braiding_tensorUnit_right]
  monoidal

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
private lemma line_trivializations {Y : Scheme.{u}}
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) :
    ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
      ∀ i, Nonempty ((upperStar (ModuleCat.{u + 1} A) (U.f i)).obj J ≅ 𝟙_ _) := by
  obtain ⟨U, hU⟩ := hJ
  refine ⟨U, fun i ↦ (hU i).map fun e ↦ e ≪≫ ?_⟩
  exact Iso.refl _

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- Flatness and ordinary identity self braiding of an etale line.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle.
(auxiliary; not a blueprint node).

Proof: The etale trivializing cover supplies isomorphisms to the tensor unit. The existing
tensorInverseOfUpperStarIso constructs the internal-dual tensor inverse, so flat_of_tensorIso
gives flatness.
Upper-star functors of this cover preserve equalizers and jointly reflect isomorphisms, hence are
jointly faithful on ordinary sheaf morphisms. Transport braiding through the monoidal adjunction,
and use braiding naturality along the local unit isomorphisms. The self braiding of the unit is
identity by unitor coherence. Cancel the invertible tensor comparisons and apply joint
faithfulness. -/
theorem etaleLineFlatAndBraiding {Y : Scheme.{u}}
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) :
    ObjectProperty.flat J ∧ (β_ J J).hom = 𝟙 _ := by
  classical
  obtain ⟨U, hU⟩ := line_trivializations A J hJ
  have : ∀ i, Etale (U.f i) := U.map_prop
  have hc : ⋃ i, Set.range (U.f i).base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := U.exists_eq x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  let e := tensorInverseOfUpperStarIso (ModuleCat.{u + 1} A) U.f hc J
    (fun i ↦ (hU i).some)
  refine ⟨ObjectProperty.flat_of_tensorIso e.rightIso, ?_⟩
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} A) (U.f i)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N f h
    exact isIso_of_isIso_upperStar_map_of_cover U f h
  apply hf.map_injective
  intro i
  let F := upperStar (ModuleCat.{u + 1} A) (U.f i)
  apply (cancel_mono (Functor.OplaxMonoidal.δ F J J)).1
  rw [Adjunction.map_braiding_comp_δ
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (U.f i))]
  rw [self_braiding_of_unit (hU i).some]
  simp only [Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Etale.CoordinateTrace

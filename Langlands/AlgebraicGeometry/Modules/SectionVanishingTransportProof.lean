import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportStatement
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Langlands.AlgebraicGeometry.Modules.MorphismVanishing

/-! # Zero tests and transport of actual pulled-back sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X Y Z : Scheme.{u}}

/-- The section morphism is zero exactly when the section is zero. -/
lemma sectionHom_eq_zero_iff (M : X.Modules) (s : GlobalSections M) :
    sectionHom M s = 0 ↔ s = 0 := by
  rw [structureModule_hom_eq_zero_iff, sectionHom_app_one]
  change M.presheaf.map (𝟙 _) s = 0 ↔ s = 0
  simp

/-- Zero of the actual pulled-back section can be tested on its pulled-back morphism. -/
lemma pullbackSection_eq_zero_iff (f : Y ⟶ X) (M : X.Modules) (s : GlobalSections M) :
    pullbackSection f M s = 0 ↔
      (Scheme.Modules.pullback f).map (sectionHom M s) = 0 := by
  change (pullbackSectionHom f M s).app ⊤ (1 : Γ(Y, ⊤)) = 0 ↔ _
  rw [← structureModule_hom_eq_zero_iff]
  exact comp_eq_zero_iff_of_epi (Langlands.Scheme.Modules.pullbackUnitIso f).inv

/-- Successive pullbacks and composite pullback have the same zero condition. -/
lemma pullbackSection_comp_eq_zero_iff (f : Z ⟶ Y) (g : Y ⟶ X)
    (M : X.Modules) (s : GlobalSections M) :
    pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s) = 0 ↔
      pullbackSection (f ≫ g) M s = 0 := by
  rw [pullbackSection_eq_zero_iff, sectionHom_pullbackSection, pullbackSectionHom,
    Functor.map_comp, comp_eq_zero_iff_of_epi, pullback_map_comp_eq_zero_iff,
    ← pullbackSection_eq_zero_iff]

/-- Pullback along an isomorphism of schemes preserves and reflects zero of a section. -/
lemma pullbackSection_iso_eq_zero_iff (f : Y ⟶ X) [IsIso f]
    (M : X.Modules) (s : GlobalSections M) :
    pullbackSection f M s = 0 ↔ s = 0 := by
  rw [pullbackSection_eq_zero_iff, pullback_map_iso_eq_zero_iff, sectionHom_eq_zero_iff]

/-- Pulling back a section commutes with an actual module-sheaf morphism. -/
lemma pullbackSection_naturality (f : Y ⟶ X) {M N : X.Modules}
    (φ : M ⟶ N) (s : GlobalSections M) :
    pullbackSection f N (φ.app ⊤ s) =
      ((Scheme.Modules.pullback f).map φ).app ⊤ (pullbackSection f M s) := by
  apply sectionHom_injective
  rw [sectionHom_pullbackSection, sectionHom_naturality, sectionHom_pullbackSection]
  simp only [pullbackSectionHom, sectionHom_naturality, Functor.map_comp, Category.assoc]

/-- A module-sheaf isomorphism preserves and reflects zero after any pullback. -/
lemma pullbackSection_mapIso_eq_zero_iff (f : Y ⟶ X) {M N : X.Modules}
    (e : M ≅ N) (s : GlobalSections M) :
    pullbackSection f N (e.hom.app ⊤ s) = 0 ↔ pullbackSection f M s = 0 := by
  rw [pullbackSection_eq_zero_iff, pullbackSection_eq_zero_iff, sectionHom_naturality,
    Functor.map_comp, comp_eq_zero_iff_of_mono]

/-- The six actual-section zero and naturality assertions, with no geometric hypotheses. -/
theorem sectionVanishingTransport : SectionVanishingTransportStatement.{u} :=
  ⟨fun _ M s ↦ sectionHom_eq_zero_iff M s,
    fun _ _ f M s ↦ pullbackSection_eq_zero_iff f M s,
    fun _ _ _ f g M s ↦ pullbackSection_comp_eq_zero_iff f g M s,
    fun _ _ f _ M s ↦ pullbackSection_iso_eq_zero_iff f M s,
    fun _ _ f _ _ φ s ↦ pullbackSection_naturality f φ s,
    fun _ _ f _ _ e s ↦ pullbackSection_mapIso_eq_zero_iff f e s⟩

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

variable {X Y Z : Scheme.{u}} {L M : LineBundle X}

/-- Vanishing of a pulled-back line-bundle section is vanishing along the composite. -/
lemma vanishesAlong_pullback_iff (f : Z ⟶ Y) (g : Y ⟶ X) (L : LineBundle X)
    (s : GlobalSections L.obj) :
    VanishesAlong ((LineBundle.pullback g).obj L) f (pullbackSection g L.obj s) ↔
      VanishesAlong L (f ≫ g) s :=
  pullbackSection_comp_eq_zero_iff f g L.obj s

/-- Vanishing along any morphism is preserved and reflected by a sheaf isomorphism. -/
lemma vanishesAlong_mapIso_iff (e : L.obj ≅ M.obj) (f : Y ⟶ X)
    (s : GlobalSections L.obj) :
    VanishesAlong M f (e.hom.app ⊤ s) ↔ VanishesAlong L f s :=
  pullbackSection_mapIso_eq_zero_iff f e s

/-- A scheme isomorphism reflects zero of a section in the vanishing predicate. -/
lemma vanishesAlong_iso_iff (f : Y ⟶ X) [IsIso f] (L : LineBundle X)
    (s : GlobalSections L.obj) : VanishesAlong L f s ↔ s = 0 :=
  pullbackSection_iso_eq_zero_iff f L.obj s

/-- An isomorphism of underlying sheaves transports separation of points and tangents. -/
lemma SeparatesPointsAndTangents.of_iso {K : Type u} [Field K]
    {p : X ⟶ Spec (CommRingCat.of K)} (h : SeparatesPointsAndTangents p L)
    (e : L.obj ≅ M.obj) : SeparatesPointsAndTangents p M := by
  rcases h with ⟨hb, hp, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs⟩ := hb x hx
    exact ⟨e.hom.app ⊤ s, (not_congr (vanishesAlong_mapIso_iff e x s)).mpr hs⟩
  · intro x y hx hy hxy
    obtain ⟨s, hs, hs'⟩ := hp x y hx hy hxy
    exact ⟨e.hom.app ⊤ s, (vanishesAlong_mapIso_iff e x s).mpr hs,
      (not_congr (vanishesAlong_mapIso_iff e y s)).mpr hs'⟩
  · intro x hx t ht'
    obtain ⟨s, hs, hs'⟩ := ht x hx t ht'
    exact ⟨e.hom.app ⊤ s, (vanishesAlong_mapIso_iff e x s).mpr hs,
      (not_congr (vanishesAlong_mapIso_iff e t s)).mpr hs'⟩

end Langlands.AlgebraicGeometry.Picard

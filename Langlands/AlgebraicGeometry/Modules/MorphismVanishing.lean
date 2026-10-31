import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Zero tests for module-sheaf morphisms and their pullbacks

These lemmas are the shared helpers from `ResidueLocalChartProof`.
-/

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

lemma structureModule_hom_eq_zero_iff {X : Scheme.{u}} {M : X.Modules}
    (φ : structureModule X ⟶ M) :
    φ = 0 ↔ φ.app ⊤ (1 : Γ(X, ⊤)) = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    change Γ(X, U) at a
    have hn := ConcreteCategory.congr_hom
      (φ.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
      (1 : Γ(X, ⊤))
    change φ.app U (X.presheaf.map _ (1 : Γ(X, ⊤))) = M.presheaf.map _ (φ.app ⊤ (1 : Γ(X, ⊤))) at hn
    rw [map_one, h, map_zero] at hn
    have hs := φ.app_smul a (1 : Γ(X, U))
    change φ.app U (a * (1 : Γ(X, U))) = a • φ.app U (1 : Γ(X, U)) at hs
    simpa only [mul_one, hn, smul_zero, Scheme.Modules.Hom.zero_app,
      AddCommGrpCat.zero_apply] using hs

lemma map_eq_zero_iff_of_natIso {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G) {A B : C} (φ : A ⟶ B) :
    F.map φ = 0 ↔ G.map φ = 0 := by
  rw [← comp_eq_zero_iff_of_mono (e.hom.app B), e.hom.naturality,
    comp_eq_zero_iff_of_epi]

lemma pullback_map_comp_eq_zero_iff {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) = 0 ↔
      (Scheme.Modules.pullback (f ≫ g)).map φ = 0 :=
  map_eq_zero_iff_of_natIso (Scheme.Modules.pullbackComp f g) φ

lemma pullback_map_iso_eq_zero_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    have h' : (Scheme.Modules.pullback (inv f)).map
        ((Scheme.Modules.pullback f).map φ) = 0 := by rw [h, Functor.map_zero]
    rw [pullback_map_comp_eq_zero_iff, IsIso.inv_hom_id] at h'
    exact (map_eq_zero_iff_of_natIso (Scheme.Modules.pullbackId Y) φ).mp h'
  · rintro rfl
    simp only [Functor.map_zero]

end Langlands.SchemeModule

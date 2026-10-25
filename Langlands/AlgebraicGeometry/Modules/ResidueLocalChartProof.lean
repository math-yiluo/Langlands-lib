import Langlands.AlgebraicGeometry.Modules.ResidueLocalChartStatement
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Mathlib.CategoryTheory.Adjunction.Additive

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

private lemma unit_hom_eq_zero_iff {X : Scheme.{u}} {M : X.Modules}
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

private lemma natIso_map_eq_zero_iff {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G) {A B : C} (φ : A ⟶ B) :
    F.map φ = 0 ↔ G.map φ = 0 := by
  rw [← comp_eq_zero_iff_of_mono (e.hom.app B), e.hom.naturality,
    comp_eq_zero_iff_of_epi]

private lemma pullback_comp_eq_zero_iff {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) = 0 ↔
      (Scheme.Modules.pullback (f ≫ g)).map φ = 0 :=
  natIso_map_eq_zero_iff (Scheme.Modules.pullbackComp f g) φ

private lemma pullback_iso_eq_zero_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    have h' : (Scheme.Modules.pullback (inv f)).map
        ((Scheme.Modules.pullback f).map φ) = 0 := by rw [h, Functor.map_zero]
    rw [pullback_comp_eq_zero_iff, IsIso.inv_hom_id] at h'
    exact (natIso_map_eq_zero_iff (Scheme.Modules.pullbackId Y) φ).mp h'
  · rintro rfl
    simp only [Functor.map_zero]

private lemma nonvanishing_iff_pullback_ne_zero {X : Scheme.{u}}
    (M : X.Modules) (s : GlobalSections M) (x : X) :
    NonvanishingAt M s x ↔
      (Scheme.Modules.pullback (X.fromSpecResidueField x)).map (sectionHom M s) ≠ 0 := by
  change (pullbackSectionHom (X.fromSpecResidueField x) M s).app ⊤
    (1 : Γ(Spec (X.residueField x), ⊤)) ≠ 0 ↔ _
  exact (not_congr (unit_hom_eq_zero_iff
    (pullbackSectionHom (X.fromSpecResidueField x) M s))).symm.trans
      (not_congr (comp_eq_zero_iff_of_epi
        (Langlands.Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField x)).inv))

private lemma pullback_scalar_eq_zero_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    (φ : structureModule X ⟶ structureModule X) :
    (Scheme.Modules.pullback f).map φ = 0 ↔
      f.appTop (φ.app ⊤ (1 : Γ(X, ⊤))) = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  rw [← comp_eq_zero_iff_of_mono (Langlands.Scheme.Modules.pullbackUnitIso f).hom]
  rw [← adj.homEquiv _ _ |>.injective.eq_iff]
  dsimp only [adj]
  erw [Adjunction.homEquiv_naturality_left,
    Langlands.Scheme.Modules.pullbackUnitAdjunction Y X f,
    Adjunction.homAddEquiv_zero, unit_hom_eq_zero_iff]
  rfl

private lemma residue_appTop {X : Scheme.{u}} (x : X) :
    (X.fromSpecResidueField x).appTop =
      X.Γevaluation x ≫ (Scheme.ΓSpecIso (X.residueField x)).inv := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  rw [show (homOfLE le_top : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ ⊤) = 𝟙 _ from rfl]
  simp only [op_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.assoc]
  erw [← Scheme.ΓSpecIso_inv_naturality (X.residue x)]
  rfl

private lemma pullback_residue_scalar_eq_zero_iff {X : Scheme.{u}}
    (φ : structureModule X ⟶ structureModule X) (x : X) :
    (Scheme.Modules.pullback (X.fromSpecResidueField x)).map φ = 0 ↔
      X.Γevaluation x (φ.app ⊤ (1 : Γ(X, ⊤))) = 0 := by
  rw [pullback_scalar_eq_zero_iff, residue_appTop]
  change (Scheme.ΓSpecIso (X.residueField x)).inv
    (X.Γevaluation x (φ.app ⊤ (1 : Γ(X, ⊤)))) = 0 ↔ _
  exact (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (X.residueField x)).inv).injective.eq_iff' (map_zero _)

private lemma residue_restrict_eq_zero_iff {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsOpenImmersion i] (x : Y) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback (X.fromSpecResidueField (i x))).map φ = 0 ↔
      (Scheme.Modules.pullback (Y.fromSpecResidueField x)).map
        ((Scheme.Modules.restrictFunctor i).map φ) = 0 := by
  let k := Spec.map (i.residueFieldMap x)
  calc
    _ ↔ (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullback (X.fromSpecResidueField (i x))).map φ) = 0 :=
      (pullback_iso_eq_zero_iff k _).symm
    _ ↔ (Scheme.Modules.pullback (k ≫ X.fromSpecResidueField (i x))).map φ = 0 :=
      pullback_comp_eq_zero_iff _ _ _
    _ ↔ (Scheme.Modules.pullback (Y.fromSpecResidueField x)).map
        ((Scheme.Modules.pullback i).map φ) = 0 := by
      rw [show k ≫ X.fromSpecResidueField (i x) = Y.fromSpecResidueField x ≫ i from
        i.SpecMap_residueFieldMap_fromSpecResidueField x]
      exact (pullback_comp_eq_zero_iff _ _ _).symm
    _ ↔ _ := (natIso_map_eq_zero_iff
      (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback i)
        (Scheme.Modules.pullback (Y.fromSpecResidueField x))) φ).symm

/-- The actual residue section is nonzero exactly when its scalar in a local
rank-one chart has nonzero residue. -/
theorem residueLocalChartCriterion : ResidueLocalChartCriterion.{u} := by
  intro X M s U x e
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s) ≫ e.hom
  change NonvanishingAt M s (U.ι x) ↔
    U.toScheme.Γevaluation x (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) ≠ 0
  rw [nonvanishing_iff_pullback_ne_zero]
  apply not_congr
  calc
    _ ↔ (Scheme.Modules.pullback (U.toScheme.fromSpecResidueField x)).map
        ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s)) = 0 :=
      residue_restrict_eq_zero_iff _ _ _
    _ ↔ (Scheme.Modules.pullback (U.toScheme.fromSpecResidueField x)).map ψ = 0 := by
      dsimp only [ψ]
      rw [Functor.map_comp, Functor.map_comp, comp_eq_zero_iff_of_epi,
        comp_eq_zero_iff_of_mono]
    _ ↔ _ := pullback_residue_scalar_eq_zero_iff ψ x

end Langlands.SchemeModule

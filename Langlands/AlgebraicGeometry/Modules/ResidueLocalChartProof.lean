import Langlands.AlgebraicGeometry.Modules.ResidueLocalChartStatement
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.Modules.MorphismVanishing

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

private lemma nonvanishing_iff_pullback_ne_zero {X : Scheme.{u}}
    (M : X.Modules) (s : GlobalSections M) (x : X) :
    NonvanishingAt M s x ↔
      (Scheme.Modules.pullback (X.fromSpecResidueField x)).map (sectionHom M s) ≠ 0 := by
  change (pullbackSectionHom (X.fromSpecResidueField x) M s).app ⊤
    (1 : Γ(Spec (X.residueField x), ⊤)) ≠ 0 ↔ _
  exact (not_congr (structureModule_hom_eq_zero_iff
    (pullbackSectionHom (X.fromSpecResidueField x) M s))).symm.trans
      (not_congr (comp_eq_zero_iff_of_epi
        (Langlands.Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField x)).inv))

lemma pullback_scalar_eq_zero_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    (φ : structureModule X ⟶ structureModule X) :
    (Scheme.Modules.pullback f).map φ = 0 ↔
      f.appTop (φ.app ⊤ (1 : Γ(X, ⊤))) = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  rw [← comp_eq_zero_iff_of_mono (Langlands.Scheme.Modules.pullbackUnitIso f).hom]
  rw [← adj.homEquiv _ _ |>.injective.eq_iff]
  dsimp only [adj]
  erw [Adjunction.homEquiv_naturality_left,
    Langlands.Scheme.Modules.pullbackUnitAdjunction Y X f,
    Adjunction.homAddEquiv_zero, structureModule_hom_eq_zero_iff]
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
      (pullback_map_iso_eq_zero_iff k _).symm
    _ ↔ (Scheme.Modules.pullback (k ≫ X.fromSpecResidueField (i x))).map φ = 0 :=
      pullback_map_comp_eq_zero_iff _ _ _
    _ ↔ (Scheme.Modules.pullback (Y.fromSpecResidueField x)).map
        ((Scheme.Modules.pullback i).map φ) = 0 := by
      rw [show k ≫ X.fromSpecResidueField (i x) = Y.fromSpecResidueField x ≫ i from
        i.SpecMap_residueFieldMap_fromSpecResidueField x]
      exact (pullback_map_comp_eq_zero_iff _ _ _).symm
    _ ↔ _ := (map_eq_zero_iff_of_natIso
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

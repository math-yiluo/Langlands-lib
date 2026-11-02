import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Chart
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Glue

/-! # Module charts of the iterated twists -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.SchemeModule.SectionClearing

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

section Naturality

variable (T : X.Opens) (L : X.Modules)
  (e : L.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)

/-- The identifications `stripIso` are natural in the module. -/
lemma stripIso_naturality {A B : X.Modules} (g : A ⟶ B) (m : ℕ) :
    (Scheme.Modules.pullback T.ι).map ((twistIter L m).map g) ≫ (stripIso T L e B m).hom =
      (stripIso T L e A m).hom ≫ (Scheme.Modules.pullback T.ι).map g := by
  induction m with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m ih =>
    change (Scheme.Modules.pullback T.ι).map (tensorMap ((twistIter L m).map g) (𝟙 L)) ≫
        pullbackTensorComparisonApp T.ι ((twistIter L m).obj B) L ≫
          tensorMap (stripIso T L e B m).hom (pullbackTriv T L e).hom ≫
            (tensorRightUnitor ((Scheme.Modules.pullback T.ι).obj B)).hom =
      (pullbackTensorComparisonApp T.ι ((twistIter L m).obj A) L ≫
          tensorMap (stripIso T L e A m).hom (pullbackTriv T L e).hom ≫
            (tensorRightUnitor ((Scheme.Modules.pullback T.ι).obj A)).hom) ≫
        (Scheme.Modules.pullback T.ι).map g
    rw [reassoc_of% (pullbackTensorComparisonApp_naturality T.ι ((twistIter L m).map g) (𝟙 L)),
      reassoc_of% (tensorMap_comp _ _ _ _), CategoryTheory.Functor.map_id, Category.id_comp, ih,
      Category.assoc, Category.assoc, ← tensorRightUnitor_naturality,
      reassoc_of% (tensorMap_comp _ _ _ _), Category.comp_id]

/-- The identifications `twistChartIso` are natural in the module. -/
lemma twistChartIso_naturality {A B : X.Modules} (g : A ⟶ B) (m : ℕ) :
    (Scheme.Modules.restrictFunctor T.ι).map ((twistIter L m).map g) ≫
        (twistChartIso T L e B m).hom =
      (twistChartIso T L e A m).hom ≫ (Scheme.Modules.restrictFunctor T.ι).map g := by
  simp only [twistChartIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback T.ι).hom.naturality,
    Category.assoc, reassoc_of% (stripIso_naturality T L e g m), Category.assoc,
    Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback T.ι).inv.naturality]

end Naturality

section ModE

variable {T : X.Opens}

/-- Restriction maps of the restricted module are those of the module. -/
lemma toImage_map (M : X.Modules) {W₁' W₂' : T.toScheme.Opens} (h : W₂' ≤ W₁')
    (d : Γ(M.restrict T.ι, W₁')) :
    toImage M ((M.restrict T.ι).presheaf.map (homOfLE h).op d) =
      M.presheaf.map (homOfLE (T.ι.image_mono h)).op (toImage M d) := rfl

/-- Restricted morphisms act on sections as the original morphisms. -/
lemma toImage_app {M M' : X.Modules} (f : M ⟶ M') {W' : T.toScheme.Opens}
    (d : Γ(M.restrict T.ι, W')) :
    toImage M' (((Scheme.Modules.restrictFunctor T.ι).map f).app W' d) =
      f.app (T.ι ''ᵁ W') (toImage M d) := rfl

/-- The action of functions on sections of the restricted module. -/
lemma toImage_smul (M : X.Modules) {W' : T.toScheme.Opens} (r : Γ(T.toScheme, W'))
    (d : Γ(M.restrict T.ι, W')) :
    toImage M (r • d) = (T.ι.appIso W').inv r • toImage M d := rfl

variable {M Z : X.Modules} (Ψ : M.restrict T.ι ≅ Z.restrict T.ι)

/-- A section of `M` over an open inside `T`, transported to `Z` along an identification of
the restrictions to `T`. -/
def modE (W : X.Opens) (hW : W ≤ T) (d : Γ(M, W)) : Γ(Z, W) :=
  Z.presheaf.map (homOfLE (le_image_preimage hW)).op (toImage Z (Ψ.hom.app (T.ι ⁻¹ᵁ W)
    (ofImage M (M.presheaf.map (homOfLE (T.ι.image_preimage_le W)).op d))))

/-- Transport back along the inverse identification undoes `modE`. -/
lemma modE_symm_modE (W : X.Opens) (hW : W ≤ T) (d : Γ(M, W)) :
    modE Ψ.symm W hW (modE Ψ W hW d) = d := by
  unfold modE
  rw [modules_map_map, modules_map_id, ofImage_toImage]
  have h : ∀ y, Ψ.symm.hom.app (T.ι ⁻¹ᵁ W) (Ψ.hom.app (T.ι ⁻¹ᵁ W) y) = y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.symm_hom,
      Iso.hom_inv_id]
    rfl
  rw [h]
  exact (modules_map_map M _ _ d).trans (modules_map_id M _ d)

/-- `modE` is injective. -/
lemma modE_injective (W : X.Opens) (hW : W ≤ T) : Function.Injective (modE Ψ W hW) :=
  Function.LeftInverse.injective (modE_symm_modE Ψ W hW)

/-- `modE` is surjective. -/
lemma modE_surjective (W : X.Opens) (hW : W ≤ T) : Function.Surjective (modE Ψ W hW) :=
  Function.RightInverse.surjective (modE_symm_modE Ψ.symm W hW)

/-- `modE` commutes with restriction. -/
lemma modE_res (W₁ W₂ : X.Opens) (h₁ : W₁ ≤ T) (h : W₂ ≤ W₁) (d : Γ(M, W₁)) :
    modE Ψ W₂ (h.trans h₁) (M.presheaf.map (homOfLE h).op d) =
      Z.presheaf.map (homOfLE h).op (modE Ψ W₁ h₁ d) := by
  unfold modE
  have h' : T.ι ⁻¹ᵁ W₂ ≤ T.ι ⁻¹ᵁ W₁ := T.ι.preimage_mono h
  rw [modules_map_map, ← modules_map_map M (T.ι.image_preimage_le W₁) (T.ι.image_mono h'),
    ofImage_map M h', hom_app_map Ψ.hom h', toImage_map, modules_map_map, modules_map_map]

/-- `modE` is linear over functions. -/
lemma modE_smul (W : X.Opens) (hW : W ≤ T) (t : Γ(X, W)) (d : Γ(M, W)) :
    modE Ψ W hW (t • d) = t • modE Ψ W hW d := by
  unfold modE
  rw [Scheme.Modules.map_smul, ofImage_smul, Scheme.Modules.Hom.app_smul, toImage_smul,
    Iso.hom_inv_id_apply, Scheme.Modules.map_smul, presheaf_map_map, presheaf_map_id]

/-- `modE` is natural for morphisms compatible with the identifications. -/
lemma modE_naturality {M' Z' : X.Modules} (Ψ' : M'.restrict T.ι ≅ Z'.restrict T.ι)
    (f : M ⟶ M') (g : Z ⟶ Z')
    (hfg : (Scheme.Modules.restrictFunctor T.ι).map f ≫ Ψ'.hom =
      Ψ.hom ≫ (Scheme.Modules.restrictFunctor T.ι).map g)
    (W : X.Opens) (hW : W ≤ T) (d : Γ(M, W)) :
    modE Ψ' W hW (f.app W d) = g.app W (modE Ψ W hW d) := by
  unfold modE
  have h : ∀ y, Ψ'.hom.app (T.ι ⁻¹ᵁ W)
      (((Scheme.Modules.restrictFunctor T.ι).map f).app (T.ι ⁻¹ᵁ W) y) =
      ((Scheme.Modules.restrictFunctor T.ι).map g).app (T.ι ⁻¹ᵁ W)
        (Ψ.hom.app (T.ι ⁻¹ᵁ W) y) := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hfg]
    rfl
  rw [← hom_app_map, ofImage_app, h, toImage_app, hom_app_map]

/-- In the transported sections, a morphism read as multiplication by a coefficient on `T`
is multiplication by the chart coefficient. -/
lemma modE_mul {M' : X.Modules} (Ψ' : M'.restrict T.ι ≅ Z.restrict T.ι) (f : M ⟶ M')
    (φ : structureSheaf T.toScheme ⟶ structureSheaf T.toScheme)
    (hf : (Scheme.Modules.restrictFunctor T.ι).map f ≫ Ψ'.hom =
      Ψ.hom ≫ (unitEndCoefficient φ ⊤ • 𝟙 _))
    (W : X.Opens) (hW : W ≤ T) (d : Γ(M, W)) :
    modE Ψ' W hW (f.app W d) = X.presheaf.map (homOfLE hW).op (chartCoeff φ) • modE Ψ W hW d := by
  unfold modE chartCoeff
  have h : ∀ y, Ψ'.hom.app (T.ι ⁻¹ᵁ W)
      (((Scheme.Modules.restrictFunctor T.ι).map f).app (T.ι ⁻¹ᵁ W) y) =
      restrictScalar (T.ι ⁻¹ᵁ W) (unitEndCoefficient φ ⊤) • Ψ.hom.app (T.ι ⁻¹ᵁ W) y :=
    fun y => by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hf]
      rfl
  have hr : restrictScalar (T.ι ⁻¹ᵁ W) (unitEndCoefficient φ ⊤) =
      T.toScheme.presheaf.map (homOfLE (le_top : T.ι ⁻¹ᵁ W ≤ ⊤)).op
        (unitEndCoefficient φ ⊤) := rfl
  rw [← hom_app_map, ofImage_app, h, toImage_smul, hr, appIso_inv_res,
    Scheme.Modules.map_smul, presheaf_map_map, presheaf_map_map]

end ModE

section TwistChart

variable (N : X.Modules) (s : GlobalSections N) (T : X.Opens)
  (e : N.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)

/-- The module chart of the iterated twists of `Z` over a trivializing open of `N`, with
reference module `Z`. -/
def twistModChart (Z : X.Modules) :
    ModChart (fun m => (twistIter N m).obj Z) (fun m => (stepNat N s m).app Z) Z T
      (chartCoeff (chartMulOf T N e (sectionHom N s))) where
  E m W hW := modE (twistChartIso T N e Z m) W hW
  injective _ W hW := modE_injective _ W hW
  surjective _ W hW := modE_surjective _ W hW
  res _ W₁ W₂ h₁ h d := modE_res _ W₁ W₂ h₁ h d
  smul _ W hW t d := modE_smul _ W hW t d
  mul m W hW d := modE_mul _ _ _ _ (twistChartIso_succ T N e s Z m) W hW d

/-- The module charts of the iterated twists are natural in the module. -/
lemma twistModChart_naturality {A B : X.Modules} (g : A ⟶ B) (m : ℕ) (W : X.Opens)
    (hW : W ≤ T) (d : Γ((twistIter N m).obj A, W)) :
    (twistModChart N s T e B).E m W hW (((twistIter N m).map g).app W d) =
      g.app W ((twistModChart N s T e A).E m W hW d) :=
  modE_naturality _ _ _ g (twistChartIso_naturality T N e g m) W hW d

end TwistChart

end Langlands.AlgebraicGeometry.Modules.SerreVanishing

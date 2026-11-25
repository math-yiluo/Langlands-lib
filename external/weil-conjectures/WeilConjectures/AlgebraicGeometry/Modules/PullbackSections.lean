/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections of the pullback of a quasi-coherent module over an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` a quasi-coherent `𝒪_Y`-module, `V` an affine open
of `Y` and `U` an affine open of `X` with `f(U) ⊆ V`. Then the sections of `f^* ℱ` over `U` are
`Γ(X, U) ⊗[Γ(Y, V)] Γ(ℱ, V)`, the element `1 ⊗ m` corresponding to the restriction to `U` of the
pullback of `m`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_pullback_sections`
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The units of the pullback along two equal morphisms agree, up to `pullbackCongr`. -/
lemma pullbackCongr_hom_app_pullbackSection {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    {U : Y.Opens} (m : Γ(M, U)) :
    ((pullbackCongr h).hom.app M).app (f ⁻¹ᵁ U) (pullbackSection f m) =
      ((pullback g).obj M).presheaf.map (eqToHom (by rw [h])).op (pullbackSection g m) := by
  subst h
  simp [pullbackCongr]

/-- The pullback along a composite `g ≫ f` of a section is the pullback along `g` of its pullback
along `f`, up to `pullbackComp`. -/
lemma pullbackComp_inv_app_pullbackSection (g : Z ⟶ Y) (f : Y ⟶ X) {M : X.Modules}
    {U : X.Opens} (m : Γ(M, U)) :
    ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) (pullbackSection (g ≫ f) m) =
      pullbackSection g (pullbackSection f m) :=
  pullbackUnit_comp_app_apply g f M U m

/-- The pullback along an affine open immersion `Spec Γ(X, U) ⟶ X` of sections over `U`,
followed by the identification `fromSpec ⁻¹ᵁ U = ⊤`, is bijective. -/
lemma bijective_pullbackSection_fromSpec (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (fun m : Γ(M, U) ↦ ((pullback hU.fromSpec).obj M).presheaf.map
      (eqToHom hU.fromSpec_preimage_self.symm).op (pullbackSection hU.fromSpec m)) :=
  (ConcreteCategory.bijective_of_isIso (((pullback hU.fromSpec).obj M).presheaf.map
    (eqToHom hU.fromSpec_preimage_self.symm).op)).comp
    (bijective_pullbackUnit_app_of_isOpenImmersion hU.fromSpec M hU.opensRange_fromSpec.ge)

/-- The pullback along `fromSpec` of sections over `U`, as a linear equivalence
`Γ(M, U) ≃ Γ(fromSpec^* M, ⊤)` over `Γ(X, U)`. -/
noncomputable def pullbackSectionFromSpecEquiv (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ((pullback hU.fromSpec).obj M, ⊤) :=
  LinearEquiv.ofBijective
    { toFun m := ((pullback hU.fromSpec).obj M).presheaf.map
        (eqToHom hU.fromSpec_preimage_self.symm).op (pullbackSection hU.fromSpec m)
      map_add' m m' := by simp [pullbackSection_add]
      map_smul' r m := by
        rw [pullbackSection_smul, map_smul, RingHom.id_apply, hU.fromSpec_app_self,
          smul_Spec_def]
        rfl }
    (bijective_pullbackSection_fromSpec M hU)

lemma pullbackSectionFromSpecEquiv_apply (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (m : Γ(M, U)) :
    pullbackSectionFromSpecEquiv M hU m = ((pullback hU.fromSpec).obj M).presheaf.map
        (eqToHom hU.fromSpec_preimage_self.symm).op (pullbackSection hU.fromSpec m) :=
  rfl

/-- Pullback of sections commutes with restriction along any inclusion of opens. -/
lemma pullbackSection_presheaf_map (g : X ⟶ Y) {M : Y.Modules} {U V : Y.Opens} (i : V ⟶ U)
    (m : Γ(M, U)) :
    pullbackSection g (M.presheaf.map i.op m) =
      ((pullback g).obj M).presheaf.map (homOfLE (g.preimage_mono i.le)).op
        (pullbackSection g m) := by
  rw [show i = homOfLE i.le from Subsingleton.elim _ _]
  exact pullbackSection_map g i.le m

/-- Two restrictions of the same section to the same open agree. -/
lemma presheaf_map_apply_congr (M : X.Modules) {U V : X.Opens} (i j : V ⟶ U) (m : Γ(M, U)) :
    M.presheaf.map i.op m = M.presheaf.map j.op m := by
  rw [Subsingleton.elim i j]


/-- Restricting twice is restricting once. -/
lemma presheaf_map_presheaf_map_apply (M : X.Modules) {U V W : X.Opens} (i : V ⟶ U)
    (j : W ⟶ V) (k : W ⟶ U) (m : Γ(M, U)) :
    M.presheaf.map j.op (M.presheaf.map i.op m) = M.presheaf.map k.op m := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (i.op ≫ j.op) k.op]

lemma iso_hom_app_inv_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(N, U)) :
    Hom.app e.hom U (Hom.app e.inv U x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app,
    ConcreteCategory.id_apply]

lemma natIso_hom_app_inv_app {C : Type*} [Category C] {F G : C ⥤ X.Modules} (e : F ≅ G) (M : C)
    (U : X.Opens) (x : Γ(G.obj M, U)) :
    Hom.app (e.hom.app M) U (Hom.app (e.inv.app M) U x) = x :=
  iso_hom_app_inv_app (e.app M) U x

/-- For a commutative square `g ≫ f = g' ≫ f'`, the comparison `g^* f^* M ≅ g'^* f'^* M` sends
the iterated pullback of a section to the iterated pullback. -/
lemma pullbackComp_congr_hom_app_pullbackSection {Y' : Scheme.{u}} {g : Z ⟶ Y} {f : Y ⟶ X}
    {g' : Z ⟶ Y'} {f' : Y' ⟶ X} (h : g ≫ f = g' ≫ f') (M : X.Modules) {U : X.Opens}
    (m : Γ(M, U)) :
    ((pullbackComp g f).app M ≪≫ (pullbackCongr h).app M ≪≫
        ((pullbackComp g' f').app M).symm).hom.app ((g ≫ f) ⁻¹ᵁ U)
        (pullbackSection g (pullbackSection f m)) =
      ((pullback g').obj ((pullback f').obj M)).presheaf.map (eqToHom (by
        change (g ≫ f) ⁻¹ᵁ U = (g' ≫ f') ⁻¹ᵁ U; rw [h])).op
        (pullbackSection g' (pullbackSection f' m)) := by
  rw [← pullbackComp_inv_app_pullbackSection, ← pullbackComp_inv_app_pullbackSection]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [natIso_hom_app_inv_app (pullbackComp g f) M _ (pullbackSection (g ≫ f) m),
    pullbackCongr_hom_app_pullbackSection]
  exact Hom.app_presheaf_map _ _ _

/-- A variant of `pullbackComp_congr_hom_app_pullbackSection` stated over `g ⁻¹ᵁ f ⁻¹ᵁ U`. -/
lemma pullbackComp_congr_hom_app_pullbackSection' {Y' : Scheme.{u}} {g : Z ⟶ Y} {f : Y ⟶ X}
    {g' : Z ⟶ Y'} {f' : Y' ⟶ X} (h : g ≫ f = g' ≫ f') (M : X.Modules) {U : X.Opens}
    (m : Γ(M, U)) :
    ((pullbackComp g f).app M ≪≫ (pullbackCongr h).app M ≪≫
        ((pullbackComp g' f').app M).symm).hom.app (g ⁻¹ᵁ f ⁻¹ᵁ U)
        (pullbackSection g (pullbackSection f m)) =
      ((pullback g').obj ((pullback f').obj M)).presheaf.map (eqToHom (by
        change (g ≫ f) ⁻¹ᵁ U = (g' ≫ f') ⁻¹ᵁ U; rw [h])).op
        (pullbackSection g' (pullbackSection f' m)) :=
  pullbackComp_congr_hom_app_pullbackSection h M m

/-- `pullbackΓ` is the pullback of sections followed by the identification `g ⁻¹ᵁ ⊤ = ⊤`. -/
lemma pullbackΓ_eq (g : Y ⟶ X) (M : X.Modules) (x : Γ(M, ⊤)) :
    pullbackΓ g M x = ((pullback g).obj M).presheaf.map (eqToHom g.preimage_top.symm).op
      (pullbackSection g x) := by
  rw [pullbackΓ_apply, show (eqToHom g.preimage_top.symm).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- A morphism of `𝒪_{Spec R}`-modules, on global sections, as an `R`-linear map. -/
noncomputable def Hom.appTopLinear {R : CommRingCat.{u}} {M N : (Spec R).Modules} (φ : M ⟶ N) :
    Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) where
  toFun := φ.app ⊤
  map_add' := map_add _
  map_smul' r x := by rw [smul_Spec_def, smul_Spec_def, Hom.app_smul]; rfl

/-- **Sections of a pullback over an affine open.** Let `f : X ⟶ Y`, `ℱ` a quasi-coherent
`𝒪_Y`-module, `V ⊆ Y` and `U ⊆ X` affine opens with `U ⊆ f⁻¹ V`. Then
`Γ(f^* ℱ, U) ≅ Γ(X, U) ⊗[Γ(Y, V)] Γ(ℱ, V)`, with `1 ⊗ m` corresponding to the restriction of the
pullback of `m`. -/
theorem exists_linearEquiv_pullback_sections (f : X ⟶ Y) (ℱ : Y.Modules) [ℱ.IsQuasicoherent]
    {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V U hUV).hom.toAlgebra
    ∃ e : Γ(X, U) ⊗[Γ(Y, V)] Γ(ℱ, V) ≃ₗ[Γ(X, U)] Γ((pullback f).obj ℱ, U),
      ∀ m : Γ(ℱ, V), e (1 ⊗ₜ m) =
        ((pullback f).obj ℱ).presheaf.map (homOfLE hUV).op (pullbackSection f m) := by
  let := (f.appLE V U hUV).hom.toAlgebra
  have hsq : Spec.map (f.appLE V U hUV) ≫ hV.fromSpec = hU.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  let 𝒢 := (pullback hV.fromSpec).obj ℱ
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_pullback_Spec (A := Γ(Y, V)) (B := Γ(X, U)) 𝒢
  replace he₁ (m) : e₁ (1 ⊗ₜ m) = pullbackΓ (Spec.map (f.appLE V U hUV)) 𝒢 m := he₁ m
  let E : (pullback (Spec.map (f.appLE V U hUV))).obj 𝒢 ≅
      (pullback hU.fromSpec).obj ((pullback f).obj ℱ) :=
    (pullbackComp _ _).app ℱ ≪≫ (pullbackCongr hsq).app ℱ ≪≫ ((pullbackComp _ _).app ℱ).symm
  let eE : Γ((pullback (Spec.map (f.appLE V U hUV))).obj 𝒢, ⊤) ≃ₗ[Γ(X, U)]
      Γ((pullback hU.fromSpec).obj ((pullback f).obj ℱ), ⊤) :=
    { Hom.appTopLinear E.hom with
      invFun := E.inv.app ⊤
      left_inv x := congr($(E.hom_inv_id).app ⊤ x)
      right_inv x := congr($(E.inv_hom_id).app ⊤ x) }
  refine ⟨((pullbackSectionFromSpecEquiv ℱ hV).baseChange Γ(Y, V) Γ(X, U) _ _).trans
    (e₁.trans (eE.trans (pullbackSectionFromSpecEquiv _ hU).symm)), fun m ↦ ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.trans_apply, he₁,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq, pullbackSectionFromSpecEquiv_apply,
    pullbackSectionFromSpecEquiv_apply, pullbackΓ_eq]
  have hE (x) : eE x = E.hom.app ⊤ x := rfl
  refine (hE _).trans ?_
  rw [Hom.app_presheaf_map, pullbackSection_presheaf_map, Hom.app_presheaf_map,
    show E.hom.app _ (pullbackSection _ (pullbackSection _ m)) = _ from
      pullbackComp_congr_hom_app_pullbackSection' hsq ℱ m, pullbackSection_presheaf_map]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

section PullbackSection

variable {A B : Scheme.{u}} (g : A ⟶ B)

/-- Pullbacks of sections are natural in the module. -/
lemma pullback_map_app_pullbackSection {M N : B.Modules} (ψ : M ⟶ N) {U : B.Opens}
    (m : Γ(M, U)) :
    ((Modules.pullback g).map ψ).app (g ⁻¹ᵁ U) (pullbackSection g m) =
      pullbackSection g (ψ.app U m) := by
  have h := (pullbackPushforwardAdjunction g).unit.naturality ψ
  exact (congrArg (fun φ ↦ φ.app U m) h).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of a function `r` on `U`, under `g^* 𝒪_B ≅ 𝒪_A`, is `g^♯ r`. -/
lemma pullbackObjUnitIso_hom_app_pullbackSection {U : B.Opens} (r : Γ(B, U)) :
    (pullbackObjUnitIso g).hom.app (g ⁻¹ᵁ U) (pullbackSection g (M := Modules.unit B) r) =
      g.app U r := by
  have h2 : (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackObjUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_unit] at h2
  exact congrArg (fun φ : Modules.unit B ⟶ (pushforward g).obj (Modules.unit A) ↦ φ.app U r) h2

end PullbackSection

end AlgebraicGeometry.Scheme.Modules

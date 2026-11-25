/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.SectionsBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Sections of the Čech resolution of a base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, a finite family `U` of opens of `X` and an open `W` of `T`, with
`B = Γ(T, W)`. The sections over `f'⁻¹ W` of the sheafified Čech complex `Č(g'⁻¹ U, g'^* ℱ)` are
the explicit Čech complex of the presheaf `V ↦ Γ(f'⁻¹ W, j_{V,*} (g'^* ℱ)|_V)`
(`AlgebraicGeometry.Scheme.Modules.sectionsCechResolutionIso`). We construct the base change
map `B ⊗[A] Č(U, ℱ) ⟶ Γ(f'⁻¹ W, Č(g'⁻¹ U, g'^* ℱ))`, `b ⊗ c ↦ (y ↦ b • (g'^* c_y)|)`,
as a morphism of complexes of abelian groups
(`AlgebraicGeometry.Scheme.Modules.cechSectionsBaseChange`), and show that it is bijective in
each degree when `W` is affine, `ℱ` is quasi-coherent and the finite intersections of the `U i`
are affine (`AlgebraicGeometry.Scheme.Modules.bijective_cechSectionsBaseChange_f`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- The presheaf `V ↦ Γ(Z, j_{V,*} M|_V)` of abelian groups, whose Čech complex is the complex
of sections over `Z` of the sheafified Čech complex of `M`. -/
noncomputable abbrev cechSectionsPresheaf {Y : Scheme.{u}} (M : Y.Modules) (Z : Y.Opens) :
    Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  cechPresheaf M ⋙ sectionsModuleFunctor Z ⋙ forget₂ _ AddCommGrpCat.{u}

lemma cechSectionsPresheaf_map_apply {Y : Scheme.{u}} (M : Y.Modules) (Z : Y.Opens)
    {V V' : Y.Opens} (h : V' ≤ V) (x : (cechSectionsPresheaf M Z).obj (op V)) :
    (cechSectionsPresheaf M Z).map (homOfLE h).op x =
      (M.presheaf.map (homOfLE (ι_image_preimage_mono h Z)).op :
        Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ Z) ⟶ Γ(M, V'.ι ''ᵁ V'.ι ⁻¹ᵁ Z)) x :=
  ConcreteCategory.congr_hom (cechPresheaf_map_app M (homOfLE h).op Z) x

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens) (W : T.Opens)
  [Algebra Γ(S, ⊤) Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

omit [Algebra Γ(S, ⊤) Γ(T, W)] in
lemma cech_image_preimage_le {k : ℕ} (y : Fin (k + 1) → ι) :
    (⨅ l, g' ⁻¹ᵁ U (y l)).ι ''ᵁ (⨅ l, g' ⁻¹ᵁ U (y l)).ι ⁻¹ᵁ (f' ⁻¹ᵁ W) ≤
      g' ⁻¹ᵁ (⨅ l, U (y l)) ⊓ f' ⁻¹ᵁ W := by
  rw [ι_image_preimage, iInf_preimage_eq_preimage_iInf g' U y]

/-- The base change of Čech cochains `B ⊗[A] Č^k(U, ℱ) ⟶ Γ(f'⁻¹ W, Č^k(g'⁻¹ U, g'^* ℱ))`,
`b ⊗ c ↦ (y ↦ b • (g'^* c_y)|)`, in explicit cochains. -/
noncomputable def cechSectionsBaseChangeX (k : ℕ) :
    Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) →+
      CechCochain (fun i ↦ g' ⁻¹ᵁ U i) (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W))
        k :=
  AddMonoidHom.pi fun y ↦ (sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)).comp
    ((LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, W)).toAddMonoidHom

lemma cechSectionsBaseChangeX_tmul (k : ℕ) (b : Γ(T, W))
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) (y : Fin (k + 1) → ι) :
    cechSectionsBaseChangeX H ℱ U W hg k (b ⊗ₜ c) y =
      sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y) (b ⊗ₜ c y) :=
  rfl

/-- **The base change of Čech cochains commutes with the differentials.** -/
lemma cechSectionsBaseChangeX_d (k : ℕ)
    (x : Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    cechSectionsBaseChangeX H ℱ U W hg (k + 1) ((cechModuleD f ℱ U k).baseChange Γ(T, W) x) =
      ((cechComplex (fun i ↦ g' ⁻¹ᵁ U i)).obj
        (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W))).d k (k + 1)
        (cechSectionsBaseChangeX H ℱ U W hg k x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [LinearMap.baseChange_tmul, cechSectionsBaseChangeX_tmul, cechComplex_d_apply,
      cechModuleD_apply_apply, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.tmul_smul, map_zsmul, cechSectionsPresheaf_map_apply,
      cechSectionsBaseChangeX_tmul]
    congr 1
    rw [presheaf_map_sectionsBaseChangeOpen H ℱ W hg (iInf_le_iInf_comp U y i.succAbove),
      LinearMap.baseChange_tmul]

/-- **The base change map of Čech complexes on sections over `f'⁻¹ W`**:
`B ⊗[A] Č(U, ℱ) ⟶ Γ(f'⁻¹ W, Č(g'⁻¹ U, g'^* ℱ))` as a morphism of complexes of abelian groups,
the target in explicit cochains. -/
noncomputable def cechSectionsBaseChange :
    ((forget₂ (ModuleCat.{u} Γ(T, W)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, W)).mapHomologicalComplex _).obj
        (cechModuleComplexNat f ℱ U)) ⟶
      (cechComplex (fun i ↦ g' ⁻¹ᵁ U i)).obj
        (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)) where
  f k := AddCommGrpCat.ofHom (cechSectionsBaseChangeX H ℱ U W hg k)
  comm' := by
    rintro k _ rfl
    ext x
    change ((cechComplex (fun i ↦ g' ⁻¹ᵁ U i)).obj
      (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W))).d k (k + 1)
        (cechSectionsBaseChangeX H ℱ U W hg k x) =
      cechSectionsBaseChangeX H ℱ U W hg (k + 1)
        (((cechModuleComplexNat f ℱ U).d k (k + 1)).hom.baseChange Γ(T, W) x)
    rw [cechModuleComplexNat_d]
    exact (cechSectionsBaseChangeX_d H ℱ U W hg k x).symm

lemma cechSectionsBaseChange_f_apply (k : ℕ) (x) :
    (cechSectionsBaseChange H ℱ U W hg).f k x = cechSectionsBaseChangeX H ℱ U W hg k x :=
  rfl

omit [Algebra Γ(S, ⊤) Γ(T, W)] in
lemma cech_image_preimage_eq {k : ℕ} (y : Fin (k + 1) → ι) :
    (⨅ l, g' ⁻¹ᵁ U (y l)).ι ''ᵁ (⨅ l, g' ⁻¹ᵁ U (y l)).ι ⁻¹ᵁ (f' ⁻¹ᵁ W) =
      g' ⁻¹ᵁ (⨅ l, U (y l)) ⊓ f' ⁻¹ᵁ W := by
  rw [ι_image_preimage, iInf_preimage_eq_preimage_iInf g' U y]

/-- **The base change map of Čech complexes is bijective** over an affine open `W` of `T`, for
`S` affine, `ℱ` quasi-coherent and a finite family `U` whose finite intersections are affine. -/
theorem bijective_cechSectionsBaseChangeX [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] (hW : IsAffineOpen W)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (k : ℕ) :
    Function.Bijective (cechSectionsBaseChangeX H ℱ U W hg k) := by
  classical
  have := Fintype.ofFinite ι
  have hy (y : Fin (k + 1) → ι) :
      Function.Bijective (sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)) := by
    have h := presheaf_map_sectionsBaseChangeOpen H ℱ W hg (le_refl (⨅ l, U (y l)))
      (le_refl _) (cech_image_preimage_le U W y) (cech_image_preimage_le U W y)
    have hid : (sectionsModuleRestrict f ℱ (le_refl (⨅ l, U (y l)))).baseChange Γ(T, W) =
        LinearMap.id := by
      rw [show sectionsModuleRestrict f ℱ (le_refl (⨅ l, U (y l))) = LinearMap.id from
        LinearMap.ext fun m ↦ sectionsModuleRestrict_self f ℱ _ m, LinearMap.baseChange_id]
    have : ⇑(sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)) =
        ((pullback g').obj ℱ).presheaf.map (homOfLE (cech_image_preimage_le U W y)).op ∘
          sectionsBaseChangeOpen H ℱ W hg (le_refl _) := by
      funext x
      rw [Function.comp_apply, h, hid, LinearMap.id_apply]
    rw [this]
    have := isIso_presheaf_map_of_le ((pullback g').obj ℱ)
      (homOfLE (cech_image_preimage_le (f' := f') (g' := g') U W y))
      (cech_image_preimage_eq (f' := f') (g' := g') U W y).ge
    exact (ConcreteCategory.bijective_of_isIso _).comp
      (bijective_sectionsBaseChangeOpen H ℱ W hg hW (hU k y))
  let e := (TensorProduct.piRight Γ(S, ⊤) Γ(T, W) Γ(T, W)
    (fun y : Fin (k + 1) → ι ↦ sectionsModule f ℱ (⨅ l, U (y l)))).toAddEquiv.trans
    (AddEquiv.piCongrRight fun y ↦ AddEquiv.ofBijective _ (hy y))
  suffices h : ∀ x, cechSectionsBaseChangeX H ℱ U W hg k x = e x by
    have : ⇑(cechSectionsBaseChangeX H ℱ U W hg k) = ⇑e := funext h
    rw [this]
    exact e.bijective
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [cechSectionsBaseChangeX_tmul]
    rfl

/-! ### The module structure on the sections of the Čech resolution -/

section Sections

variable {Z : Scheme.{u}} (M : Z.Modules)

/-- The functions on `V` act on the sections over `V` of `j_* (M|_A)` through their restriction
to `A ⊓ V`. -/
lemma extendRestrict_smul (A V : Z.Opens) (r : Γ(Z, V))
    (m : Γ((extendRestrictFunctor A).obj M, V)) :
    (show Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V) from r • m) =
      Z.presheaf.map (homOfLE (ι_image_preimage_le_self A V)).op r •
        (show Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V) from m) := by
  change (A.ι.appIso (A.ι ⁻¹ᵁ V)).inv (A.ι.app V r) • (show Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V) from m) = _
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.app_appIso_inv]
  rfl

variable {ι : Type u} (U : ι → Z.Opens)

/-- The sections of the Čech resolution in explicit cochains, through the restriction maps of the
presheaf `V ↦ j_{V,*} (M|_V)`. -/
lemma sectionsCechResolutionIso_hom_f_apply' (V : Z.Opens) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V).hom.f k x y =
      Hom.app ((cechPresheaf M).map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op) V
        (Hom.app (Pi.π (fun y : Fin (k + 1) → ι ↦ (cechPresheaf M).obj (op (∏ᶜ fun l ↦ U (y l))))
          y) V x) := by
  change cechComplexFunctorXAddEquiv U (cechPresheaf M ⋙ sectionsModuleFunctor V) k
    ((cechComplexFunctorMapIso U (sectionsModuleFunctor V) (cechPresheaf M)).hom.f k x) y = _
  rw [cechComplexFunctorXAddEquiv_apply, cechComplexFunctorMapIso_hom_f, cechComplexFunctorπ]
  have h := ConcreteCategory.congr_hom (piComparison_comp_π (sectionsModuleFunctor V)
    (fun y : Fin (k + 1) → ι ↦ (cechPresheaf M).obj (op (∏ᶜ fun l ↦ U (y l)))) y) x
  rw [ConcreteCategory.comp_apply] at h
  exact congrArg _ h

/-- The sections of the Čech resolution in explicit cochains. -/
lemma sectionsCechResolutionIso_hom_f_apply (V : Z.Opens) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V).hom.f k x y =
      M.presheaf.map (homOfLE (ι_image_preimage_mono (TopCat.Presheaf.iInf_le_piObj U y) V)).op
        ((Pi.π (fun y : Fin (k + 1) → ι ↦ (cechPresheaf M).obj (op (∏ᶜ fun l ↦ U (y l)))) y).app
          V x) := by
  rw [sectionsCechResolutionIso_hom_f_apply']
  exact ConcreteCategory.congr_hom
    (cechPresheaf_map_app M (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op V) _

/-- The identification of the sections of the Čech resolution with explicit cochains is linear
over the functions. -/
lemma sectionsCechResolutionIso_hom_f_smul (V : Z.Opens) (k : ℕ) (r : Γ(Z, V))
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V).hom.f k (r • x) y =
      (show Γ((cechPresheaf M).obj (op (⨅ l, U (y l))), V) from
        r • (show Γ((cechPresheaf M).obj (op (⨅ l, U (y l))), V) from
          (sectionsCechResolutionIso U M V).hom.f k x y)) := by
  rw [sectionsCechResolutionIso_hom_f_apply', sectionsCechResolutionIso_hom_f_apply',
    Hom.app_smul, Hom.app_smul]

/-- The restriction of a section of the Čech resolution, in explicit cochains. -/
lemma sectionsCechResolutionIso_hom_f_presheaf_map {V V' : Z.Opens} (h : V' ≤ V) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V').hom.f k
        (((cechResolution U M).X k).presheaf.map (homOfLE h).op x) y =
      ((cechPresheaf M).obj (op (⨅ l, U (y l)))).presheaf.map (homOfLE h).op
        ((sectionsCechResolutionIso U M V).hom.f k x y) := by
  rw [sectionsCechResolutionIso_hom_f_apply', sectionsCechResolutionIso_hom_f_apply']
  erw [Hom.app_presheaf_map (Pi.π _ y) (homOfLE h) x]
  exact Hom.app_presheaf_map _ (homOfLE h) _

lemma sectionsCechResolutionIso_inv_hom_f_apply (V : Z.Opens) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) :
    (sectionsCechResolutionIso U M V).inv.f k ((sectionsCechResolutionIso U M V).hom.f k x) =
      x := by
  change ((sectionsCechResolutionIso U M V).hom.f k ≫
    (sectionsCechResolutionIso U M V).inv.f k) x = x
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rfl

lemma sectionsCechResolutionIso_hom_inv_f_apply (V : Z.Opens) (k : ℕ) (c) :
    (sectionsCechResolutionIso U M V).hom.f k ((sectionsCechResolutionIso U M V).inv.f k c) =
      c := by
  change ((sectionsCechResolutionIso U M V).inv.f k ≫
    (sectionsCechResolutionIso U M V).hom.f k) c = c
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rfl

lemma cechPresheaf_obj_presheaf_map_apply (A : Z.Opens) {V V' : Z.Opens} (h : V' ≤ V)
    (x : Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V)) :
    ((cechPresheaf M).obj (op A)).presheaf.map (homOfLE h).op x =
      M.presheaf.map (homOfLE (by
          rw [ι_image_preimage, ι_image_preimage]; exact inf_le_inf_left A h :
        A.ι ''ᵁ A.ι ⁻¹ᵁ V' ≤ A.ι ''ᵁ A.ι ⁻¹ᵁ V)).op x :=
  rfl

end Sections

/-! ### Linearity and restriction of the base change map -/

section Linear

lemma sectionsBaseChangeOpen_smul {UX : X.Opens} {Z : Y.Opens} (hZ : Z ≤ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W)
    (b : Γ(T, W)) (w : Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ UX) :
    sectionsBaseChangeOpen H ℱ W hg hZ (b • w) =
      f'.appLE W Z (hZ.trans inf_le_right) b • sectionsBaseChangeOpen H ℱ W hg hZ w := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul b' m =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, sectionsBaseChangeOpen_tmul,
      sectionsBaseChangeOpen_tmul, map_mul, mul_smul]

/-- **The base change map of Čech cochains is semilinear**, once identified with the sections of
the Čech resolution: `b • w ↦ f'^♯ b • (…)`. -/
lemma sectionsCechResolutionIso_inv_cechSectionsBaseChangeX_smul (k : ℕ) (b : Γ(T, W))
    (w : Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)).inv.f k
        (cechSectionsBaseChangeX H ℱ U W hg k (b • w)) =
      (show Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W) from
        f'.app W b •
          (show Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W)
            from (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
              (f' ⁻¹ᵁ W)).inv.f k (cechSectionsBaseChangeX H ℱ U W hg k w))) := by
  set iso := sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)
  set s : Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W) :=
    iso.inv.f k (cechSectionsBaseChangeX H ℱ U W hg k w)
  have hs : iso.hom.f k s = cechSectionsBaseChangeX H ℱ U W hg k w :=
    sectionsCechResolutionIso_hom_inv_f_apply _ _ _ _ _
  have key : cechSectionsBaseChangeX H ℱ U W hg k (b • w) = iso.hom.f k (f'.app W b • s) := by
    funext y
    rw [sectionsCechResolutionIso_hom_f_smul, hs]
    change sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)
      (((LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, W)) (b • w)) = _
    rw [LinearMap.map_smul, sectionsBaseChangeOpen_smul]
    exact (extendRestrict_smul _ _ _ _ _).symm
  rw [key]
  exact sectionsCechResolutionIso_inv_hom_f_apply _ _ _ _ _

/-- **The base change map of Čech cochains is compatible with restriction** from `W'` to
`W ≤ W'`, on the cochains `1 ⊗ m`. -/
lemma presheaf_map_sectionsCechResolutionIso_inv_one_tmul {W' : T.Opens} (hW : W ≤ W')
    [Algebra Γ(S, ⊤) Γ(T, W')]
    (hg' : algebraMap Γ(S, ⊤) Γ(T, W') = (g.appLE ⊤ W' (le_top.trans g.preimage_top.ge)).hom)
    (k : ℕ) (m : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :
    ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k).presheaf.map
        (homOfLE (f'.preimage_mono hW)).op
        ((sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
          (f' ⁻¹ᵁ W')).inv.f k (cechSectionsBaseChangeX H ℱ U W' hg' k (1 ⊗ₜ m))) =
      (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
          (f' ⁻¹ᵁ W)).inv.f k (cechSectionsBaseChangeX H ℱ U W hg k (1 ⊗ₜ m)) := by
  set iso' := sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W')
  set s' : Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W') :=
    iso'.inv.f k (cechSectionsBaseChangeX H ℱ U W' hg' k (1 ⊗ₜ m))
  have hs' : iso'.hom.f k s' = cechSectionsBaseChangeX H ℱ U W' hg' k (1 ⊗ₜ m) :=
    sectionsCechResolutionIso_hom_inv_f_apply _ _ _ _ _
  set iso := sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)
  have key : iso.hom.f k
      (((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k).presheaf.map
        (homOfLE (f'.preimage_mono hW)).op s') =
      cechSectionsBaseChangeX H ℱ U W hg k (1 ⊗ₜ m) := by
    funext y
    rw [sectionsCechResolutionIso_hom_f_presheaf_map, hs', cechSectionsBaseChangeX_tmul,
      cechSectionsBaseChangeX_tmul]
    erw [sectionsBaseChangeOpen_tmul, sectionsBaseChangeOpen_tmul]
    simp only [map_one, one_smul]
    erw [cechPresheaf_obj_presheaf_map_apply]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← key]
  exact (sectionsCechResolutionIso_inv_hom_f_apply _ _ _ _ _).symm

end Linear

end AlgebraicGeometry.Scheme.Modules

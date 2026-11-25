/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-!
# Internal homs and pushforward

Let `f : X ⟶ Y` be a morphism of schemes, `L` a sheaf of modules on `X`, `G` a sheaf of modules
on `Y` and `τ : f_* L ⟶ G` a morphism, e.g. a trace map. Then every `φ : M|_{f⁻¹V} ⟶ L|_{f⁻¹V}`
gives `τ ∘ f_* φ : (f_* M)|_V ⟶ G|_V`. This is a morphism of sheaves of modules
`f_* Hom(M, L) ⟶ Hom(f_* M, G)` on `Y`, natural in `M`.

For a finite morphism `f` and `τ` identifying `f_* L` with `Hom(f_* 𝒪_X, G)`, this is the
adjunction isomorphism `f_* Hom(M, L) ≅ Hom(f_* M, G)` of duality for `f`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pushforwardHomObjComparison`: the morphism
  `f_* Hom(M, L) ⟶ Hom(f_* M, G)`, `φ ↦ τ ∘ f_* φ`.
- `AlgebraicGeometry.Scheme.Modules.pushforwardHomObjComparisonNatTrans`: the same morphism as a
  natural transformation in `M`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : X.Modules} {G : Y.Modules}
  (τ : (pushforward f).obj L ⟶ G) (M : X.Modules)

/-- The section `τ ∘ f_* φ : (f_* M)|_V ⟶ G|_V` of `Hom(f_* M, G)` over `V` given by a section
`φ : M|_{f⁻¹V} ⟶ L|_{f⁻¹V}` of `Hom(M, L)` over `f⁻¹V`. -/
noncomputable def pushforwardHomObjComparisonApp (V : Y.Opens)
    (φ : (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj L.val) :
    (PresheafOfModules.restrictOver Y.sheaf.obj V).obj ((pushforward f).obj M).val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj V).obj G.val where
  app W := (ModuleCat.restrictScalars (f.app W.unop.left).hom).map
      (φ.app (op (Over.mk ((TopologicalSpace.Opens.map f.base).map W.unop.hom)))) ≫
    τ.val.app (op W.unop.left)
  naturality {W W'} g := by
    ext x
    have h₁ := PresheafOfModules.naturality_apply φ
      (Over.homMk ((TopologicalSpace.Opens.map f.base).map g.unop.left) (Subsingleton.elim _ _) :
        Over.mk ((TopologicalSpace.Opens.map f.base).map W'.unop.hom) ⟶
          Over.mk ((TopologicalSpace.Opens.map f.base).map W.unop.hom)).op x
    have h₂ := PresheafOfModules.naturality_apply τ.val g.unop.left.op
      ((φ.app (op (Over.mk ((TopologicalSpace.Opens.map f.base).map W.unop.hom)))).hom x)
    exact (congrArg (τ.val.app (op W'.unop.left)) h₁).trans h₂

@[simp]
lemma pushforwardHomObjComparisonApp_app_apply (V : Y.Opens)
    (φ : (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj L.val)
    (W : (Over V)ᵒᵖ) (x : Γ(M, f ⁻¹ᵁ W.unop.left)) :
    (pushforwardHomObjComparisonApp f τ M V φ).app W x = τ.val.app (op W.unop.left)
      ((φ.app (op (Over.mk ((TopologicalSpace.Opens.map f.base).map W.unop.hom)))).hom x) :=
  rfl

/-- The morphism `f_* Hom(M, L) ⟶ Hom(f_* M, G)` of sheaves of modules on `Y` sending a section
`φ : M|_{f⁻¹V} ⟶ L|_{f⁻¹V}` to `τ ∘ f_* φ : (f_* M)|_V ⟶ G|_V`. -/
noncomputable def pushforwardHomObjComparison :
    (pushforward f).obj (homObj M L) ⟶ homObj ((pushforward f).obj M) G where
  val :=
    { app V := ModuleCat.ofHom (X := ((pushforward f).obj (homObj M L)).val.obj V)
        (Y := (homObj ((pushforward f).obj M) G).val.obj V)
        { toFun := pushforwardHomObjComparisonApp f τ M V.unop
          map_add' φ ψ := by
            refine PresheafOfModules.hom_ext fun W ↦ ?_
            ext x
            exact map_add (τ.val.app (op W.unop.left)).hom _ _
          map_smul' r φ := by
            refine PresheafOfModules.hom_ext fun W ↦ ?_
            ext x
            -- `r` acts on `f_* Hom(M, L)` through `f^♯`, and `τ` is `𝒪_Y`-linear.
            have h := (ConcreteCategory.congr_hom (f.naturality W.unop.hom.op) r).symm
            let y : Γ(L, f ⁻¹ᵁ W.unop.left) :=
              (φ.app (op (Over.mk ((TopologicalSpace.Opens.map f.base).map W.unop.hom)))).hom x
            exact (congrArg (fun s : Γ(X, f ⁻¹ᵁ W.unop.left) ↦ τ.app W.unop.left
              (show Γ((pushforward f).obj L, W.unop.left) from s • y)) h).trans
                (τ.app_smul (Y.presheaf.map W.unop.hom.op r) y) }
      naturality {V V'} g := by
        ext φ : 2
        refine PresheafOfModules.hom_ext fun W ↦ ?_
        ext x
        exact congrArg (τ.val.app (op W.unop.left)).hom
          (PresheafOfModules.restrictOver_hom_app_congr φ rfl x) }

variable {M} in
/-- `f_* Hom(M, L) ⟶ Hom(f_* M, G)` is natural in `M`: for `u : M' ⟶ M` the square
```
  f_* Hom(M, L)  ---> Hom(f_* M, G)
        |                   |
     f_* u^*            (f_* u)^*
        v                   v
  f_* Hom(M', L) ---> Hom(f_* M', G)
```
commutes. -/
@[reassoc]
lemma pushforwardHomObjComparison_naturality {M' : X.Modules} (u : M' ⟶ M) :
    (pushforward f).map (SheafOfModules.homObjMap (R := X.sheaf) u (𝟙 L)) ≫
        pushforwardHomObjComparison f τ M' =
      pushforwardHomObjComparison f τ M ≫
        SheafOfModules.homObjMap (R := Y.sheaf) ((pushforward f).map u) (𝟙 G) := by
  ext V φ
  rfl

/-- The morphism `f_* Hom(M, L) ⟶ Hom(f_* M, G)`, `φ ↦ τ ∘ f_* φ`, as a natural transformation
in `M`. -/
@[simps]
noncomputable def pushforwardHomObjComparisonNatTrans :
    (SheafOfModules.homFunctor X.sheaf).flip.obj L ⋙ pushforward f ⟶
      (pushforward f).op ⋙ (SheafOfModules.homFunctor Y.sheaf).flip.obj G where
  app M := pushforwardHomObjComparison f τ M.unop
  naturality _ _ u := pushforwardHomObjComparison_naturality f τ u.unop

section Retract

variable {f τ}

/-- `φ ↦ τ ∘ f_* φ` is compatible with composition: `τ ∘ f_*(φ ∘ a) = (τ ∘ f_* φ) ∘ f_* a`. -/
lemma pushforwardHomObjComparisonApp_comp {M' : X.Modules} (V : Y.Opens)
    (a : (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M'.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val)
    (φ : (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj L.val) :
    pushforwardHomObjComparisonApp f τ M' V (a ≫ φ) =
      pushforwardHomObjComparisonApp f (𝟙 _) M' V a ≫
        pushforwardHomObjComparisonApp f τ M V φ := by
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext x
  rfl

lemma pushforwardHomObjComparisonApp_id (V : Y.Opens) :
    pushforwardHomObjComparisonApp f (𝟙 _) M V (𝟙 _) = 𝟙 _ := by
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext x
  rfl

lemma pushforwardHomObjComparisonApp_sum (V : Y.Opens) {ι : Type*} (s : Finset ι)
    (φ : ι → ((PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj L.val)) :
    pushforwardHomObjComparisonApp f τ M V (∑ i ∈ s, φ i) =
      ∑ i ∈ s, pushforwardHomObjComparisonApp f τ M V (φ i) :=
  map_sum ((pushforwardHomObjComparison f τ M).val.app (op V)).hom φ s

/-- If `M|_{f⁻¹V}` is a direct summand of a finite direct sum of copies of `N|_{f⁻¹V}`, and
`φ ↦ τ ∘ f_* φ` is bijective over `V` for `N`, then it is bijective over `V` for `M`. -/
lemma bijective_pushforwardHomObjComparisonApp_of_sum_comp_eq_id {N : X.Modules} (V : Y.Opens)
    {n : ℕ} (ξ : Fin n → ((PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj N.val))
    (m : Fin n → ((PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj N.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val))
    (h : ∑ j, ξ j ≫ m j = 𝟙 _)
    (hN : Function.Bijective (pushforwardHomObjComparisonApp f τ N V)) :
    Function.Bijective (pushforwardHomObjComparisonApp f τ M V) := by
  have hsum (φ : (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj (f ⁻¹ᵁ V)).obj L.val) :
      φ = ∑ j, ξ j ≫ m j ≫ φ := by
    simp_rw [← Category.assoc, ← Preadditive.sum_comp, h, Category.id_comp]
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · have hj (j : Fin n) : m j ≫ φ = m j ≫ ψ := hN.1 <| by
      rw [pushforwardHomObjComparisonApp_comp, pushforwardHomObjComparisonApp_comp, hφψ]
    rw [hsum φ, hsum ψ]
    simp_rw [hj]
  · choose ψ hψ using fun j ↦ hN.2 (pushforwardHomObjComparisonApp f (𝟙 _) N V (m j) ≫ χ)
    refine ⟨∑ j, ξ j ≫ ψ j, ?_⟩
    rw [pushforwardHomObjComparisonApp_sum]
    simp_rw [pushforwardHomObjComparisonApp_comp, hψ, ← Category.assoc]
    rw [← Preadditive.sum_comp]
    simp_rw [← pushforwardHomObjComparisonApp_comp]
    rw [← pushforwardHomObjComparisonApp_sum, h, pushforwardHomObjComparisonApp_id,
      Category.id_comp]

/-- **Reduction to the structure sheaf.** Let `f : X ⟶ Y` be affine and `τ : f_* L ⟶ G`. If
`f_* Hom(𝒪_X, L) ⟶ Hom(f_* 𝒪_X, G)`, `φ ↦ τ ∘ f_* φ`, is an isomorphism, then so is
`f_* Hom(M, L) ⟶ Hom(f_* M, G)` for every finite locally free `M`. -/
theorem isIso_pushforwardHomObjComparison_of_isIso_unit [IsAffineHom f]
    (hτ : IsIso (pushforwardHomObjComparison f τ (SheafOfModules.unit X.ringCatSheaf)))
    (M : X.Modules) [M.IsFiniteLocallyFree] : IsIso (pushforwardHomObjComparison f τ M) := by
  refine isIso_of_bijective_app_of_isAffineOpen _ fun V hV ↦ ?_
  obtain ⟨n, ξ, m, h⟩ := exists_sum_comp_eq_id_over M (hV.preimage f)
  have hN : Function.Bijective
      (pushforwardHomObjComparisonApp f τ (SheafOfModules.unit X.ringCatSheaf) V) :=
    ConcreteCategory.bijective_of_isIso
      (Hom.app (pushforwardHomObjComparison f τ (SheafOfModules.unit X.ringCatSheaf)) V)
  have h' := congrArg (fun g ↦ (SheafOfModules.forget _).map g) h
  simp only [Functor.map_sum, Functor.map_comp] at h'
  exact bijective_pushforwardHomObjComparisonApp_of_sum_comp_eq_id M V
    (fun j ↦ (SheafOfModules.forget _).map (ξ j)) (fun j ↦ (SheafOfModules.forget _).map (m j))
    h' hN

end Retract

end AlgebraicGeometry.Scheme.Modules

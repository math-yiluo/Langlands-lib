/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import WeilConjectures.AlgebraicGeometry.Modules.FpqcSections

/-!
# The étale sheaf attached to a quasi-coherent module

Let `F` be an `𝒪_X`-module. The presheaf `F_ét` on the small étale site of `X` sends an étale
`X`-scheme `u : U ⟶ X` to the group `Γ(U, u^* F)`, with the pullback restrictions. We realise
the sections over `U` as the morphisms `u^* 𝒪_X ⟶ u^* F` of `𝒪_U`-modules, i.e. as the étale
presheaf `AlgebraicGeometry.Scheme.Modules.etaleHom (𝒪_X) F`; a morphism `φ` corresponds to the
section `φ(u^* 1)` of `u^* F` (`AlgebraicGeometry.Scheme.Modules.etaleSectionsEquiv`), and
restriction corresponds to pullback of sections
(`AlgebraicGeometry.Scheme.Modules.homSection_pullHom`). For quasi-coherent `F`, this presheaf is
a sheaf by fpqc descent of morphisms of quasi-coherent modules.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.etalePresheaf`: the presheaf `F_ét` of abelian groups.
- `AlgebraicGeometry.Scheme.Modules.etaleSheaf`: the sheaf `F_ét`, for quasi-coherent `F`.
- `AlgebraicGeometry.Scheme.Modules.etaleSectionsEquiv`: `F_ét(U) ≃ Γ(U, u^* F)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isSheaf_etalePresheaf`: `F_ét` is a sheaf for quasi-coherent
  `F` (descent for quasi-coherent modules).
-/

@[expose] public section

universe u

open CategoryTheory Opposite Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The functor `X.Etale ⥤ Over X` underlying the étale `X`-schemes. -/
noncomputable abbrev etaleToOver (X : Scheme.{u}) : X.Etale ⥤ Over X :=
  toProEt X ⋙ ProEt.forget X

/-- The group of sections of `F_ét` over an étale `X`-scheme `V`: morphisms
`V^* 𝒪_X ⟶ V^* F` of `𝒪_V`-modules. -/
abbrev EtaleSections (F : X.Modules) (V : X.Etale) : Type u :=
  (pullback V.hom).obj (unit X) ⟶ (pullback V.hom).obj F

/-- Restriction of sections of `F_ét` along a morphism `g : W ⟶ V` of étale `X`-schemes:
`φ ↦ g^* φ`, composed with the identifications `g^* V^* = W^*`. -/
noncomputable def etaleRestrict (F : X.Modules) {V W : X.Etale} (g : W ⟶ V) :
    EtaleSections F V →+ EtaleSections F W where
  toFun φ := (pullbackCompOfEq g.left V.hom W.hom (MorphismProperty.Over.w g) (unit X)).inv ≫
    (pullback g.left).map φ ≫
      (pullbackCompOfEq g.left V.hom W.hom (MorphismProperty.Over.w g) F).hom
  map_zero' := by simp
  map_add' φ ψ := by simp [Preadditive.add_comp, Preadditive.comp_add]

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
lemma etaleRestrict_eq (F : X.Modules) {V W : X.Etale} (g : W ⟶ V) (φ : EtaleSections F V) :
    etaleRestrict F g φ = (etaleHom (X := X) (unitObj X) F).map g.op φ := by
  simp only [etaleHom, Functor.comp_map, Functor.op_map, Pseudofunctor.presheafHom_map,
    TypeCat.ofHom_apply, Quiver.Hom.unop_op]
  rw [modulesPseudofunctor_pullHom_eq_pullbackCompOfEq]
  rfl

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
lemma etaleRestrict_id (F : X.Modules) (V : X.Etale) (φ : EtaleSections F V) :
    etaleRestrict F (𝟙 V) φ = φ :=
  (etaleRestrict_eq F (𝟙 V) φ).trans
    (show (etaleHom (X := X) (unitObj X) F).map (𝟙 (op V)) φ = φ from
      Functor.map_id_apply (F := TypeCat.Fun) (carrier := id) (etaleHom (X := X) (unitObj X) F)
        (op V) φ)

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
lemma etaleRestrict_comp (F : X.Modules) {V W T : X.Etale} (g : W ⟶ V) (f : T ⟶ W)
    (φ : EtaleSections F V) :
    etaleRestrict F (f ≫ g) φ = etaleRestrict F f (etaleRestrict F g φ) :=
  (etaleRestrict_eq F (f ≫ g) φ).trans
    ((show (etaleHom (X := X) (unitObj X) F).map (g.op ≫ f.op) φ = _ from
      Functor.map_comp_apply (F := TypeCat.Fun) (carrier := id)
        (etaleHom (X := X) (unitObj X) F) g.op f.op φ).trans
      ((etaleRestrict_eq F f _).trans
        (congrArg (fun x ↦ (etaleHom (X := X) (unitObj X) F).map f.op x)
          (etaleRestrict_eq F g φ))).symm)

/-- **The étale sheaf `F_ét` of an `𝒪_X`-module `F`**, as a presheaf of abelian groups on the
small étale site: `u: U ⟶ X` is sent to (the group of morphisms `u^* 𝒪_X ⟶ u^* F`, identified
with) `Γ(U, u^* F)`, with the pullback restrictions. The sections are lifted to the universe
`u + 1` of sheaves on the small étale site. -/
noncomputable def etalePresheaf (F : X.Modules) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj V := AddCommGrpCat.of (ULift.{u + 1} (EtaleSections F V.unop))
  map g := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((etaleRestrict F g.unop).comp AddEquiv.ulift.toAddMonoidHom))
  map_id V := by
    refine AddCommGrpCat.ext fun φ ↦ ?_
    exact congrArg ULift.up (etaleRestrict_id F V.unop φ.down)
  map_comp f g := by
    refine AddCommGrpCat.ext fun φ ↦ ?_
    exact congrArg ULift.up (etaleRestrict_comp F f.unop g.unop φ.down)

lemma etalePresheaf_map_apply (F : X.Modules) {V W : X.Etale} (g : W ⟶ V)
    (φ : (etalePresheaf F).obj (op V)) :
    ((etalePresheaf F).map g.op φ).down = etaleRestrict F g φ.down :=
  rfl

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
/-- **Descent for quasi-coherent modules**: for a quasi-coherent `𝒪_X`-module `F`, the presheaf
`u ↦ Γ(U, u^* F)` on the small étale site is a sheaf. -/
theorem isSheaf_etalePresheaf (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf X.smallEtaleTopology (etalePresheaf F) := by
  have : ((F : modulesPseudofunctor.obj (.mk (op X))) : X.Modules).IsQuasicoherent :=
    inferInstanceAs F.IsQuasicoherent
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat.{u + 1}),
    isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv (P₁ := etaleHom (X := X) (unitObj X) F)
    (fun _ ↦ Equiv.ulift.symm) (fun V W g x ↦ ?_)
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_etaleHom (unitObj X) F))
  exact congrArg ULift.up (etaleRestrict_eq F g x).symm

/-- **The étale sheaf `F_ét` of a quasi-coherent `𝒪_X`-module `F`**: `u: U ⟶ X` is sent to
`Γ(U, u^* F)` (realised as morphisms `u^* 𝒪_X ⟶ u^* F`, see
`AlgebraicGeometry.Scheme.Modules.etaleSectionsEquiv`). -/
noncomputable def etaleSheaf (F : X.Modules) [F.IsQuasicoherent] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨etalePresheaf F, isSheaf_etalePresheaf F⟩

/-- The sections of `F_ét` over `u : U ⟶ X` are the global sections of `u^* F`: a morphism
`φ : u^* 𝒪_X ⟶ u^* F` corresponds to `φ(u^* 1)`. -/
noncomputable def etaleSectionsEquiv (F : X.Modules) (V : X.Etale) :
    EtaleSections F V ≃+ Γ((pullback V.hom).obj F, V.hom ⁻¹ᵁ ⊤) :=
  AddEquiv.ofBijective
    ({ toFun := homSection V.hom
       map_zero' := rfl
       map_add' _ _ := rfl } : EtaleSections F V →+ Γ((pullback V.hom).obj F, V.hom ⁻¹ᵁ ⊤))
    ⟨homSection_injective V.hom, homSection_surjective V.hom⟩

lemma etaleSectionsEquiv_apply (F : X.Modules) (V : X.Etale) (φ : EtaleSections F V) :
    etaleSectionsEquiv F V φ = homSection V.hom φ :=
  rfl

end AlgebraicGeometry.Scheme.Modules

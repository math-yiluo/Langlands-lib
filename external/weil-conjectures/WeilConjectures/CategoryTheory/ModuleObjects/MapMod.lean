/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!

# Module objects under a lax monoidal functor, and monoidal adjunctions

Let `F : C ⥤ D` be a lax monoidal functor between monoidal categories and `R : C` an algebra
object, so that `F.obj R` is an algebra object of `D` (`Functor.monObjObj`, a scoped instance of
`CategoryTheory.Obj`). The induced functor
`Functor.mapMod F R : Mod C R ⥤ Mod D (F.obj R)` and the module structure `Functor.modObjObj` on
`F.obj M` are defined in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`; here
`Functor.modObjObj` is made a scoped instance of `CategoryTheory.Obj`, and:

* `Functor.mapMod` commutes with the forgetful functors (`Functor.mapMod_comp_forget`) and with
  restriction of scalars (`Functor.mapModComapIso`), sends the regular module to the regular
  module (`Functor.mapModRegularIso`), and is exact when `F` is.
* `Functor.mapModCompIso`: for a monoidal natural isomorphism `τ : F ⋙ G ⟶ H`, transporting
  module objects along `F` and then `G` is transporting them along `H` and restricting scalars
  along `τ.app R`.

The second part concerns a *monoidal adjunction* `adj : F ⊣ G` in the sense of mathlib
(`Adjunction.IsMonoidal`: `F` is strong monoidal, `G` is lax monoidal, and the two structures
are mates). The unit `R ⟶ G.obj (F.obj R)` is then a morphism of algebra objects
(`Adjunction.isMonHom_unit_app`), and the adjunction lifts to module objects:
```
Adjunction.mapModAdjunction adj R : F.mapMod ⊣ G.mapMod ⋙ Mod.comap (adj.unit.app R)
```
(an `F.obj R`-linear map `F.obj M ⟶ N` is the same as an `R`-linear map `M ⟶ G.obj N`, where
`R` acts on `G.obj N` through the unit). The lift of `adj` is the elementary input for the
adjunction `f^* ⊣ f_*` on module objects over a coefficient ring sheaf, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory MonObj Limits Functor.LaxMonoidal

namespace CategoryTheory

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-! ### The functor `mapMod` -/

namespace Functor

section MapMod

variable (F : C ⥤ D) [F.LaxMonoidal] {R : C} [MonObj R]

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.modObjObj

lemma modObjObj_smul (M : C) [ModObj R M] :
    γ[F.obj R, F.obj M] = Functor.LaxMonoidal.μ F R M ≫ F.map γ[R,M] := rfl

lemma mapMod_obj_smul (M : Mod C R) :
    γ[F.obj R, ((F.mapMod R).obj M).X] =
      Functor.LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] := rfl

/-- `mapMod` commutes with the forgetful functors. -/
lemma mapMod_comp_forget : F.mapMod R ⋙ Mod.forget (F.obj R) = Mod.forget R ⋙ F := rfl


instance faithful_mapMod [F.Faithful] : (F.mapMod R).Faithful where
  map_injective h := Mod.hom_ext _ _ (F.map_injective congr(($h).hom))

section Comap

variable {S : C} [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- `mapMod` commutes with restriction of scalars: the `F.obj R`-module objects
`F.obj (N with scalars restricted along φ)` and `(F.obj N) with scalars restricted along
F.map φ` coincide. -/
@[simps!]
def mapModComapIso : Mod.comap φ ⋙ F.mapMod R ≅ F.mapMod S ⋙ Mod.comap (F.map φ) :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    change Functor.LaxMonoidal.μ F R N.X ≫ F.map (φ ▷ N.X ≫ γ[S,N.X]) =
      F.map φ ▷ F.obj N.X ≫ Functor.LaxMonoidal.μ F S N.X ≫ F.map γ[S,N.X]
    rw [F.map_comp, μ_natural_left_assoc])) (fun _ ↦ by ext; simp)

end Comap

variable (R) in
/-- The image of the regular module under a lax monoidal functor `F` is the regular module over
`F R`. -/
noncomputable def mapModRegularIso :
    (F.mapMod R).obj (Mod.regular R : Mod C R) ≅ (Mod.regular (F.obj R) : Mod D (F.obj R)) :=
  Mod.isoMk (Iso.refl (F.obj R)) (by
    erw [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp])

/-! ### Exactness of `mapMod` -/

section Exact

variable [Abelian C] [Abelian D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft (F.obj R))]

/-- If `F` is left exact, then so is `F.mapMod`: finite limits of module objects are computed
in the ambient categories on both sides. -/
instance preservesFiniteLimits_mapMod [PreservesFiniteLimits F] :
    PreservesFiniteLimits (F.mapMod R) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
      inferInstanceAs (PreservesLimitsOfShape J (Mod.forget R ⋙ F))
    have : ReflectsLimitsOfShape J (Mod.forget (F.obj R) : Mod D (F.obj R) ⥤ D) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    preservesLimitsOfShape_of_reflects_of_preserves (F.mapMod R) (Mod.forget (F.obj R))

/-- If `F` is right exact, then so is `F.mapMod`: finite colimits of module objects are
computed in the ambient categories on both sides. -/
instance preservesFiniteColimits_mapMod [PreservesFiniteColimits F] :
    PreservesFiniteColimits (F.mapMod R) where
  preservesFiniteColimits J _ _ :=
    have : PreservesColimitsOfShape J (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape J (Mod.forget R ⋙ F))
    have : ReflectsColimitsOfShape J (Mod.forget (F.obj R) : Mod D (F.obj R) ⥤ D) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves (F.mapMod R) (Mod.forget (F.obj R))

end Exact

end MapMod

/-! ### Identity and composition -/

section Comp

variable (F : C ⥤ D) (G : D ⥤ E) [F.LaxMonoidal] [G.LaxMonoidal] (R : C) [MonObj R]

/-- The algebra object `(𝟭 C).obj R = R` obtained from the lax monoidal structure of the
identity functor is `R`. -/
lemma monObjObj_id : (𝟭 C).monObjObj R = ‹MonObj R› :=
  MonObj.ext _ _ (by
    change Functor.LaxMonoidal.μ (𝟭 C) R R ≫ (𝟭 C).map μ[R] = μ[R]
    simp)

/-- The algebra object `(F ⋙ G).obj R` is `G.obj (F.obj R)`, with the algebra structure
transported in two steps. -/
lemma monObjObj_comp : (F ⋙ G).monObjObj R = G.monObjObj (F.obj R) :=
  MonObj.ext _ _ (by
    change Functor.LaxMonoidal.μ (F ⋙ G) R R ≫ (F ⋙ G).map μ[R] =
      Functor.LaxMonoidal.μ G (F.obj R) (F.obj R) ≫ G.map (Functor.LaxMonoidal.μ F R R ≫ F.map μ[R])
    rw [comp_μ, Functor.comp_map, Category.assoc, G.map_comp])

end Comp

end Functor

/-! ### Change of scalars along an isomorphism -/

namespace Mod

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

/-- Restriction of scalars along an isomorphism of algebra objects is an equivalence, with
inverse the restriction of scalars along the inverse isomorphism. -/
noncomputable def comapEquivalenceOfIsIso : Mod C S ≌ Mod C R :=
  Equivalence.mk (comap φ) (comap (asIso φ).inv)
    ((comapId S).symm ≪≫ comapCongr (by simp) ≪≫ comapComp (asIso φ).inv φ)
    ((comapComp φ (asIso φ).inv).symm ≪≫ comapCongr (by simp) ≪≫ comapId R)

/-- Extension of scalars along an isomorphism of algebra objects is restriction of scalars
along the inverse isomorphism, by uniqueness of left adjoints. -/
noncomputable def extendScalarsIsoComapInv : extendScalars φ ≅ comap (asIso φ).inv :=
  (extendRestrictAdjunction φ).leftAdjointUniq (comapEquivalenceOfIsIso φ).symm.toAdjunction

/-- Coextension of scalars along an isomorphism of algebra objects is restriction of scalars
along the inverse isomorphism, by uniqueness of right adjoints. -/
noncomputable def coextendScalarsIsoComapInv : coextendScalars φ ≅ comap (asIso φ).inv :=
  (restrictCoextendAdjunction φ).rightAdjointUniq (comapEquivalenceOfIsIso φ).toAdjunction

/-- Along an isomorphism of algebra objects, extension and coextension of scalars agree: both
are the restriction of scalars along the inverse isomorphism. -/
noncomputable def extendScalarsIsoCoextendScalars : extendScalars φ ≅ coextendScalars φ :=
  extendScalarsIsoComapInv φ ≪≫ (coextendScalarsIsoComapInv φ).symm

end Mod

/-! ### Transport of `IsMonHom` along equalities of algebra object structures -/

/-- An algebra object morphism remains one when the algebra object structures of its source and
target are replaced by equal ones. -/
lemma IsMonHom.of_eq {M N : C} {h₁ h₁' : MonObj M} {h₂ h₂' : MonObj N} (f : M ⟶ N)
    (e₁ : h₁ = h₁') (e₂ : h₂ = h₂') [hf : @IsMonHom _ _ _ M N h₁ h₂ f] :
    @IsMonHom _ _ _ M N h₁' h₂' f := by
  subst e₁ e₂
  exact hf

/-! ### Monoidal adjunctions on module objects -/

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (R : C) [MonObj R]

/-- The unit of a monoidal adjunction at an algebra object `R`, as a morphism
`R ⟶ G.obj (F.obj R)` whose target carries the algebra object structure transported first along
`F` and then along `G`. It is an `abbrev` of `adj.unit.app R`, with its type spelled out so that
the algebra object structures on its source and target are the intended ones. -/
abbrev unitAlgHom : R ⟶ G.obj (F.obj R) := adj.unit.app R

/-- The counit of a monoidal adjunction at an algebra object `S`, as a morphism
`F.obj (G.obj S) ⟶ S`, see `Adjunction.unitAlgHom`. -/
abbrev counitAlgHom (S : D) [MonObj S] : F.obj (G.obj S) ⟶ S := adj.counit.app S

/-- The unit `R ⟶ G.obj (F.obj R)` of a monoidal adjunction at an algebra object `R` is a
morphism of algebra objects. -/
instance isMonHom_unitAlgHom : IsMonHom (adj.unitAlgHom R) :=
  IsMonHom.of_eq (h₁ := (𝟭 C).monObjObj R) (h₂ := (F ⋙ G).monObjObj R) (adj.unit.app R)
    (Functor.monObjObj_id R) (Functor.monObjObj_comp F G R)

/-- The counit `F.obj (G.obj S) ⟶ S` of a monoidal adjunction at an algebra object `S` is a
morphism of algebra objects. -/
instance isMonHom_counitAlgHom (S : D) [MonObj S] : IsMonHom (adj.counitAlgHom S) :=
  IsMonHom.of_eq (h₁ := (G ⋙ F).monObjObj S) (h₂ := (𝟭 D).monObjObj S) (adj.counit.app S)
    (Functor.monObjObj_comp G F S) (Functor.monObjObj_id S)

open Functor.OplaxMonoidal Functor.Monoidal

section HomEquiv

variable {R} (M : Mod C R) (N : Mod D (F.obj R))

/-- The `R`-linearity of the adjoint `M ⟶ G.obj N` of an `F.obj R`-linear map
`F.obj M ⟶ N`, where `R` acts on `G.obj N` through the unit. -/
lemma mapMod_homEquiv_smul_hom (φ : (F.mapMod R).obj M ⟶ N) :
    γ[R,M.X] ≫ adj.homEquiv M.X N.X φ.hom =
      R ◁ adj.homEquiv M.X N.X φ.hom ≫
        γ[R,((G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)).obj N).X] := by
  have hφ : F.map γ[R,M.X] ≫ φ.hom =
      Functor.OplaxMonoidal.δ F R M.X ≫ F.obj R ◁ φ.hom ≫ γ[F.obj R,N.X] := by
    rw [← Mod.act_hom φ, Mod.act, F.mapMod_obj_smul, ← Category.assoc, ← Category.assoc,
      Functor.Monoidal.δ_μ, Category.id_comp]
  change _ = _ ≫ adj.unit.app R ▷ G.obj N.X ≫
    Functor.LaxMonoidal.μ G (F.obj R) N.X ≫ G.map γ[F.obj R,N.X]
  rw [homEquiv_unit, ← adj.unit_naturality_assoc, ← G.map_comp, hφ,
    G.map_comp, G.map_comp]
  erw [adj.unit_app_tensor_comp_map_δ_assoc]
  rw [← μ_natural_right_assoc,
    tensorHom_def', Category.assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    ← whisker_exchange_assoc]

/-- The `F.obj R`-linearity of the adjoint `F.obj M ⟶ N` of an `R`-linear map `M ⟶ G.obj N`,
where `R` acts on `G.obj N` through the unit. -/
lemma mapMod_homEquiv_symm_smul_hom
    (ψ : M ⟶ (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)).obj N) :
    γ[F.obj R,((F.mapMod R).obj M).X] ≫ (adj.homEquiv M.X N.X).symm ψ.hom =
      F.obj R ◁ (adj.homEquiv M.X N.X).symm ψ.hom ≫ γ[F.obj R,N.X] := by
  have hψ : γ[R,M.X] ≫ ψ.hom = (adj.unit.app R ⊗ₘ ψ.hom) ≫
      Functor.LaxMonoidal.μ G (F.obj R) N.X ≫ G.map γ[F.obj R,N.X] := by
    rw [Mod.act_hom, tensorHom_def', Category.assoc]
    rfl
  rw [homEquiv_counit, F.mapMod_obj_smul, Category.assoc, ← F.map_comp_assoc, hψ, F.map_comp,
    F.map_comp, Category.assoc, Category.assoc, adj.counit_naturality,
    adj.map_μ_comp_counit_app_tensor_assoc, ← μ_natural_assoc]
  erw [Functor.Monoidal.μ_δ_assoc]
  rw [tensorHom_comp_tensorHom_assoc, left_triangle_components,
    id_tensorHom]

end HomEquiv

/-- A monoidal adjunction `F ⊣ G` lifts to module objects: an `F.obj R`-linear map
`F.obj M ⟶ N` is the same as an `R`-linear map `M ⟶ G.obj N`, where `R` acts on `G.obj N`
through the unit `R ⟶ G.obj (F.obj R)`. -/
noncomputable def mapModAdjunction :
    F.mapMod R ⊣ G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun φ := Mod.Hom.mk' (adj.homEquiv M.X N.X φ.hom) (adj.mapMod_homEquiv_smul_hom M N φ)
          invFun ψ := Mod.Hom.mk' ((adj.homEquiv M.X N.X).symm ψ.hom)
            (adj.mapMod_homEquiv_symm_smul_hom M N ψ)
          left_inv φ := by ext; simp
          right_inv ψ := by ext; simp }
      homEquiv_naturality_left_symm _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_right _ _) }

@[simp]
lemma mapModAdjunction_unit_app_hom (M : Mod C R) :
    ((adj.mapModAdjunction R).unit.app M).hom = adj.unit.app M.X := by
  simp only [mapModAdjunction, Adjunction.mkOfHomEquiv_unit_app]
  exact adj.homEquiv_id M.X

@[simp]
lemma mapModAdjunction_counit_app_hom (N : Mod D (F.obj R)) :
    ((adj.mapModAdjunction R).counit.app N).hom = adj.counit.app N.X := by
  simp only [mapModAdjunction, Adjunction.mkOfHomEquiv_counit_app]
  exact adj.homEquiv_symm_id N.X

end Adjunction

/-! ### Module objects under a composition of lax monoidal functors -/

namespace Functor

variable (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
  (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ] (R : C) [MonObj R]

/-- The component at an algebra object `R` of a monoidal natural transformation
`τ : F ⋙ G ⟶ H`, as a morphism `G.obj (F.obj R) ⟶ H.obj R` whose source carries the algebra
object structure transported first along `F` and then along `G`. It is an `abbrev` of
`τ.app R`, see `Adjunction.unitAlgHom`. -/
abbrev compAlgHom : G.obj (F.obj R) ⟶ H.obj R := τ.app R

/-- The component `G.obj (F.obj R) ⟶ H.obj R` of a monoidal natural transformation
`τ : F ⋙ G ⟶ H` is a morphism of algebra objects. -/
instance isMonHom_compAlgHom : IsMonHom (compAlgHom F G τ R) :=
  IsMonHom.of_eq (h₁ := (F ⋙ G).monObjObj R) (h₂ := H.monObjObj R) (τ.app R)
    (Functor.monObjObj_comp F G R) rfl

variable [IsIso τ]

/-- `mapMod` of a composition: for a monoidal natural isomorphism `τ : F ⋙ G ⟶ H` of lax
monoidal functors, transporting an `R`-module object first along `F` and then along `G` is
transporting it along `H` and restricting scalars along `τ.app R`. -/
@[simps!]
noncomputable def mapModCompIso :
    F.mapMod R ⋙ G.mapMod (F.obj R) ≅ H.mapMod R ⋙ Mod.comap (compAlgHom F G τ R) :=
  NatIso.ofComponents (fun M ↦ Mod.isoMk (asIso (τ.app M.X)) (by
    change (Functor.LaxMonoidal.μ G (F.obj R) (F.obj M.X) ≫
        G.map (Functor.LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X])) ≫ τ.app M.X =
      G.obj (F.obj R) ◁ τ.app M.X ≫ τ.app R ▷ H.obj M.X ≫ Functor.LaxMonoidal.μ H R M.X ≫
        H.map γ[R,M.X]
    have h₁ : (F ⋙ G).map γ[R,M.X] ≫ τ.app M.X = τ.app (R ⊗ M.X) ≫ H.map γ[R,M.X] :=
      τ.naturality γ[R,M.X]
    have h₂ := NatTrans.IsMonoidal.tensor (τ := τ) R M.X
    rw [comp_μ] at h₂
    rw [whisker_exchange_assoc, ← tensorHom_def_assoc, ← reassoc_of% h₂, ← h₁, G.map_comp,
      Category.assoc, Category.assoc]
    rfl)) (fun f ↦ by ext; exact τ.naturality f.hom)

end Functor

end CategoryTheory

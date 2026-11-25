/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!

# The projection formula and the linearization of an exceptional adjunction

Let `S : D ⥤ C` be a strong monoidal functor between monoidal categories (`f^*` in a
six-functor formalism) and `P : C ⥤ D` a functor (`f_!`). A *projection formula* for `P`
relative to `S` is a family of isomorphisms
```
PF_{L,M} : P (S L ⊗ M) ≅ L ⊗ P M
```
natural in `L` and `M` and compatible with the unit and the associativity constraints of `S`
(`Functor.ProjectionFormula`). The main case is `P` left adjoint to `S` itself (`j_! ⊣ j^*` for
an open immersion `j`): the projection formula map is then canonical, the adjoint of
`S L ⊗ M ⟶ S L ⊗ S P M ⟶ S (L ⊗ P M)` (`Adjunction.projectionFormulaMap`), its coherences are
formal consequences of the monoidal structure of `S`, and the projection formula is the
statement that it is an isomorphism (`Adjunction.HasProjectionFormula`,
`Adjunction.projectionFormula`). In general (`f_!` and `f^*` for a morphism `f`), the coherent
projection formula is part of the data of the six-functor formalism.

A projection formula *linearizes* `P` and any right adjoint `G` of `P` to module objects, for
every algebra object `B : D`:

* **Linearize `P`.** An `S B`-module object `M` makes `P M` a `B`-module object, with action
  ```
  B ⊗ P M ≅ P (S B ⊗ M) ⟶ P M
  ```
  (`Functor.ProjectionFormula.modObj`), giving `Functor.ProjectionFormula.mapModLeft pf B :
  Mod C (S.obj B) ⥤ Mod D B`, written `P_B`. It commutes with the forgetful functors and is
  exact when `P` is.
* **Linearize `G`.** For an adjunction `adj : P ⊣ G`, the mate of the projection formula is
  the natural map
  ```
  θ_{L,N} : S L ⊗ G N ⟶ G (L ⊗ N),
  ```
  adjoint to `P (S L ⊗ G N) ≅ L ⊗ P G N ⟶ L ⊗ N` (`Functor.ProjectionFormula.theta`). It is
  natural and compatible with the unit and the associativity constraints, and for a `B`-module
  object `N` the composite `S B ⊗ G N ⟶ G (B ⊗ N) ⟶ G N` makes `G N` an `S B`-module object
  (`Functor.ProjectionFormula.rightModObj`), giving
  `Functor.ProjectionFormula.mapModRight pf adj B : Mod D B ⥤ Mod C (S.obj B)`, written `G_B`.
* **The adjunction `P_B ⊣ G_B`** (`Functor.ProjectionFormula.mapModAdjunction`): a `B`-linear
  map `P M ⟶ N` is the same as an `S B`-linear map `M ⟶ G N`, the projection formula being
  exactly what transposes the two linearities along `adj`.

When `G = S`, the map `θ` is the lax structure `μ S` of `S`, so that `G_B` is the transport
`S.mapMod` of module objects along `S`; this is `Adjunction.mapModLeftAdjunction`.

Combined with the change of scalars of
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, this gives the exceptional
operations on module objects over a coefficient ring sheaf, `f_! = P_B ∘ Res_{α_f}` and
`f^! = Coext_{α_f} ∘ G_B`, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Limits Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-! ### Projection formulas -/

/-- A *projection formula* for a functor `P : C ⥤ D` relative to a strong monoidal functor
`S : D ⥤ C`: natural isomorphisms `P (S L ⊗ M) ≅ L ⊗ P M`, compatible with the unit and the
associativity constraints of `S`. -/
structure Functor.ProjectionFormula (S : D ⥤ C) [S.Monoidal] (P : C ⥤ D) where
  /-- The projection formula isomorphism `P (S L ⊗ M) ≅ L ⊗ P M`. -/
  iso (L : D) (M : C) : P.obj (S.obj L ⊗ M) ≅ L ⊗ P.obj M
  /-- Naturality in `L`. -/
  natural_left {L L' : D} (f : L ⟶ L') (M : C) :
    P.map (S.map f ▷ M) ≫ (iso L' M).hom = (iso L M).hom ≫ f ▷ P.obj M
  /-- Naturality in `M`. -/
  natural_right (L : D) {M M' : C} (g : M ⟶ M') :
    P.map (S.obj L ◁ g) ≫ (iso L M').hom = (iso L M).hom ≫ L ◁ P.map g
  /-- Compatibility with the unit: for `L = 𝟙`, the projection formula is the identification
  `P (S 𝟙 ⊗ M) ≅ P M ≅ 𝟙 ⊗ P M`. -/
  unit (M : C) :
    (iso (𝟙_ D) M).hom ≫ (λ_ (P.obj M)).hom = P.map (Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom)
  /-- Compatibility with the associativity constraints. -/
  assoc (L L' : D) (M : C) :
    (iso (L ⊗ L') M).hom ≫ (α_ L L' (P.obj M)).hom =
      P.map (δ S L L' ▷ M ≫ (α_ (S.obj L) (S.obj L') M).hom) ≫
        (iso L (S.obj L' ⊗ M)).hom ≫ L ◁ (iso L' M).hom

attribute [reassoc] Functor.ProjectionFormula.natural_left Functor.ProjectionFormula.natural_right
  Functor.ProjectionFormula.unit Functor.ProjectionFormula.assoc

/-! ### The projection formula map of an adjunction `P ⊣ S` -/

namespace Adjunction

variable {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.Monoidal]

/-- The projection formula map `P (S L ⊗ M) ⟶ L ⊗ P M` of an adjunction `P ⊣ S` with `S`
monoidal: the adjoint of `S L ⊗ M ⟶ S L ⊗ S P M ⟶ S (L ⊗ P M)`. -/
noncomputable def projectionFormulaMap (L : D) (M : C) : P.obj (S.obj L ⊗ M) ⟶ L ⊗ P.obj M :=
  (adj.homEquiv _ _).symm (S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M))

lemma homEquiv_projectionFormulaMap (L : D) (M : C) :
    adj.homEquiv _ _ (adj.projectionFormulaMap L M) =
      S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M) := by
  simp [projectionFormulaMap]

/-- The projection formula map is natural in `L`. -/
@[reassoc]
lemma projectionFormulaMap_natural_left {L L' : D} (f : L ⟶ L') (M : C) :
    P.map (S.map f ▷ M) ≫ adj.projectionFormulaMap L' M =
      adj.projectionFormulaMap L M ≫ f ▷ P.obj M := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_projectionFormulaMap,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_left, ← whisker_exchange_assoc]
  rfl

/-- The projection formula map is natural in `M`. -/
@[reassoc]
lemma projectionFormulaMap_natural_right (L : D) {M M' : C} (g : M ⟶ M') :
    P.map (S.obj L ◁ g) ≫ adj.projectionFormulaMap L M' =
      adj.projectionFormulaMap L M ≫ L ◁ P.map g := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_projectionFormulaMap,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_right,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [adj.unit_naturality]

/-- The projection formula map is compatible with the unit: for `L = 𝟙`, it is the
identification `P (S 𝟙 ⊗ M) ≅ P M ≅ 𝟙 ⊗ P M`. -/
@[reassoc]
lemma projectionFormulaMap_unit (M : C) :
    adj.projectionFormulaMap (𝟙_ D) M ≫ (λ_ (P.obj M)).hom =
      P.map (Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom) := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_right, homEquiv_projectionFormulaMap, ← Category.comp_id (P.map _),
    homEquiv_naturality_left, homEquiv_id, Category.assoc,
    ← Category.id_comp (Functor.LaxMonoidal.μ S (𝟙_ D) _),
    ← Functor.Monoidal.whiskerRight_η_ε (F := S), Category.assoc, Category.assoc,
    ← Functor.LaxMonoidal.left_unitality]
  erw [whisker_exchange_assoc, leftUnitor_naturality]
  simp only [Category.assoc]
  rfl

/-- The projection formula map is compatible with the associativity constraints. -/
@[reassoc]
lemma projectionFormulaMap_assoc (L L' : D) (M : C) :
    adj.projectionFormulaMap (L ⊗ L') M ≫ (α_ L L' (P.obj M)).hom =
      P.map (δ S L L' ▷ M ≫ (α_ (S.obj L) (S.obj L') M).hom) ≫
        adj.projectionFormulaMap L (S.obj L' ⊗ M) ≫ L ◁ adj.projectionFormulaMap L' M := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_right, homEquiv_naturality_left, homEquiv_naturality_right,
    homEquiv_projectionFormulaMap, homEquiv_projectionFormulaMap]
  simp only [Category.assoc]
  rw [← μ_natural_right, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [← adj.homEquiv_unit, homEquiv_projectionFormulaMap]
  rw [← cancel_epi (Functor.LaxMonoidal.μ S L L' ▷ M), Functor.Monoidal.whiskerRight_μ_δ_assoc]
  erw [← whisker_exchange_assoc, Functor.LaxMonoidal.associativity,
    associator_naturality_right_assoc]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]

/-- An adjunction `P ⊣ S` with `S` monoidal *satisfies the projection formula* if the
projection formula maps `P (S L ⊗ M) ⟶ L ⊗ P M` are isomorphisms. -/
class HasProjectionFormula : Prop where
  isIso (L : D) (M : C) : IsIso (adj.projectionFormulaMap L M)

attribute [instance] HasProjectionFormula.isIso

/-- The projection formula of an adjunction `P ⊣ S` with `S` monoidal satisfying the
projection formula. -/
@[simps]
noncomputable def projectionFormula [adj.HasProjectionFormula] : S.ProjectionFormula P where
  iso L M := asIso (adj.projectionFormulaMap L M)
  natural_left := adj.projectionFormulaMap_natural_left
  natural_right := adj.projectionFormulaMap_natural_right
  unit := adj.projectionFormulaMap_unit
  assoc := adj.projectionFormulaMap_assoc

end Adjunction

namespace Functor.ProjectionFormula

open Adjunction

variable {S : D ⥤ C} [S.Monoidal] {P : C ⥤ D} (pf : S.ProjectionFormula P)

@[reassoc]
lemma whiskerRight_iso_inv {L L' : D} (f : L ⟶ L') (M : C) :
    f ▷ P.obj M ≫ (pf.iso L' M).inv = (pf.iso L M).inv ≫ P.map (S.map f ▷ M) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← pf.natural_left, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

@[reassoc]
lemma whiskerLeft_iso_inv (L : D) {M M' : C} (g : M ⟶ M') :
    L ◁ P.map g ≫ (pf.iso L M').inv = (pf.iso L M).inv ≫ P.map (S.obj L ◁ g) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← pf.natural_right, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-! ### Linearization of `P` -/

section MapModLeft

variable (B : D) [MonObj B]

/-- The action of `B` on `P M` for an `S B`-module object `M`, through the projection formula:
`B ⊗ P M ≅ P (S B ⊗ M) ⟶ P M`. -/
noncomputable def smul (M : C) [ModObj (S.obj B) M] : B ⊗ P.obj M ⟶ P.obj M :=
  (pf.iso B M).inv ≫ P.map γ[S.obj B,M]

@[reassoc]
lemma iso_hom_smul (M : C) [ModObj (S.obj B) M] :
    (pf.iso B M).hom ≫ pf.smul B M = P.map γ[S.obj B,M] := by
  simp [smul]

/-- For an `S B`-module object `M`, `P M` is a `B`-module object through the projection
formula. -/
@[instance_reducible]
noncomputable def modObj (M : C) [ModObj (S.obj B) M] : ModObj B (P.obj M) where
  smul := pf.smul B M
  one_smul := by
    change η[B] ▷ P.obj M ≫ pf.smul B M = (λ_ (P.obj M)).hom
    have h : S.map η[B] ▷ M ≫ γ[S.obj B,M] = Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom := by
      rw [← ModObj.one_smul_self (S.obj B) M, Functor.obj.η_def, comp_whiskerRight,
        Category.assoc, ← Category.assoc (Functor.OplaxMonoidal.η S ▷ M),
        Functor.Monoidal.whiskerRight_η_ε, Category.id_comp]
    rw [smul, whiskerRight_iso_inv_assoc, ← P.map_comp, h, ← pf.unit, Iso.inv_hom_id_assoc]
  mul_smul := by
    change μ[B] ▷ P.obj M ≫ pf.smul B M =
      (α_ B B (P.obj M)).hom ≫ B ◁ pf.smul B M ≫ pf.smul B M
    have h : S.map μ[B] ▷ M ≫ γ[S.obj B,M] = (δ S B B ▷ M ≫ (α_ _ _ _).hom) ≫
        S.obj B ◁ γ[S.obj B,M] ≫ γ[S.obj B,M] := by
      rw [Category.assoc, ← ModObj.mul_smul_self (S.obj B) M, Functor.obj.μ_def,
        comp_whiskerRight, Category.assoc, ← Category.assoc (δ S B B ▷ M),
        Functor.Monoidal.whiskerRight_δ_μ, Category.id_comp]
    have h' : (pf.iso (B ⊗ B) M).inv ≫ P.map (δ S B B ▷ M ≫ (α_ (S.obj B) (S.obj B) M).hom) =
        (α_ B B (P.obj M)).hom ≫ B ◁ (pf.iso B M).inv ≫ (pf.iso B (S.obj B ⊗ M)).inv := by
      rw [Iso.inv_comp_eq, pf.assoc_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.hom_inv_id,
        Category.comp_id]
    rw [smul, whiskerRight_iso_inv_assoc, ← P.map_comp, h, P.map_comp, ← Category.assoc, h',
      P.map_comp]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, whiskerLeft_iso_inv_assoc]

lemma modObj_smul (M : C) [ModObj (S.obj B) M] : (pf.modObj B M).smul = pf.smul B M := rfl


/-- The linearization `P_B : Mod C (S B) ⥤ Mod D B` of `P`: an `S B`-module object `M` is sent
to `P M` with the `B`-action induced by the projection formula. -/
noncomputable def mapModLeft : Mod C (S.obj B) ⥤ Mod D B where
  obj M := letI := pf.modObj B M.X; ⟨P.obj M.X⟩
  map {M N} f :=
    letI := pf.modObj B M.X
    letI := pf.modObj B N.X
    Mod.Hom.mk' (P.map f.hom) (by
      change pf.smul B M.X ≫ P.map f.hom = B ◁ P.map f.hom ≫ pf.smul B N.X
      rw [smul, smul, Category.assoc, ← P.map_comp, Mod.act_hom, P.map_comp,
        whiskerLeft_iso_inv_assoc])
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

lemma mapModLeft_obj_X (M : Mod C (S.obj B)) : ((pf.mapModLeft B).obj M).X = P.obj M.X := rfl


lemma mapModLeft_map_hom {M N : Mod C (S.obj B)} (f : M ⟶ N) :
    ((pf.mapModLeft B).map f).hom = P.map f.hom := rfl

lemma mapModLeft_obj_smul (M : Mod C (S.obj B)) :
    γ[B,((pf.mapModLeft B).obj M).X] = pf.smul B M.X := rfl


/-- The linearization of `P` commutes with the forgetful functors. -/
lemma mapModLeft_comp_forget : pf.mapModLeft B ⋙ Mod.forget B = Mod.forget (S.obj B) ⋙ P := rfl

section Preadditive

variable [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [P.Additive]

instance additive_mapModLeft : (pf.mapModLeft B).Additive where
  map_add := by intros; ext; simp [mapModLeft_map_hom]

end Preadditive

section Exact

variable [Abelian C] [Abelian D] [MonoidalPreadditive C] [MonoidalPreadditive D] [P.Additive]
  [PreservesFiniteColimits (tensorLeft (S.obj B))] [PreservesFiniteColimits (tensorLeft B)]

/-- If `P` is left exact, then so is its linearization: finite limits of module objects are
computed in the ambient categories on both sides. -/
instance preservesFiniteLimits_mapModLeft [PreservesFiniteLimits P] :
    PreservesFiniteLimits (pf.mapModLeft B) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (pf.mapModLeft B ⋙ Mod.forget B) :=
      inferInstanceAs (PreservesLimitsOfShape J (Mod.forget (S.obj B) ⋙ P))
    have : ReflectsLimitsOfShape J (Mod.forget B : Mod D B ⥤ D) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    preservesLimitsOfShape_of_reflects_of_preserves (pf.mapModLeft B) (Mod.forget B)

/-- If `P` is right exact, then so is its linearization. -/
instance preservesFiniteColimits_mapModLeft [PreservesFiniteColimits P] :
    PreservesFiniteColimits (pf.mapModLeft B) where
  preservesFiniteColimits J _ _ :=
    have : PreservesColimitsOfShape J (pf.mapModLeft B ⋙ Mod.forget B) :=
      inferInstanceAs (PreservesColimitsOfShape J (Mod.forget (S.obj B) ⋙ P))
    have : ReflectsColimitsOfShape J (Mod.forget B : Mod D B ⥤ D) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves (pf.mapModLeft B) (Mod.forget B)

end Exact

end MapModLeft

/-! ### The mate of the projection formula and the linearization of a right adjoint -/

section MapModRight

variable {G : D ⥤ C} (adj : P ⊣ G)

/-- The mate `θ_{L,N} : S L ⊗ G N ⟶ G (L ⊗ N)` of the projection formula under an adjunction
`P ⊣ G`: the adjoint of `P (S L ⊗ G N) ≅ L ⊗ P G N ⟶ L ⊗ N`. -/
noncomputable def theta (L N : D) : S.obj L ⊗ G.obj N ⟶ G.obj (L ⊗ N) :=
  adj.homEquiv _ _ ((pf.iso L (G.obj N)).hom ≫ L ◁ adj.counit.app N)

lemma homEquiv_symm_theta (L N : D) :
    (adj.homEquiv _ _).symm (pf.theta adj L N) =
      (pf.iso L (G.obj N)).hom ≫ L ◁ adj.counit.app N := by
  simp [theta]

@[reassoc]
lemma map_theta_comp_counit (L N : D) :
    P.map (pf.theta adj L N) ≫ adj.counit.app (L ⊗ N) =
      (pf.iso L (G.obj N)).hom ≫ L ◁ adj.counit.app N := by
  have := pf.homEquiv_symm_theta adj L N
  rwa [adj.homEquiv_counit] at this

/-- `θ` is natural in `L`. -/
@[reassoc]
lemma theta_natural_left {L L' : D} (f : L ⟶ L') (N : D) :
    S.map f ▷ G.obj N ≫ pf.theta adj L' N = pf.theta adj L N ≫ G.map (f ▷ N) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, homEquiv_symm_theta,
    homEquiv_symm_theta, pf.natural_left_assoc, Category.assoc]
  erw [whisker_exchange]

/-- `θ` is natural in `N`. -/
@[reassoc]
lemma theta_natural_right (L : D) {N N' : D} (g : N ⟶ N') :
    S.obj L ◁ G.map g ≫ pf.theta adj L N' = pf.theta adj L N ≫ G.map (L ◁ g) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, homEquiv_symm_theta,
    homEquiv_symm_theta, pf.natural_right_assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
  erw [adj.counit_naturality]

/-- `θ` is compatible with the unit. -/
@[reassoc]
lemma theta_unit (N : D) :
    Functor.LaxMonoidal.ε S ▷ G.obj N ≫ pf.theta adj (𝟙_ D) N ≫ G.map (λ_ N).hom =
      (λ_ (G.obj N)).hom := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, homEquiv_symm_theta,
    Category.assoc, leftUnitor_naturality, ← Category.assoc ((pf.iso _ _).hom), pf.unit,
    ← Category.assoc, ← P.map_comp, ← Category.assoc, ← comp_whiskerRight,
    Functor.Monoidal.ε_η, id_whiskerRight, Category.id_comp, homEquiv_counit]

/-- `θ` is compatible with the associativity constraints. -/
@[reassoc]
lemma theta_assoc (L L' N : D) :
    Functor.LaxMonoidal.μ S L L' ▷ G.obj N ≫ pf.theta adj (L ⊗ L') N ≫ G.map (α_ L L' N).hom =
      (α_ (S.obj L) (S.obj L') (G.obj N)).hom ≫ S.obj L ◁ pf.theta adj L' N ≫
        pf.theta adj L (L' ⊗ N) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, homEquiv_symm_theta,
    homEquiv_naturality_left_symm, homEquiv_naturality_left_symm, homEquiv_symm_theta]
  simp only [Category.assoc]
  erw [associator_naturality_right]
  rw [← Category.assoc ((pf.iso _ _).hom), pf.assoc]
  simp only [Category.assoc]
  rw [← P.map_comp_assoc, ← Category.assoc (Functor.LaxMonoidal.μ S L L' ▷ G.obj N),
    ← comp_whiskerRight, Functor.Monoidal.μ_δ, id_whiskerRight, Category.id_comp,
    ← MonoidalCategory.whiskerLeft_comp, pf.natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, map_theta_comp_counit]

variable (B : D) [MonObj B]

/-- The action of `S B` on `G N` for a `B`-module object `N`, through the mate of the projection
formula: `S B ⊗ G N ⟶ G (B ⊗ N) ⟶ G N`. -/
noncomputable def rightSMul (N : D) [ModObj B N] : S.obj B ⊗ G.obj N ⟶ G.obj N :=
  pf.theta adj B N ≫ G.map γ[B,N]

/-- For a `B`-module object `N`, `G N` is an `S B`-module object through the mate of the
projection formula. -/
@[instance_reducible]
noncomputable def rightModObj (N : D) [ModObj B N] : ModObj (S.obj B) (G.obj N) where
  smul := pf.rightSMul adj B N
  one_smul := by
    change η[S.obj B] ▷ G.obj N ≫ pf.rightSMul adj B N = (λ_ (G.obj N)).hom
    rw [rightSMul, Functor.obj.η_def, comp_whiskerRight, Category.assoc,
      theta_natural_left_assoc, ← G.map_comp, ModObj.one_smul_self, theta_unit]
  mul_smul := by
    change μ[S.obj B] ▷ G.obj N ≫ pf.rightSMul adj B N =
      (α_ (S.obj B) (S.obj B) (G.obj N)).hom ≫ S.obj B ◁ pf.rightSMul adj B N ≫
        pf.rightSMul adj B N
    rw [rightSMul, Functor.obj.μ_def, comp_whiskerRight, Category.assoc,
      theta_natural_left_assoc, ← G.map_comp, ModObj.mul_smul_self, G.map_comp, G.map_comp,
      theta_assoc_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      theta_natural_right_assoc]

lemma rightModObj_smul (N : D) [ModObj B N] :
    (pf.rightModObj adj B N).smul = pf.rightSMul adj B N :=
  rfl


/-- The linearization `G_B : Mod D B ⥤ Mod C (S B)` of a right adjoint `G` of `P`: a
`B`-module object `N` is sent to `G N` with the `S B`-action induced by the mate of the
projection formula. -/
noncomputable def mapModRight : Mod D B ⥤ Mod C (S.obj B) where
  obj N := letI := pf.rightModObj adj B N.X; ⟨G.obj N.X⟩
  map {N N'} f :=
    letI := pf.rightModObj adj B N.X
    letI := pf.rightModObj adj B N'.X
    Mod.Hom.mk' (G.map f.hom) (by
      change pf.rightSMul adj B N.X ≫ G.map f.hom =
        S.obj B ◁ G.map f.hom ≫ pf.rightSMul adj B N'.X
      rw [rightSMul, rightSMul, Category.assoc, ← G.map_comp, Mod.act_hom, G.map_comp,
        theta_natural_right_assoc])
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

lemma mapModRight_obj_X (N : Mod D B) : ((pf.mapModRight adj B).obj N).X = G.obj N.X := rfl

lemma mapModRight_map_hom {N N' : Mod D B} (f : N ⟶ N') :
    ((pf.mapModRight adj B).map f).hom = G.map f.hom := rfl

lemma mapModRight_obj_smul (N : Mod D B) :
    γ[S.obj B,((pf.mapModRight adj B).obj N).X] = pf.rightSMul adj B N.X := rfl

/-- The linearization of `G` commutes with the forgetful functors. -/
lemma mapModRight_comp_forget :
    pf.mapModRight adj B ⋙ Mod.forget (S.obj B) = Mod.forget B ⋙ G := rfl


/-! ### The adjunction `P_B ⊣ G_B` -/

variable {B}

/-- A map `P M ⟶ N` is `B`-linear iff its adjoint `M ⟶ G N` is `S B`-linear, for the action of
`B` on `P M` through the projection formula and of `S B` on `G N` through its mate. -/
lemma smul_comp_eq_iff (M : Mod C (S.obj B)) (N : Mod D B) (φ : P.obj M.X ⟶ N.X) :
    pf.smul B M.X ≫ φ = B ◁ φ ≫ γ[B,N.X] ↔
      γ[S.obj B,M.X] ≫ adj.homEquiv M.X N.X φ =
        S.obj B ◁ adj.homEquiv M.X N.X φ ≫ pf.rightSMul adj B N.X := by
  rw [smul, Category.assoc, Iso.inv_comp_eq]
  refine Iff.trans ?_ (adj.homEquiv _ _).symm.apply_eq_iff_eq
  rw [
    homEquiv_naturality_left_symm, Equiv.symm_apply_apply, homEquiv_naturality_left_symm,
    rightSMul, homEquiv_naturality_right_symm, homEquiv_symm_theta]
  simp only [Category.assoc]
  have h : P.map (adj.homEquiv M.X N.X φ) ≫ adj.counit.app N.X = φ := by
    have := adj.homEquiv_counit (g := adj.homEquiv M.X N.X φ)
    rw [Equiv.symm_apply_apply] at this; exact this.symm
  rw [pf.natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, h]

/-- The linearization of `P` is left adjoint to the linearization of `G`: a `B`-linear map
`P M ⟶ N` is the same as an `S B`-linear map `M ⟶ G N`. -/
noncomputable def mapModAdjunction : pf.mapModLeft B ⊣ pf.mapModRight adj B :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun φ := Mod.Hom.mk' (adj.homEquiv M.X N.X φ.hom)
            ((pf.smul_comp_eq_iff adj M N φ.hom).1 (Mod.act_hom φ))
          invFun ψ := Mod.Hom.mk' ((adj.homEquiv M.X N.X).symm ψ.hom)
            ((pf.smul_comp_eq_iff adj M N _).2
              (by simp only [Equiv.apply_symm_apply]; exact Mod.act_hom ψ))
          left_inv φ := by ext; simp
          right_inv ψ := by ext; simp }
      homEquiv_naturality_left_symm _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_right _ _) }

lemma isLeftAdjoint_mapModLeft {G : D ⥤ C} (adj : P ⊣ G) : (pf.mapModLeft B).IsLeftAdjoint :=
  (pf.mapModAdjunction adj (B := B)).isLeftAdjoint


end MapModRight

end Functor.ProjectionFormula

/-! ### The case of an adjunction `P ⊣ S` -/

namespace Adjunction

variable {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.Monoidal] [adj.HasProjectionFormula]
  (B : D) [MonObj B]

/-- The linearization of the left adjoint `P` of a strong monoidal functor `S` satisfying the
projection formula. -/
noncomputable abbrev mapModLeft : Mod C (S.obj B) ⥤ Mod D B := adj.projectionFormula.mapModLeft B

/-- The linearization of `P` commutes with the forgetful functors. -/
lemma mapModLeft_comp_forget : adj.mapModLeft B ⋙ Mod.forget B = Mod.forget (S.obj B) ⋙ P := rfl

/-- For `G = S`, the mate `θ` of the projection formula is the lax structure `μ S`. -/
lemma projectionFormula_theta (L N : D) :
    adj.projectionFormula.theta adj L N = Functor.LaxMonoidal.μ S L N := by
  rw [Functor.ProjectionFormula.theta, projectionFormula_iso, asIso_hom, homEquiv_naturality_right,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_right,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [adj.right_triangle_components]
  erw [MonoidalCategory.whiskerLeft_id, Category.id_comp]


variable {B}

/-- A map `P M ⟶ N` is `B`-linear iff its adjoint `M ⟶ S N` is `S B`-linear, for the action of
`B` on `P M` through the projection formula and of `S B` on `S N` through the lax structure of
`S`: for `G = S`, the mate `θ` of the projection formula is the lax structure `μ S`. -/
lemma projectionFormulaSMul_comp_eq_iff (M : Mod C (S.obj B)) (N : Mod D B)
    (φ : P.obj M.X ⟶ N.X) :
    adj.projectionFormula.smul B M.X ≫ φ = B ◁ φ ≫ γ[B,N.X] ↔
      γ[S.obj B,M.X] ≫ adj.homEquiv M.X N.X φ =
        S.obj B ◁ adj.homEquiv M.X N.X φ ≫ Functor.LaxMonoidal.μ S B N.X ≫ S.map γ[B,N.X] := by
  rw [Functor.ProjectionFormula.smul, Category.assoc, projectionFormula_iso, asIso_inv,
    IsIso.inv_comp_eq, ← (adj.homEquiv _ _).apply_eq_iff_eq,
    homEquiv_naturality_left, homEquiv_naturality_right, S.map_comp,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [← adj.homEquiv_unit]
  exact Iff.rfl

/-- The linearization of `P` is left adjoint to the transport of module objects along `S`: a
`B`-linear map `P M ⟶ N` is the same as an `S B`-linear map `M ⟶ S N`. -/
noncomputable def mapModLeftAdjunction : adj.mapModLeft B ⊣ S.mapMod B :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun φ := Mod.Hom.mk' (adj.homEquiv M.X N.X φ.hom)
            ((adj.projectionFormulaSMul_comp_eq_iff M N φ.hom).1 (Mod.act_hom φ))
          invFun ψ := Mod.Hom.mk' ((adj.homEquiv M.X N.X).symm ψ.hom)
            ((adj.projectionFormulaSMul_comp_eq_iff M N _).2
              (by simp only [Equiv.apply_symm_apply]; exact Mod.act_hom ψ))
          left_inv φ := by ext; simp
          right_inv ψ := by ext; simp }
      homEquiv_naturality_left_symm _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_right _ _) }

end Adjunction

end CategoryTheory

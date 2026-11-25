/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric

/-!

# Monoidality of `mapMod` and of change of scalars along an isomorphism

Let `C` and `D` be braided monoidal categories with coequalizers preserved by tensoring on either
side, so that the module objects over a commutative algebra object carry the relative tensor
product `⊗_R` (`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`). This file shows that the
two operations out of which the pullback of module objects over a coefficient ring sheaf is
built are strong monoidal for `⊗_R`:

* **Transport along a braided functor.** For a braided (strong monoidal) functor `F : C ⥤ D`
  preserving coequalizers and a commutative algebra object `R : C`, the functor
  `F.mapMod : Mod C R ⥤ Mod D (F.obj R)` is strong monoidal
  (`Functor.mapModCoreMonoidal`, `Functor.monoidal_mapMod`). The comparison
  `F M ⊗_{F R} F N ≅ F (M ⊗_R N)` is induced on the coequalizers presenting both sides by the
  tensorator `μ F M N : F M ⊗ F N ≅ F (M ⊗ N)`: the coequalizer presenting `M ⊗_R N` is
  preserved by `F`, and `μ F` identifies the image of its parallel pair with the parallel pair
  presenting `F M ⊗_{F R} F N`. The braiding of `F` is needed because the right action of `R`
  on a module object involves the braiding of `C`.
* **Restriction of scalars along an isomorphism.** For an isomorphism `ψ : S ⟶ R` of
  commutative algebra objects, `Mod.comap ψ : Mod C R ⥤ Mod C S` is strong monoidal
  (`Mod.comapCoreMonoidal`, `Mod.monoidal_comap`): the coequalizers presenting `M ⊗_R N` and
  `M ⊗_S N` are coequalizers of parallel pairs differing by the isomorphism `M ⊗ ψ ⊗ N`, and
  the comparison is the identity of `M ⊗ N` on the projections. Consequently the extension of
  scalars along an isomorphism `φ` of commutative algebra objects, which is the restriction of
  scalars along `φ⁻¹` (`Mod.extendScalarsIsoComapInv`), is strong monoidal
  (`Mod.monoidal_extendScalars`).

## Main definitions

- `Mod.tensorObjDesc`: a morphism out of `M ⊗_R N` from an `R`-balanced morphism out of `M ⊗ N`.
- `Functor.mapModTensorIso`, `Functor.mapModCoreMonoidal`, `Functor.monoidal_mapMod`: the strong
  monoidal structure of `F.mapMod`.
- `Mod.comapTensorIso`, `Mod.comapCoreMonoidal`, `Mod.monoidal_comap`: the strong monoidal
  structure of `Mod.comap ψ` along an isomorphism `ψ`.
- `Mod.monoidal_extendScalars`: the strong monoidal structure of `Mod.extendScalars φ` along an
  isomorphism `φ`.

## Implementation notes

The balancing conditions (`Functor.mapMod_μ_balanced`, `Functor.mapMod_δ_balanced`,
`Mod.comap_tensorπ_balanced`, `Mod.tensorπ_comap_balanced`), the linearity of the comparison maps
(`Functor.mapModTensorIso_linear`, `Mod.comapTensorIso_linear`) and the coherence axioms of
`Functor.mapModCoreMonoidal` and `Mod.comapCoreMonoidal` are checked after precomposition with the
projections onto the coequalizers (`Mod.tensorObjπ`), where they reduce to the coherences of `μ F`
and of the algebra structures.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

namespace Mod

variable {R : C} [MonObj R] [IsCommMonObj R]

/-- A morphism out of the relative tensor product `M ⊗_R N`, from a morphism out of `M ⊗ N`
which is balanced for the two actions of `R`. -/
noncomputable def tensorObjDesc (M N : Mod C R) {W : C} (k : M.X ⊗ N.X ⟶ W)
    (hk : ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ k = ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ k) :
    (M ⊗ N).X ⟶ W :=
  Cofork.IsColimit.desc (isColimitTensorπ M N) k hk

@[reassoc (attr := simp)]
lemma tensorObjπ_tensorObjDesc (M N : Mod C R) {W : C} (k : M.X ⊗ N.X ⟶ W) (hk) :
    tensorObjπ M N ≫ tensorObjDesc M N k hk = k := by
  unfold tensorObjDesc
  exact Cofork.IsColimit.π_desc' (isColimitTensorπ M N) k hk

end Mod

/-! ### Transport of module objects along a braided functor -/

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

open scoped Obj

namespace Functor

variable (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The composite `F M ⊗ F N ⟶ F (M ⊗ N) ⟶ F (M ⊗_R N)` is balanced for the two actions of
`F R`, the right action of `F R` on `F M` being `F` of the right action of `R` on `M` since `F`
is braided. -/
lemma mapMod_μ_balanced (M N : Mod C R) :
    ((β_ ((F.mapMod R).obj M).X (F.obj R)).hom ≫ γ[F.obj R, ((F.mapMod R).obj M).X]) ▷
        ((F.mapMod R).obj N).X ≫ LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) =
      ((α_ ((F.mapMod R).obj M).X (F.obj R) ((F.mapMod R).obj N).X).hom ≫
        ((F.mapMod R).obj M).X ◁ γ[F.obj R, ((F.mapMod R).obj N).X]) ≫
          LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) := by
  have _ := (inferInstance : HasCoequalizers D)
  have _ := (inferInstance : ∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X))
  have _ := (inferInstance : ∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X))
  have _ := (inferInstance : PreservesColimitsOfShape WalkingParallelPair F)
  dsimp only [Functor.mapMod]
  simp only [F.modObjObj_smul]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.μ_natural_right_assoc]
  slice_lhs 1 2 => rw [← comp_whiskerRight, ← Functor.LaxBraided.braided]
  simp only [comp_whiskerRight, Category.assoc]
  rw [LaxMonoidal.μ_natural_left_assoc, ← LaxMonoidal.associativity_assoc]
  simp only [← F.map_comp]
  have h := Mod.tensorObjπ_condition M N
  simp only [comp_whiskerRight, Category.assoc] at h
  rw [h]

/-- The composite `F (M ⊗ N) ⟶ F M ⊗ F N ⟶ F M ⊗_{F R} F N` coequalizes the image under `F` of
the parallel pair presenting `M ⊗_R N`. -/
lemma mapMod_δ_balanced (M N : Mod C R) :
    F.map (((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X) ≫ OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) =
      F.map ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) := by
  have _ := (inferInstance : HasCoequalizers C)
  have _ := (inferInstance : ∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X))
  have _ := (inferInstance : ∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X))
  have _ := (inferInstance : PreservesColimitsOfShape WalkingParallelPair F)
  rw [← cancel_epi (LaxMonoidal.μ F M.X R ▷ F.obj N.X ≫
    LaxMonoidal.μ F (M.X ⊗ R) N.X)]
  simp only [Category.assoc, F.map_comp]
  rw [← LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.associativity_assoc,
    ← LaxMonoidal.μ_natural_right_assoc, Monoidal.μ_δ_assoc]
  simp only [F.map_comp, comp_whiskerRight, Category.assoc]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, Functor.LaxBraided.braided, comp_whiskerRight]
  simp only [Category.assoc]
  have h := Mod.tensorObjπ_condition ((F.mapMod R).obj M) ((F.mapMod R).obj N)
  dsimp only [Functor.mapMod] at h ⊢
  simpa only [F.modObjObj_smul, comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc] using h

/-- The image under `F` of the coequalizer presenting `M ⊗_R N` is a coequalizer, `F`
preserving coequalizers. -/
noncomputable def isColimitMapTensorπ (M N : Mod C R) :=
  isColimitCoforkMapOfIsColimit F (Mod.tensorObjπ_condition M N) (Mod.isColimitTensorπ M N)

/-- The comparison `F M ⊗_{F R} F N ≅ F (M ⊗_R N)` of the underlying objects, induced by the
tensorator `μ F M N` on the coequalizers presenting both sides. -/
noncomputable def mapModTensorIsoX (M N : Mod C R) :
    ((F.mapMod R).obj M ⊗ (F.mapMod R).obj N).X ≅ ((F.mapMod R).obj (M ⊗ N)).X where
  hom := Mod.tensorObjDesc _ _ (LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N))
    (F.mapMod_μ_balanced M N)
  inv := Cofork.IsColimit.desc (F.isColimitMapTensorπ M N)
    (OplaxMonoidal.δ F M.X N.X ≫ Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N))
    (F.mapMod_δ_balanced M N)
  hom_inv_id := by
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N)),
      Mod.tensorObjπ_tensorObjDesc_assoc,
      Category.assoc, Category.comp_id]
    erw [Cofork.IsColimit.π_desc' (F.isColimitMapTensorπ M N)]
    rw [Monoidal.μ_δ_assoc]
  inv_hom_id := by
    refine Cofork.IsColimit.hom_ext (F.isColimitMapTensorπ M N) ?_
    erw [Cofork.IsColimit.π_desc'_assoc (F.isColimitMapTensorπ M N)]
    rw [Category.assoc, Mod.tensorObjπ_tensorObjDesc, Monoidal.δ_μ_assoc]
    exact (Category.comp_id _).symm

/-- The comparison `F M ⊗_{F R} F N ⟶ F (M ⊗_R N)` is `F R`-linear. -/
lemma mapModTensorIso_linear (M N : Mod C R) :
    γ[F.obj R, ((F.mapMod R).obj M ⊗ (F.mapMod R).obj N).X] ≫ (F.mapModTensorIsoX M N).hom =
      F.obj R ◁ (F.mapModTensorIsoX M N).hom ≫ γ[F.obj R, ((F.mapMod R).obj (M ⊗ N)).X] := by
  have h : Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ≫
      (F.mapModTensorIsoX M N).hom =
      LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) :=
    Mod.tensorObjπ_tensorObjDesc _ _ _ _
  rw [← cancel_epi (F.obj R ◁ Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N)),
    Mod.whiskerLeft_tensorπ_smul_assoc, h,
    ← MonoidalCategory.whiskerLeft_comp_assoc, h]
  change (α_ (F.obj R) (F.obj M.X) (F.obj N.X)).inv ≫
      (LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X]) ▷ F.obj N.X ≫
        LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) =
    F.obj R ◁ (LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N)) ≫
      LaxMonoidal.μ F R (M ⊗ N).X ≫ F.map γ[R,(M ⊗ N).X]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.μ_natural_right_assoc]
  simp only [← F.map_comp]
  rw [Mod.whiskerLeft_tensorπ_smul]
  simp only [F.map_comp]
  rw [LaxMonoidal.associativity_inv_assoc]

/-- The comparison isomorphism `F M ⊗_{F R} F N ≅ F (M ⊗_R N)` of `F R`-module objects. -/
noncomputable def mapModTensorIso (M N : Mod C R) :
    (F.mapMod R).obj M ⊗ (F.mapMod R).obj N ≅ (F.mapMod R).obj (M ⊗ N) :=
  Mod.isoMk (F.mapModTensorIsoX M N) (F.mapModTensorIso_linear M N)

@[simp]
lemma mapModTensorIso_hom_hom (M N : Mod C R) :
    (F.mapModTensorIso M N).hom.hom = (F.mapModTensorIsoX M N).hom :=
  rfl

@[reassoc (attr := simp)]
lemma tensorπ_mapModTensorIso_hom_hom (M N : Mod C R) :
    Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ≫ (F.mapModTensorIso M N).hom.hom =
      LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) :=
  Mod.tensorObjπ_tensorObjDesc _ _ _ _

/-- The unit comparison `𝟙 ≅ F.mapMod 𝟙`: both are `F R` with its algebra structure. -/
noncomputable def mapModUnitIso :
    𝟙_ (Mod D (F.obj R)) ≅ (F.mapMod R).obj (𝟙_ (Mod C R)) :=
  Mod.isoMk (Iso.refl (F.obj R)) (by
    change MonObj.mul ≫ 𝟙 _ = _ ◁ 𝟙 _ ≫ (LaxMonoidal.μ F R R ≫ F.map MonObj.mul)
    simp only [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl)

/-- The transport `F.mapMod : Mod C R ⥤ Mod D (F.obj R)` of module objects along a braided
functor preserving coequalizers is strong monoidal for the relative tensor products, with
comparison isomorphisms `Functor.mapModTensorIso` and `Functor.mapModUnitIso`. -/
noncomputable def mapModCoreMonoidal : (F.mapMod R).CoreMonoidal where
  εIso := F.mapModUnitIso
  μIso := F.mapModTensorIso
  μIso_hom_natural_left := by
    intro M N f X
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj X))]
    change _ ≫ ((F.mapMod R).map f ▷ (F.mapMod R).obj X).hom ≫
      (F.mapModTensorIso N X).hom.hom = _
    rw [Mod.tensorObjπ_whiskerRight_assoc]
    rw [tensorπ_mapModTensorIso_hom_hom]
    change _ = _ ≫ (F.mapModTensorIso M X).hom.hom ≫
      ((F.mapMod R).map (f ▷ X)).hom
    rw [tensorπ_mapModTensorIso_hom_hom_assoc]
    dsimp only [Functor.mapMod] at ⊢
    change F.map f.hom ▷ F.obj X.X ≫ LaxMonoidal.μ F N.X X.X ≫
      F.map (N.tensorObjπ X) =
      LaxMonoidal.μ F M.X X.X ≫ F.map (M.tensorObjπ X) ≫ F.map ((f ▷ X).hom)
    rw [LaxMonoidal.μ_natural_left_assoc]
    rw [← F.map_comp]
    rw [← F.map_comp]
    rw [Mod.tensorObjπ_whiskerRight]
  μIso_hom_natural_right := by
    intro M N X f
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj X) ((F.mapMod R).obj M))]
    change _ ≫ ((F.mapMod R).obj X ◁ (F.mapMod R).map f).hom ≫
      (F.mapModTensorIso X N).hom.hom = _
    rw [Mod.tensorObjπ_whiskerLeft_assoc]
    rw [tensorπ_mapModTensorIso_hom_hom]
    change _ = _ ≫ (F.mapModTensorIso X M).hom.hom ≫
      ((F.mapMod R).map (X ◁ f)).hom
    rw [tensorπ_mapModTensorIso_hom_hom_assoc]
    dsimp only [Functor.mapMod] at ⊢
    change F.obj X.X ◁ F.map f.hom ≫ LaxMonoidal.μ F X.X N.X ≫
      F.map (X.tensorObjπ N) =
      LaxMonoidal.μ F X.X M.X ≫ F.map (X.tensorObjπ M) ≫ F.map ((X ◁ f).hom)
    rw [LaxMonoidal.μ_natural_right_assoc]
    rw [← F.map_comp]
    rw [← F.map_comp]
    rw [Mod.tensorObjπ_whiskerLeft]
  associativity := by
    intro M N P
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ
      ((F.mapMod R).obj M ⊗ (F.mapMod R).obj N) ((F.mapMod R).obj P))]
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ▷
      ((F.mapMod R).obj P).X)]
    simp only [Mod.comp_hom']
    rw [Mod.tensorObjπ_whiskerRight_assoc]
    rw [← comp_whiskerRight_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom]
    rw [comp_whiskerRight_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc]
    erw [LaxMonoidal.μ_natural_left_assoc]
    rw [show ((F.mapMod R).map (α_ M N P).hom).hom =
      F.map (α_ M N P).hom.hom from rfl]
    rw [← F.map_comp_assoc, ← F.map_comp]
    rw [Category.assoc, Mod.tensorObjπ_associator_hom]
    rw [Mod.tensorObjπ_associator_hom_assoc, Mod.tensorObjπ_whiskerLeft_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom]
    erw [LaxMonoidal.μ_natural_right_assoc]
    simp only [F.map_comp]
    erw [LaxMonoidal.associativity_assoc]
    rfl
  left_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ (Mod.regular (R)) Q ≫ (λ_ Q).hom.hom = γ[R,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (R)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := R)).hom
        ((Mod.toBimod (R)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod D (F.obj R)) :
        Mod.tensorObjπ (Mod.regular (F.obj R)) Q ≫ (λ_ Q).hom.hom = γ[F.obj R,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (F.obj R)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := F.obj R)).hom
        ((Mod.toBimod (F.obj R)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (F.obj R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ (Mod.regular (F.obj R)) ((F.mapMod R).obj M))]
    simp only [Mod.comp_hom']
    rw [hπD, Mod.tensorObjπ_whiskerRight_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc]
    change γ[F.obj R,((F.mapMod R).obj M).X] =
      (𝟙 (F.obj R)) ▷ F.obj M.X ≫ LaxMonoidal.μ F R M.X ≫
        F.map (Mod.tensorObjπ (Mod.regular R) M) ≫ F.map (λ_ M).hom.hom
    rw [id_whiskerRight, Category.id_comp, ← F.map_comp, hπC]
    rfl
  right_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ Q (Mod.regular (R)) ≫ (ρ_ Q).hom.hom =
          (β_ Q.X (R)).hom ≫ γ[R,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (R)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (R)).obj Q)
        (Mod.toBimodRegularIso (R := R)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod D (F.obj R)) :
        Mod.tensorObjπ Q (Mod.regular (F.obj R)) ≫ (ρ_ Q).hom.hom =
          (β_ Q.X (F.obj R)).hom ≫ γ[F.obj R,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (F.obj R)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (F.obj R)).obj Q)
        (Mod.toBimodRegularIso (R := F.obj R)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (F.obj R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) (Mod.regular (F.obj R)))]
    simp only [Mod.comp_hom']
    rw [hπD, Mod.tensorObjπ_whiskerLeft_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc]
    change (β_ (F.obj M.X) (F.obj R)).hom ≫
        LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] =
      F.obj M.X ◁ (𝟙 (F.obj R)) ≫ LaxMonoidal.μ F M.X R ≫
        F.map (Mod.tensorObjπ M (Mod.regular R)) ≫ F.map (ρ_ M).hom.hom
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp,
      ← F.map_comp, hπC]
    rw [F.map_comp, Functor.LaxBraided.braided_assoc]

/-- The transport `F.mapMod` of module objects along a braided functor preserving coequalizers
is strong monoidal. -/
noncomputable instance monoidal_mapMod : (F.mapMod R).Monoidal :=
  F.mapModCoreMonoidal.toMonoidal

lemma mapMod_μ_hom (M N : Mod C R) :
    (LaxMonoidal.μ (F.mapMod R) M N).hom = (F.mapModTensorIsoX M N).hom :=
  rfl

end Functor

/-! ### Change of scalars along an isomorphism -/

namespace Mod

section Comap

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (ψ : S ⟶ R)
  [IsMonHom ψ] [IsIso ψ]

/-- The projection `M ⊗ N ⟶ M ⊗_R N` is balanced for the two actions of `S` on the
restrictions of scalars of `M` and `N`. -/
lemma tensorπ_comap_balanced (M N : Mod C R) :
    ((β_ ((comap ψ).obj M).X S).hom ≫ γ[S,((comap ψ).obj M).X]) ▷ ((comap ψ).obj N).X ≫
        tensorObjπ M N =
      ((α_ ((comap ψ).obj M).X S ((comap ψ).obj N).X).hom ≫
        ((comap ψ).obj M).X ◁ γ[S,((comap ψ).obj N).X]) ≫ tensorObjπ M N := by
  have _ := (inferInstance : IsCommMonObj S)
  have _ := (inferInstance : IsIso ψ)
  change ((β_ M.X S).hom ≫ ψ ▷ M.X ≫ γ[R,M.X]) ▷ N.X ≫ tensorObjπ M N =
    ((α_ M.X S N.X).hom ≫ M.X ◁ (ψ ▷ N.X ≫ γ[R,N.X])) ≫ tensorObjπ M N
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, ← braiding_naturality_right, comp_whiskerRight]
  slice_lhs 2 3 => rw [← comp_whiskerRight]
  rw [tensorObjπ_condition, Category.assoc, associator_naturality_middle_assoc]

/-- The projection `M ⊗ N ⟶ M ⊗_S N` of the restrictions of scalars is balanced for the two
actions of `R`, `ψ` being an isomorphism. -/
lemma comap_tensorπ_balanced (M N : Mod C R) :
    ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) =
      ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫
        tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) := by
  have _ := (inferInstance : IsCommMonObj R)
  rw [← cancel_epi ((M.X ◁ ψ) ▷ N.X)]
  simp only [comp_whiskerRight, Category.assoc]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, braiding_naturality_right, comp_whiskerRight]
  rw [associator_naturality_middle_assoc]
  have h := tensorObjπ_condition ((comap ψ).obj M) ((comap ψ).obj N)
  change ((β_ M.X S).hom ≫ ψ ▷ M.X ≫ γ[R,M.X]) ▷ N.X ≫
    tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) =
    ((α_ M.X S N.X).hom ≫ M.X ◁ (ψ ▷ N.X ≫ γ[R,N.X])) ≫
      tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) at h
  simpa only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] using h

/-- The comparison `M ⊗_S N ≅ M ⊗_R N` of the underlying objects for an isomorphism
`ψ : S ⟶ R`: both are coequalizers of parallel pairs out of `M ⊗ S ⊗ N` and `M ⊗ R ⊗ N`
differing by `M ⊗ ψ ⊗ N`, and the comparison is the identity of `M ⊗ N` on the
projections. -/
noncomputable def comapTensorIsoX (M N : Mod C R) :
    ((comap ψ).obj M ⊗ (comap ψ).obj N).X ≅ ((comap ψ).obj (M ⊗ N)).X where
  hom := tensorObjDesc _ _ (tensorObjπ M N) (tensorπ_comap_balanced ψ M N)
  inv := tensorObjDesc M N (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N))
    (comap_tensorπ_balanced ψ M N)
  hom_inv_id := by
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N)),
      tensorObjπ_tensorObjDesc_assoc]
    erw [tensorObjπ_tensorObjDesc]
    rw [Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi (tensorObjπ M N), tensorObjπ_tensorObjDesc_assoc]
    erw [tensorObjπ_tensorObjDesc, Category.comp_id]

/-- The comparison `M ⊗_S N ⟶ M ⊗_R N` is `S`-linear. -/
lemma comapTensorIso_linear (M N : Mod C R) :
    γ[S, ((comap ψ).obj M ⊗ (comap ψ).obj N).X] ≫ (comapTensorIsoX ψ M N).hom =
      S ◁ (comapTensorIsoX ψ M N).hom ≫ γ[S, ((comap ψ).obj (M ⊗ N)).X] := by
  rw [← cancel_epi (S ◁ tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N)),
    whiskerLeft_tensorπ_smul_assoc]
  dsimp only [comapTensorIsoX]
  rw [tensorObjπ_tensorObjDesc, ← whiskerLeft_comp_assoc,
    tensorObjπ_tensorObjDesc]
  change (α_ S M.X N.X).inv ≫ (ψ ▷ M.X ≫ γ[R,M.X]) ▷ N.X ≫ tensorObjπ M N =
    S ◁ tensorObjπ M N ≫ ψ ▷ (M ⊗ N).X ≫ γ[R,(M ⊗ N).X]
  rw [whisker_exchange_assoc, whiskerLeft_tensorπ_smul,
    associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]

/-- The comparison isomorphism `ψ^* M ⊗_S ψ^* N ≅ ψ^* (M ⊗_R N)` of `S`-module objects for an
isomorphism `ψ : S ⟶ R` of commutative algebra objects. -/
noncomputable def comapTensorIso (M N : Mod C R) :
    (comap ψ).obj M ⊗ (comap ψ).obj N ≅ (comap ψ).obj (M ⊗ N) :=
  isoMk (comapTensorIsoX ψ M N) (comapTensorIso_linear ψ M N)

@[reassoc (attr := simp)]
lemma tensorπ_comapTensorIso_hom_hom (M N : Mod C R) :
    tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) ≫ (comapTensorIso ψ M N).hom.hom =
      tensorObjπ M N :=
  tensorObjπ_tensorObjDesc _ _ _ _

/-- The unit comparison `S ≅ ψ^* R` of `S`-module objects, given by `ψ`. -/
noncomputable def comapUnitIso : 𝟙_ (Mod C S) ≅ (comap ψ).obj (𝟙_ (Mod C R)) :=
  isoMk (asIso ψ) (by
    change MonObj.mul ≫ ψ = S ◁ ψ ≫ (ψ ▷ R ≫ MonObj.mul)
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

/-- Restriction of scalars along an isomorphism `ψ : S ⟶ R` of commutative algebra objects is
strong monoidal for the relative tensor products, with comparison isomorphisms
`Mod.comapTensorIso` and `Mod.comapUnitIso`. -/
noncomputable def comapCoreMonoidal : (comap ψ : Mod C R ⥤ Mod C S).CoreMonoidal where
  εIso := comapUnitIso ψ
  μIso := comapTensorIso ψ
  μIso_hom_natural_left := by
    intro M N f X
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj X))]
    change _ ≫ ((comap ψ).map f ▷ (comap ψ).obj X).hom ≫
      (comapTensorIso ψ N X).hom.hom = _
    rw [tensorObjπ_whiskerRight_assoc, tensorπ_comapTensorIso_hom_hom]
    change _ = _ ≫ (comapTensorIso ψ M X).hom.hom ≫ ((comap ψ).map (f ▷ X)).hom
    rw [tensorπ_comapTensorIso_hom_hom_assoc]
    change f.hom ▷ X.X ≫ tensorObjπ N X =
      tensorObjπ M X ≫ (f ▷ X).hom
    rw [tensorObjπ_whiskerRight]
  μIso_hom_natural_right := by
    intro M N X f
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj X) ((comap ψ).obj M))]
    change _ ≫ (((comap ψ).obj X ◁ (comap ψ).map f).hom) ≫
      (comapTensorIso ψ X N).hom.hom = _
    rw [tensorObjπ_whiskerLeft_assoc, tensorπ_comapTensorIso_hom_hom]
    change _ = _ ≫ (comapTensorIso ψ X M).hom.hom ≫ ((comap ψ).map (X ◁ f)).hom
    rw [tensorπ_comapTensorIso_hom_hom_assoc]
    change X.X ◁ f.hom ≫ tensorObjπ X N =
      tensorObjπ X M ≫ (X ◁ f).hom
    rw [tensorObjπ_whiskerLeft]
  associativity := by
    intro M N P
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ
      ((comap ψ).obj M ⊗ (comap ψ).obj N) ((comap ψ).obj P))]
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) ▷
      ((comap ψ).obj P).X)]
    simp only [Mod.comp_hom']
    rw [tensorObjπ_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      tensorπ_comapTensorIso_hom_hom,
      tensorπ_comapTensorIso_hom_hom_assoc]
    change tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P ≫ (α_ M N P).hom.hom = _
    rw [tensorObjπ_associator_hom]
    rw [tensorObjπ_associator_hom_assoc, tensorObjπ_whiskerLeft_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, tensorπ_comapTensorIso_hom_hom,
      tensorπ_comapTensorIso_hom_hom]
    rfl
  left_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ (Mod.regular (R)) Q ≫ (λ_ Q).hom.hom = γ[R,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (R)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := R)).hom
        ((Mod.toBimod (R)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod C (S)) :
        Mod.tensorObjπ (Mod.regular (S)) Q ≫ (λ_ Q).hom.hom = γ[S,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (S)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := S)).hom
        ((Mod.toBimod (S)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (S)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ (regular S) ((comap ψ).obj M))]
    simp only [Mod.comp_hom']
    rw [hπD, tensorObjπ_whiskerRight_assoc,
      tensorπ_comapTensorIso_hom_hom_assoc]
    change ψ ▷ M.X ≫ γ[R,M.X] =
      ψ ▷ M.X ≫ tensorObjπ (regular R) M ≫ (λ_ M).hom.hom
    rw [hπC]
  right_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ Q (Mod.regular (R)) ≫ (ρ_ Q).hom.hom =
          (β_ Q.X (R)).hom ≫ γ[R,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (R)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (R)).obj Q)
        (Mod.toBimodRegularIso (R := R)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod C (S)) :
        Mod.tensorObjπ Q (Mod.regular (S)) ≫ (ρ_ Q).hom.hom =
          (β_ Q.X (S)).hom ≫ γ[S,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (S)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (S)).obj Q)
        (Mod.toBimodRegularIso (R := S)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (S)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) (regular S))]
    simp only [Mod.comp_hom']
    rw [hπD, tensorObjπ_whiskerLeft_assoc,
      tensorπ_comapTensorIso_hom_hom_assoc]
    change (β_ M.X S).hom ≫ ψ ▷ M.X ≫ γ[R,M.X] =
      M.X ◁ ψ ≫ tensorObjπ M (regular R) ≫ (ρ_ M).hom.hom
    rw [hπC]
    rw [braiding_naturality_right_assoc]

/-- Restriction of scalars along an isomorphism of commutative algebra objects is strong
monoidal. -/
noncomputable instance monoidal_comap : (comap ψ : Mod C R ⥤ Mod C S).Monoidal :=
  (comapCoreMonoidal ψ).toMonoidal

end Comap

section ExtendScalars

variable [MonoidalClosed C] [HasEqualizers C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [IsIso φ]

/-- Extension of scalars along an isomorphism `φ : R ⟶ S` of commutative algebra objects is
strong monoidal for the relative tensor products: it is the restriction of scalars along `φ⁻¹`
(`Mod.extendScalarsIsoComapInv`), which is strong monoidal (`Mod.monoidal_comap`), and the
monoidal structure is transported along this isomorphism. -/
noncomputable instance monoidal_extendScalars : (extendScalars φ).Monoidal :=
  Functor.Monoidal.transport (extendScalarsIsoComapInv φ).symm

end ExtendScalars

end Mod

end CategoryTheory

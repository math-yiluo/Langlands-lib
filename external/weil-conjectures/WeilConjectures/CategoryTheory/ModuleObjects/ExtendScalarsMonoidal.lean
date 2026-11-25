/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction

/-!

# Extension of scalars of module objects is strong monoidal

Let `C` be a braided monoidal category with coequalizers preserved by tensoring on either side,
and `φ : R ⟶ S` a morphism of commutative algebra objects of `C`. This file shows that the
extension of scalars `S ⊗_R - : Mod C R ⥤ Mod C S` is strong monoidal for the relative tensor
products, for an arbitrary `φ` (the case of an isomorphism `φ` is `Mod.monoidal_extendScalars`).

* **Restriction of scalars is lax monoidal** (`Mod.comapLaxMonoidal`): the comparison
  `M ⊗_R N ⟶ M ⊗_S N` is induced by the identity of `M ⊗ N`, and the unit comparison is `φ`.
* **Extension of scalars is oplax monoidal** (`Mod.extendScalarsOplaxMonoidal`), by doctrinal
  adjunction along `extendScalars φ ⊣ comap φ`.
* **The projection formula** (`Mod.projectionIso`): for an `S`-module `Q` and an `R`-module `N`,
  the map `Q ⊗_R N ⟶ Q ⊗_S (S ⊗_R N)`, `q ⊗ n ↦ q ⊗ (1 ⊗ n)`, is an isomorphism of `R`-modules,
  with inverse `q ⊗ (s ⊗ n) ↦ s q ⊗ n`.
* **Extension of scalars is strong monoidal** (`Mod.extendScalarsMonoidal`): the unit comparison
  `S ⊗_R R ⟶ S` is an isomorphism with inverse `s ↦ s ⊗ 1`, and the comonoidal structure
  `S ⊗_R (M ⊗_R N) ⟶ (S ⊗_R M) ⊗_S (S ⊗_R N)` is an isomorphism, its restriction of scalars
  being the composite `Mod.extendTensorIso` of unitors, associators and projection formulas
  (`Mod.comap_map_δ_extendScalars`).
* **Compatibility with the braidings** (`Mod.extendScalars_map_braiding_hom_δ`), for a symmetric
  `C`, since restriction of scalars is lax braided (`Mod.comapLaxBraided`).

The structures are definitions rather than instances, to avoid a diamond with
`Mod.monoidal_comap` and `Mod.monoidal_extendScalars` when `φ` is an isomorphism.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

section Unitors

variable {R : C} [MonObj R] [IsCommMonObj R]

/-- The left unitor of the relative tensor product is induced by the action. -/
@[reassoc]
lemma tensorObjπ_regular_leftUnitor_hom (Q : Mod C R) :
    tensorObjπ (regular R) Q ≫ (λ_ Q).hom.hom = γ[R,Q.X] := by
  change tensorObjπ (regular R) Q ≫
    (Bimod.whiskerRight (toBimodRegularIso (R := R)).hom ((toBimod R).obj Q)).hom ≫
      (Bimod.LeftUnitorBimod.hom ((toBimod R).obj Q)) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, id_whiskerRight, Category.id_comp]
  exact coequalizer.π_desc _ _

/-- The right unitor of the relative tensor product is induced by the right action. -/
@[reassoc]
lemma tensorObjπ_regular_rightUnitor_hom (Q : Mod C R) :
    tensorObjπ Q (regular R) ≫ (ρ_ Q).hom.hom = (β_ Q.X R).hom ≫ γ[R,Q.X] := by
  change tensorObjπ Q (regular R) ≫
    (Bimod.whiskerLeft ((toBimod R).obj Q) (toBimodRegularIso (R := R)).hom).hom ≫
      (Bimod.RightUnitorBimod.hom ((toBimod R).obj Q)) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerLeft_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact coequalizer.π_desc _ _

end Unitors

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S)
  [IsMonHom φ]

/-! ### Restriction of scalars is lax monoidal -/

section Comap

omit [IsCommMonObj R] in
/-- The projection `M ⊗ N ⟶ M ⊗_S N` is balanced for the two actions of `R` on the
restrictions of scalars of `M` and `N`. -/
lemma tensorObjπ_comap_balanced (M N : Mod C S) :
    ((β_ ((comap φ).obj M).X R).hom ≫ γ[R,((comap φ).obj M).X]) ▷ ((comap φ).obj N).X ≫
        tensorObjπ M N =
      ((α_ ((comap φ).obj M).X R ((comap φ).obj N).X).hom ≫
        ((comap φ).obj M).X ◁ γ[R,((comap φ).obj N).X]) ≫ tensorObjπ M N := by
  change ((β_ M.X R).hom ≫ φ ▷ M.X ≫ γ[S,M.X]) ▷ N.X ≫ tensorObjπ M N =
    ((α_ M.X R N.X).hom ≫ M.X ◁ (φ ▷ N.X ≫ γ[S,N.X])) ≫ tensorObjπ M N
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, ← braiding_naturality_right, comp_whiskerRight]
  slice_lhs 2 3 => rw [← comp_whiskerRight]
  rw [tensorObjπ_condition, Category.assoc, associator_naturality_middle_assoc]

/-- The comparison `M ⊗_R N ⟶ M ⊗_S N` of the underlying objects, induced by the identity of
`M ⊗ N`. -/
noncomputable def comapTensorHomX (M N : Mod C S) :
    ((comap φ).obj M ⊗ (comap φ).obj N).X ⟶ ((comap φ).obj (M ⊗ N)).X :=
  tensorObjDesc _ _ (tensorObjπ M N) (tensorObjπ_comap_balanced φ M N)

@[reassoc (attr := simp)]
lemma tensorObjπ_comapTensorHomX (M N : Mod C S) :
    tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ≫ comapTensorHomX φ M N = tensorObjπ M N :=
  tensorObjπ_tensorObjDesc _ _ _ _

/-- The comparison `M ⊗_R N ⟶ M ⊗_S N` is `R`-linear. -/
lemma comapTensorHomX_linear (M N : Mod C S) :
    γ[R, ((comap φ).obj M ⊗ (comap φ).obj N).X] ≫ comapTensorHomX φ M N =
      R ◁ comapTensorHomX φ M N ≫ γ[R, ((comap φ).obj (M ⊗ N)).X] := by
  rw [← cancel_epi (R ◁ tensorObjπ ((comap φ).obj M) ((comap φ).obj N)),
    whiskerLeft_tensorπ_smul_assoc, tensorObjπ_comapTensorHomX, ← whiskerLeft_comp_assoc,
    tensorObjπ_comapTensorHomX]
  change (α_ R M.X N.X).inv ≫ (φ ▷ M.X ≫ γ[S,M.X]) ▷ N.X ≫ tensorObjπ M N =
    R ◁ tensorObjπ M N ≫ φ ▷ (M ⊗ N).X ≫ γ[S,(M ⊗ N).X]
  rw [whisker_exchange_assoc, whiskerLeft_tensorπ_smul,
    associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]

/-- The comparison `φ^* M ⊗_R φ^* N ⟶ φ^* (M ⊗_S N)` of `R`-module objects. -/
noncomputable def comapTensorHom (M N : Mod C S) :
    (comap φ).obj M ⊗ (comap φ).obj N ⟶ (comap φ).obj (M ⊗ N) :=
  homMk (comapTensorHomX φ M N) (comapTensorHomX_linear φ M N)

@[reassoc (attr := simp)]
lemma tensorObjπ_comapTensorHom_hom (M N : Mod C S) :
    tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ≫ (comapTensorHom φ M N).hom =
      tensorObjπ M N :=
  tensorObjπ_comapTensorHomX φ M N

/-- The unit comparison `R ⟶ φ^* S` of `R`-module objects, given by `φ`. -/
noncomputable def comapUnitHom : 𝟙_ (Mod C R) ⟶ (comap φ).obj (𝟙_ (Mod C S)) :=
  homMk φ (by
    change MonObj.mul ≫ φ = R ◁ φ ≫ (φ ▷ S ≫ MonObj.mul)
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

@[simp]
lemma comapUnitHom_hom : (comapUnitHom φ).hom = φ := rfl

/-- Restriction of scalars along a morphism `φ : R ⟶ S` of commutative algebra objects is lax
monoidal for the relative tensor products, with comparison maps `Mod.comapTensorHom` and
`Mod.comapUnitHom`. -/
@[instance_reducible]
noncomputable def comapLaxMonoidal : (comap φ : Mod C S ⥤ Mod C R).LaxMonoidal where
  ε := comapUnitHom φ
  «μ» := comapTensorHom φ
  μ_natural_left {M N} f X := by
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M) ((comap φ).obj X))]
    change _ ≫ ((comap φ).map f ▷ (comap φ).obj X).hom ≫ (comapTensorHom φ N X).hom =
      _ ≫ (comapTensorHom φ M X).hom ≫ ((comap φ).map (f ▷ X)).hom
    rw [tensorObjπ_whiskerRight_assoc, tensorObjπ_comapTensorHom_hom,
      tensorObjπ_comapTensorHom_hom_assoc]
    exact (tensorObjπ_whiskerRight f).symm
  μ_natural_right {M N} X f := by
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj X) ((comap φ).obj M))]
    change _ ≫ ((comap φ).obj X ◁ (comap φ).map f).hom ≫ (comapTensorHom φ X N).hom =
      _ ≫ (comapTensorHom φ X M).hom ≫ ((comap φ).map (X ◁ f)).hom
    rw [tensorObjπ_whiskerLeft_assoc, tensorObjπ_comapTensorHom_hom,
      tensorObjπ_comapTensorHom_hom_assoc]
    exact (tensorObjπ_whiskerLeft f).symm
  associativity M N P := by
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M ⊗ (comap φ).obj N) ((comap φ).obj P)),
      ← cancel_epi (tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ▷ ((comap φ).obj P).X)]
    simp only [Mod.comp_hom']
    rw [tensorObjπ_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      tensorObjπ_comapTensorHom_hom, tensorObjπ_comapTensorHom_hom_assoc]
    change tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P ≫ (α_ M N P).hom.hom = _
    rw [tensorObjπ_associator_hom, tensorObjπ_associator_hom_assoc,
      tensorObjπ_whiskerLeft_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      tensorObjπ_comapTensorHom_hom, tensorObjπ_comapTensorHom_hom]
    rfl
  left_unitality M := by
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ (regular R) ((comap φ).obj M))]
    simp only [Mod.comp_hom']
    rw [tensorObjπ_regular_leftUnitor_hom, tensorObjπ_whiskerRight_assoc,
      tensorObjπ_comapTensorHom_hom_assoc]
    change φ ▷ M.X ≫ γ[S,M.X] = φ ▷ M.X ≫ tensorObjπ (regular S) M ≫ (λ_ M).hom.hom
    rw [tensorObjπ_regular_leftUnitor_hom]
  right_unitality M := by
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M) (regular R))]
    simp only [Mod.comp_hom']
    rw [tensorObjπ_regular_rightUnitor_hom, tensorObjπ_whiskerLeft_assoc,
      tensorObjπ_comapTensorHom_hom_assoc]
    change (β_ M.X R).hom ≫ φ ▷ M.X ≫ γ[S,M.X] =
      M.X ◁ φ ≫ tensorObjπ M (regular S) ≫ (ρ_ M).hom.hom
    rw [tensorObjπ_regular_rightUnitor_hom, braiding_naturality_right_assoc]

end Comap

/-! ### The projection formula -/

section Projection

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The right action `q ⊗ s ↦ s • q` of `S` on an `S`-module object is unital. -/
@[reassoc]
lemma whiskerLeft_one_braiding_smul (Q : Mod C S) :
    Q.X ◁ η[S] ≫ (β_ Q.X S).hom ≫ γ[S,Q.X] = (ρ_ Q.X).hom :=
  (toBimodObj S Q).actRight_one

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The right action `q ⊗ s ↦ s • q` of `S` on an `S`-module object is associative. -/
@[reassoc]
lemma whiskerLeft_mul_braiding_smul (Q : Mod C S) :
    Q.X ◁ μ[S] ≫ (β_ Q.X S).hom ≫ γ[S,Q.X] =
      (α_ Q.X S S).inv ≫ ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ S ≫ (β_ Q.X S).hom ≫ γ[S,Q.X] :=
  (toBimodObj S Q).right_assoc

variable {φ} in
/-- A morphism out of `X ⊗ (S ⊗_R N)`, from a morphism out of `X ⊗ (S ⊗ N)` which coequalizes
the two actions of `R`. -/
noncomputable def whiskerLeftExtendDesc (X : C) (N : Mod C R) {Y : C} (k : X ⊗ (S ⊗ N.X) ⟶ Y)
    (hk : X ◁ ((S ◁ φ ≫ μ[S]) ▷ N.X) ≫ k = X ◁ ((α_ S R N.X).hom ≫ S ◁ γ[R,N.X]) ≫ k) :
    X ⊗ (extendScalarsObj φ N).X ⟶ Y :=
  Cofork.IsColimit.desc (isColimitCoforkMapOfIsColimit (tensorLeft X) _ (isColimitExtendπ φ N))
    k hk

omit [IsCommMonObj S] in
variable {φ} in
@[reassoc (attr := simp)]
lemma whiskerLeft_extendπ_whiskerLeftExtendDesc (X : C) (N : Mod C R) {Y : C}
    (k : X ⊗ (S ⊗ N.X) ⟶ Y) (hk) :
    X ◁ extendπ φ N ≫ whiskerLeftExtendDesc X N k hk = k :=
  Cofork.IsColimit.π_desc'
    (isColimitCoforkMapOfIsColimit (tensorLeft X) _ (isColimitExtendπ φ N)) k hk

/-- The map `Q ⊗ (S ⊗ N) ⟶ Q ⊗_R N`, `q ⊗ s ⊗ n ↦ s q ⊗ n`. -/
noncomputable def projectionInvAux (Q : Mod C S) (N : Mod C R) :
    Q.X ⊗ (S ⊗ N.X) ⟶ ((comap φ).obj Q ⊗ N).X :=
  (α_ Q.X S N.X).inv ≫ ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ N.X ≫ tensorObjπ ((comap φ).obj Q) N

lemma projectionInvAux_condition (Q : Mod C S) (N : Mod C R) :
    Q.X ◁ ((S ◁ φ ≫ μ[S]) ▷ N.X) ≫ projectionInvAux φ Q N =
      Q.X ◁ ((α_ S R N.X).hom ≫ S ◁ γ[R,N.X]) ≫ projectionInvAux φ Q N := by
  have h₁ := whiskerLeft_smul_tensorπ ((comap φ).obj Q) N
  change Q.X ◁ γ[R,N.X] ≫ tensorObjπ ((comap φ).obj Q) N =
    (α_ Q.X R N.X).inv ≫ ((β_ Q.X R).hom ≫ φ ▷ Q.X ≫ γ[S,Q.X]) ▷ N.X ≫
      tensorObjπ ((comap φ).obj Q) N at h₁
  have h₂ : (β_ Q.X R).hom ≫ φ ▷ Q.X ≫ γ[S,Q.X] = Q.X ◁ φ ≫ (β_ Q.X S).hom ≫ γ[S,Q.X] := by
    rw [braiding_naturality_right_assoc]
  rw [h₂] at h₁
  have h₃ : Q.X ◁ (S ◁ φ ≫ μ[S]) ≫ (β_ Q.X S).hom ≫ γ[S,Q.X] =
      (α_ Q.X S R).inv ≫ ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ R ≫ Q.X ◁ φ ≫
        (β_ Q.X S).hom ≫ γ[S,Q.X] := by
    rw [MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_mul_braiding_smul,
      ← whisker_exchange_assoc, associator_inv_naturality_right_assoc]
  dsimp only [projectionInvAux]
  calc Q.X ◁ ((S ◁ φ ≫ μ[S]) ▷ N.X) ≫ (α_ Q.X S N.X).inv ≫
        ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ N.X ≫ tensorObjπ ((comap φ).obj Q) N
      = (α_ Q.X (S ⊗ R) N.X).inv ≫ ((α_ Q.X S R).inv ≫ ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ R ≫
          Q.X ◁ φ ≫ (β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ N.X ≫ tensorObjπ ((comap φ).obj Q) N := by
        rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, h₃]
    _ = Q.X ◁ (α_ S R N.X).hom ≫ (α_ Q.X S (R ⊗ N.X)).inv ≫
          ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ (R ⊗ N.X) ≫ ((α_ Q.X R N.X).inv ≫
            (Q.X ◁ φ ≫ (β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ N.X ≫
              tensorObjπ ((comap φ).obj Q) N) := by
        monoidal
    _ = _ := by
        rw [← h₁, MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
          whisker_exchange_assoc]

/-- The map `Q ⊗ (S ⊗_R N) ⟶ Q ⊗_R N`, `q ⊗ (s ⊗ n) ↦ s q ⊗ n`. -/
noncomputable def projectionInvAuxDesc (Q : Mod C S) (N : Mod C R) :
    Q.X ⊗ (extendScalarsObj φ N).X ⟶ ((comap φ).obj Q ⊗ N).X :=
  whiskerLeftExtendDesc Q.X N (projectionInvAux φ Q N) (projectionInvAux_condition φ Q N)

@[reassoc (attr := simp)]
lemma whiskerLeft_extendπ_projectionInvAuxDesc (Q : Mod C S) (N : Mod C R) :
    Q.X ◁ extendπ φ N ≫ projectionInvAuxDesc φ Q N = projectionInvAux φ Q N :=
  whiskerLeft_extendπ_whiskerLeftExtendDesc _ _ _ _

lemma projectionInvAuxDesc_balanced (Q : Mod C S) (N : Mod C R) :
    ((β_ Q.X S).hom ≫ γ[S,Q.X]) ▷ (extendScalarsObj φ N).X ≫ projectionInvAuxDesc φ Q N =
      ((α_ Q.X S (extendScalarsObj φ N).X).hom ≫ Q.X ◁ γ[S,(extendScalarsObj φ N).X]) ≫
        projectionInvAuxDesc φ Q N := by
  rw [← cancel_epi ((Q.X ⊗ S) ◁ extendπ φ N)]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_projectionInvAuxDesc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_extendπ_smul, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_extendπ_projectionInvAuxDesc]
  dsimp only [projectionInvAux]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_mul_braiding_smul]
  monoidal

/-- The inverse `Q ⊗_S (S ⊗_R N) ⟶ Q ⊗_R N` of the projection formula map, on the underlying
objects: `q ⊗ (s ⊗ n) ↦ s q ⊗ n`. -/
noncomputable def projectionInvX (Q : Mod C S) (N : Mod C R) :
    (Q ⊗ extendScalarsObj φ N).X ⟶ ((comap φ).obj Q ⊗ N).X :=
  tensorObjDesc _ _ (projectionInvAuxDesc φ Q N) (projectionInvAuxDesc_balanced φ Q N)

@[reassoc (attr := simp)]
lemma tensorObjπ_projectionInvX (Q : Mod C S) (N : Mod C R) :
    tensorObjπ Q (extendScalarsObj φ N) ≫ projectionInvX φ Q N = projectionInvAuxDesc φ Q N :=
  tensorObjπ_tensorObjDesc _ _ _ _

omit [IsCommMonObj S] in
@[reassoc]
lemma tensorObjπ_tensorHom_hom_whisker {M M' N N' : Mod C R} (f : M ⟶ M') (g : N ⟶ N') :
    tensorObjπ M N ≫ (f ⊗ₘ g).hom = f.hom ▷ N.X ≫ M'.X ◁ g.hom ≫ tensorObjπ M' N' := by
  change tensorObjπ M N ≫ (f ▷ N ≫ M' ◁ g).hom = _
  rw [comp_hom', tensorObjπ_whiskerRight_assoc, tensorObjπ_whiskerLeft]

/-- The projection formula map `Q ⊗_R N ⟶ Q ⊗_S (S ⊗_R N)`, `q ⊗ n ↦ q ⊗ (1 ⊗ n)`, for an
`S`-module `Q` and an `R`-module `N`. -/
noncomputable def projectionHom (Q : Mod C S) (N : Mod C R) :
    (comap φ).obj Q ⊗ N ⟶ (comap φ).obj (Q ⊗ extendScalarsObj φ N) :=
  (comap φ).obj Q ◁ extendUnit φ N ≫ comapTensorHom φ Q (extendScalarsObj φ N)

@[reassoc (attr := simp)]
lemma tensorObjπ_projectionHom_hom (Q : Mod C S) (N : Mod C R) :
    tensorObjπ ((comap φ).obj Q) N ≫ (projectionHom φ Q N).hom =
      Q.X ◁ extendUnitHom φ N ≫ tensorObjπ Q (extendScalarsObj φ N) := by
  rw [projectionHom, comp_hom', tensorObjπ_whiskerLeft_assoc, extendUnit_hom]
  exact Q.X ◁ extendUnitHom φ N ≫= tensorObjπ_comapTensorHom_hom φ Q (extendScalarsObj φ N)

lemma projectionHom_hom_projectionInvX (Q : Mod C S) (N : Mod C R) :
    (projectionHom φ Q N).hom ≫ projectionInvX φ Q N = 𝟙 _ := by
  rw [← cancel_epi (tensorObjπ ((comap φ).obj Q) N), tensorObjπ_projectionHom_hom_assoc,
    tensorObjπ_projectionInvX, Category.comp_id, extendUnitHom,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_extendπ_projectionInvAuxDesc]
  dsimp only [projectionInvAux]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_one_braiding_smul]
  monoidal

lemma projectionInvX_projectionHom_hom (Q : Mod C S) (N : Mod C R) :
    projectionInvX φ Q N ≫ (projectionHom φ Q N).hom = 𝟙 _ := by
  rw [← cancel_epi (tensorObjπ Q (extendScalarsObj φ N)), ← cancel_epi (Q.X ◁ extendπ φ N),
    tensorObjπ_projectionInvX_assoc, whiskerLeft_extendπ_projectionInvAuxDesc_assoc,
    Category.comp_id]
  dsimp only [projectionInvAux]
  rw [Category.assoc, Category.assoc, tensorObjπ_projectionHom_hom, ← whisker_exchange_assoc,
    tensorObjπ_condition, Category.assoc, associator_naturality_right_assoc,
    Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_extendUnitHom_smul']

instance isIso_projectionHom (Q : Mod C S) (N : Mod C R) : IsIso (projectionHom φ Q N) := by
  have : IsIso ((forget R).map (projectionHom φ Q N)) :=
    ⟨projectionInvX φ Q N, projectionHom_hom_projectionInvX φ Q N,
      projectionInvX_projectionHom_hom φ Q N⟩
  exact isIso_of_reflects_iso _ (forget R)

/-- **The projection formula** for extension of scalars: for an `S`-module `Q` and an
`R`-module `N`, the map `Q ⊗_R N ⟶ Q ⊗_S (S ⊗_R N)`, `q ⊗ n ↦ q ⊗ (1 ⊗ n)`, is an isomorphism of
`R`-modules. -/
noncomputable def projectionIso (Q : Mod C S) (N : Mod C R) :
    (comap φ).obj Q ⊗ N ≅ (comap φ).obj (Q ⊗ extendScalarsObj φ N) :=
  asIso (projectionHom φ Q N)

@[simp]
lemma projectionIso_hom (Q : Mod C S) (N : Mod C R) :
    (projectionIso φ Q N).hom = projectionHom φ Q N := rfl

@[reassoc]
lemma whiskerLeft_extendUnitHom_tensorObjπ_projectionIso_inv_hom (Q : Mod C S) (N : Mod C R) :
    Q.X ◁ extendUnitHom φ N ≫ tensorObjπ Q (extendScalarsObj φ N) ≫
      (projectionIso φ Q N).inv.hom = tensorObjπ ((comap φ).obj Q) N := by
  rw [← tensorObjπ_projectionHom_hom_assoc, ← comp_hom']
  change _ ≫ ((projectionIso φ Q N).hom ≫ (projectionIso φ Q N).inv).hom = _
  rw [Iso.hom_inv_id, id_hom', Category.comp_id]

lemma projectionHom_naturality {Q Q' : Mod C S} (f : Q ⟶ Q') (N : Mod C R) :
    (comap φ).map f ▷ N ≫ projectionHom φ Q' N =
      projectionHom φ Q N ≫ (comap φ).map (f ▷ extendScalarsObj φ N) := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((comap φ).obj Q) N), comp_hom', comp_hom',
    tensorObjπ_whiskerRight_assoc, tensorObjπ_projectionHom_hom, tensorObjπ_projectionHom_hom_assoc]
  change f.hom ▷ N.X ≫ _ ≫ _ = _ ≫ _ ≫ (f ▷ extendScalarsObj φ N).hom
  rw [tensorObjπ_whiskerRight, whisker_exchange_assoc]

end Projection

/-! ### Extension of scalars is strong monoidal -/

section ExtendScalars

open Functor.OplaxMonoidal

omit [IsCommMonObj S] in
lemma extendRestrictAdjunction_unit_app (M : Mod C R) :
    (extendRestrictAdjunction φ).unit.app M = extendUnit φ M :=
  Mod.hom_ext _ _ (Category.comp_id _)

/-- Extension of scalars `S ⊗_R -` is oplax monoidal, by doctrinal adjunction from the lax
monoidal structure `Mod.comapLaxMonoidal` of restriction of scalars. -/
@[instance_reducible]
noncomputable def extendScalarsOplaxMonoidal : (extendScalars φ).OplaxMonoidal :=
  let := comapLaxMonoidal φ
  (extendRestrictAdjunction φ).leftAdjointOplaxMonoidal

/-- The comonoidal structure of extension of scalars is adjoint to `m ⊗ n ↦ (1 ⊗ m) ⊗ (1 ⊗ n)`. -/
lemma extendScalarsOplaxMonoidal_δ (M N : Mod C R) :
    letI := extendScalarsOplaxMonoidal φ
    δ (extendScalars φ) M N = extendHom φ ((extendUnit φ M ⊗ₘ extendUnit φ N) ≫
      comapTensorHom φ (extendScalarsObj φ M) (extendScalarsObj φ N)) := by
  let := comapLaxMonoidal φ
  change ((extendRestrictAdjunction φ).homEquiv _ _).symm
    (((extendRestrictAdjunction φ).unit.app M ⊗ₘ (extendRestrictAdjunction φ).unit.app N) ≫
      comapTensorHom φ _ _) = _
  rw [extendRestrictAdjunction_unit_app, extendRestrictAdjunction_unit_app]
  unfold extendRestrictAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit comparison of extension of scalars is adjoint to `φ : R ⟶ S`. -/
lemma extendScalarsOplaxMonoidal_η :
    letI := extendScalarsOplaxMonoidal φ
    Functor.OplaxMonoidal.η (extendScalars φ) = extendHom φ (comapUnitHom φ) := by
  let := comapLaxMonoidal φ
  change ((extendRestrictAdjunction φ).homEquiv _ _).symm (comapUnitHom φ) = _
  unfold extendRestrictAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The comonoidal structure of extension of scalars on generators:
`s ⊗ (m ⊗ n) ↦ (s ⊗ m) ⊗ (1 ⊗ n)`. -/
@[reassoc]
lemma whiskerLeft_tensorObjπ_extendπ_δ_hom (M N : Mod C R) :
    letI := extendScalarsOplaxMonoidal φ
    S ◁ tensorObjπ M N ≫ extendπ φ (M ⊗ N) ≫ (δ (extendScalars φ) M N).hom =
      (α_ S M.X N.X).inv ≫ extendπ φ M ▷ N.X ≫
        (extendScalarsObj φ M).X ◁ extendUnitHom φ N ≫
          tensorObjπ (extendScalarsObj φ M) (extendScalarsObj φ N) := by
  rw [extendScalarsOplaxMonoidal_δ, extendπ_extendHom,
    ← MonoidalCategory.whiskerLeft_comp_assoc, comp_hom', tensorObjπ_tensorHom_hom_whisker_assoc,
    extendUnit_hom, extendUnit_hom]
  erw [tensorObjπ_comapTensorHom_hom]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_tensorπ_smul]
  change S ◁ extendUnitHom φ M ▷ N.X ≫ S ◁ (extendScalarsObj φ M).X ◁ extendUnitHom φ N ≫
    (α_ S (extendScalarsObj φ M).X (extendScalarsObj φ N).X).inv ≫
      γ[S,(extendScalarsObj φ M).X] ▷ (extendScalarsObj φ N).X ≫
        tensorObjπ (extendScalarsObj φ M) (extendScalarsObj φ N) = _
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_extendUnitHom_smul']

/-- The unit comparison of extension of scalars on generators: `s ⊗ r ↦ s φ(r)`. -/
@[reassoc]
lemma extendπ_η_hom :
    letI := extendScalarsOplaxMonoidal φ
    extendπ φ (𝟙_ (Mod C R)) ≫ (Functor.OplaxMonoidal.η (extendScalars φ)).hom = S ◁ φ ≫ μ[S] := by
  rw [extendScalarsOplaxMonoidal_η, extendπ_extendHom]
  rfl

/-- The inverse `S ⟶ S ⊗_R R`, `s ↦ s ⊗ 1`, of the unit comparison of extension of scalars. -/
noncomputable def extendScalarsUnitInv : S ⟶ (extendScalarsObj φ (𝟙_ (Mod C R))).X :=
  (ρ_ S).inv ≫ S ◁ η[R] ≫ extendπ φ (𝟙_ (Mod C R))

omit [IsCommMonObj S] in
lemma mul_comp_extendScalarsUnitInv :
    (S ◁ φ ≫ μ[S]) ≫ extendScalarsUnitInv φ = extendπ φ (𝟙_ (Mod C R)) := by
  rw [extendScalarsUnitInv, rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
  have hc : (S ◁ φ ≫ μ[S]) ▷ R ≫ extendπ φ (𝟙_ (Mod C R)) =
      (α_ S R R).hom ≫ S ◁ μ[R] ≫ extendπ φ (𝟙_ (Mod C R)) := by
    have := extendπ_condition φ (𝟙_ (Mod C R))
    rw [Category.assoc] at this
    exact this
  change (ρ_ (S ⊗ R)).inv ≫ (S ⊗ R) ◁ η[R] ≫ (S ◁ φ ≫ μ[S]) ▷ R ≫
    extendπ φ (𝟙_ (Mod C R)) = _
  rw [hc]
  have : (ρ_ (S ⊗ R)).inv ≫ (S ⊗ R) ◁ η[R] ≫ (α_ S R R).hom =
      S ◁ ((ρ_ R).inv ≫ R ◁ η[R]) := by
    monoidal
  rw [reassoc_of% this, ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc,
    MonObj.mul_one, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]

lemma isIso_extendScalarsOplaxMonoidal_η :
    letI := extendScalarsOplaxMonoidal φ
    IsIso (Functor.OplaxMonoidal.η (extendScalars φ)) := by
  let := extendScalarsOplaxMonoidal φ
  have h₁ : (Functor.OplaxMonoidal.η (extendScalars φ)).hom ≫ extendScalarsUnitInv φ = 𝟙 _ := by
    rw [← cancel_epi (extendπ φ (𝟙_ (Mod C R)))]
    erw [Category.comp_id]
    rw [← Category.assoc, extendπ_η_hom]
    exact mul_comp_extendScalarsUnitInv φ
  have h₂ : extendScalarsUnitInv φ ≫ (Functor.OplaxMonoidal.η (extendScalars φ)).hom = 𝟙 _ := by
    rw [extendScalarsUnitInv, Category.assoc, Category.assoc, extendπ_η_hom]
    change (ρ_ S).inv ≫ S ◁ η[R] ≫ S ◁ φ ≫ μ[S] = 𝟙 S
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, IsMonHom.one_hom, MonObj.mul_one,
      Iso.inv_hom_id]
  have : IsIso ((forget S).map (Functor.OplaxMonoidal.η (extendScalars φ))) :=
    ⟨extendScalarsUnitInv φ, h₁, h₂⟩
  exact isIso_of_reflects_iso _ (forget S)

/-- The inverse of the left unitor of `S ⊗_R X` on generators: `s ⊗ x ↦ s ⊗ (1 ⊗ x)`. -/
@[reassoc]
lemma extendπ_leftUnitor_inv_hom (X : Mod C R) :
    extendπ φ X ≫ (λ_ (extendScalarsObj φ X)).inv.hom =
      S ◁ extendUnitHom φ X ≫ tensorObjπ (𝟙_ (Mod C S)) (extendScalarsObj φ X) := by
  have h : γ[S,(extendScalarsObj φ X).X] ≫ (λ_ (extendScalarsObj φ X)).inv.hom =
      tensorObjπ (𝟙_ (Mod C S)) (extendScalarsObj φ X) := by
    rw [← cancel_mono (λ_ (extendScalarsObj φ X)).hom.hom, Category.assoc, ← comp_hom',
      Iso.inv_hom_id, id_hom', Category.comp_id]
    exact (tensorObjπ_regular_leftUnitor_hom (extendScalarsObj φ X)).symm
  rw [← whiskerLeft_extendUnitHom_smul' φ X, Category.assoc, h]

@[reassoc]
lemma whiskerLeft_extendUnitHom_tensorObjπ_unit_projectionIso_inv_hom (N : Mod C R) :
    S ◁ extendUnitHom φ N ≫ tensorObjπ (𝟙_ (Mod C S)) (extendScalarsObj φ N) ≫
      (projectionIso φ (𝟙_ (Mod C S)) N).inv.hom =
        tensorObjπ ((comap φ).obj (𝟙_ (Mod C S))) N :=
  whiskerLeft_extendUnitHom_tensorObjπ_projectionIso_inv_hom φ (𝟙_ _) N

@[reassoc]
lemma whiskerLeft_tensorObjπ_tensorObjπ_unit_associator_inv_hom (M N : Mod C R) :
    S ◁ tensorObjπ M N ≫ tensorObjπ ((comap φ).obj (𝟙_ (Mod C S))) (M ⊗ N) ≫
      (α_ ((comap φ).obj (𝟙_ (Mod C S))) M N).inv.hom =
        (α_ S M.X N.X).inv ≫ tensorObjπ ((comap φ).obj (𝟙_ (Mod C S))) M ▷ N.X ≫
          tensorObjπ ((comap φ).obj (𝟙_ (Mod C S)) ⊗ M) N :=
  tensorObjπ_associator_inv ((comap φ).obj (𝟙_ (Mod C S))) M N

lemma tensorObjπ_unit_projectionHom_hom_leftUnitor_hom (M : Mod C R) :
    tensorObjπ ((comap φ).obj (𝟙_ (Mod C S))) M ≫ (projectionHom φ (𝟙_ (Mod C S)) M).hom ≫
      ((comap φ).map (λ_ (extendScalarsObj φ M)).hom).hom = extendπ φ M := by
  rw [tensorObjπ_projectionHom_hom_assoc]
  change S ◁ extendUnitHom φ M ≫ tensorObjπ (regular S) (extendScalarsObj φ M) ≫
    (λ_ (extendScalarsObj φ M)).hom.hom = _
  rw [tensorObjπ_regular_leftUnitor_hom, whiskerLeft_extendUnitHom_smul']

/-- The isomorphism `S ⊗_R (M ⊗_R N) ≅ (S ⊗_R M) ⊗_S (S ⊗_R N)` of `R`-modules obtained from the
unitors, the associator and the projection formula. It is the restriction of scalars of the
comonoidal structure of extension of scalars (`Mod.comap_map_δ_extendScalars`). -/
noncomputable def extendTensorIso (M N : Mod C R) :
    (comap φ).obj (extendScalarsObj φ (M ⊗ N)) ≅
      (comap φ).obj (extendScalarsObj φ M ⊗ extendScalarsObj φ N) :=
  (comap φ).mapIso (λ_ (extendScalarsObj φ (M ⊗ N))).symm ≪≫
    (projectionIso φ (𝟙_ (Mod C S)) (M ⊗ N)).symm ≪≫
      (α_ ((comap φ).obj (𝟙_ (Mod C S))) M N).symm ≪≫
        whiskerRightIso (projectionIso φ (𝟙_ (Mod C S)) M ≪≫
          (comap φ).mapIso (λ_ (extendScalarsObj φ M))) N ≪≫
          projectionIso φ (extendScalarsObj φ M) N

lemma comap_map_δ_extendScalars (M N : Mod C R) :
    letI := extendScalarsOplaxMonoidal φ
    (comap φ).map (δ (extendScalars φ) M N) = (extendTensorIso φ M N).hom := by
  let := extendScalarsOplaxMonoidal φ
  apply Mod.hom_ext
  rw [← cancel_epi (extendπ φ (M ⊗ N)), ← cancel_epi (S ◁ tensorObjπ M N)]
  change S ◁ tensorObjπ M N ≫ extendπ φ (M ⊗ N) ≫ (δ (extendScalars φ) M N).hom = _
  rw [whiskerLeft_tensorObjπ_extendπ_δ_hom]
  simp only [extendTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, comp_hom',
    whiskerRightIso_hom, comap_map_hom]
  rw [extendπ_leftUnitor_inv_hom_assoc,
    whiskerLeft_extendUnitHom_tensorObjπ_unit_projectionIso_inv_hom_assoc,
    whiskerLeft_tensorObjπ_tensorObjπ_unit_associator_inv_hom_assoc,
    tensorObjπ_whiskerRight_assoc, ← comp_whiskerRight_assoc, comp_hom', projectionIso_hom,
    projectionIso_hom, tensorObjπ_unit_projectionHom_hom_leftUnitor_hom,
    tensorObjπ_projectionHom_hom]

lemma isIso_extendScalarsOplaxMonoidal_δ (M N : Mod C R) :
    letI := extendScalarsOplaxMonoidal φ
    IsIso (δ (extendScalars φ) M N) := by
  let := extendScalarsOplaxMonoidal φ
  have : IsIso ((comap φ).map (δ (extendScalars φ) M N)) := by
    rw [comap_map_δ_extendScalars]
    infer_instance
  have : IsIso ((forget S).map (δ (extendScalars φ) M N)) :=
    inferInstanceAs (IsIso ((comap φ).map (δ (extendScalars φ) M N)).hom)
  exact isIso_of_reflects_iso _ (forget S)

/-- **Extension of scalars is strong monoidal**: for a morphism `φ : R ⟶ S` of commutative
algebra objects, `S ⊗_R (M ⊗_R N) ≅ (S ⊗_R M) ⊗_S (S ⊗_R N)` and `S ⊗_R R ≅ S`. The comonoidal
structure is the one of `Mod.extendScalarsOplaxMonoidal`, obtained by doctrinal adjunction. -/
@[instance_reducible]
noncomputable def extendScalarsMonoidal : (extendScalars φ).Monoidal :=
  letI := extendScalarsOplaxMonoidal φ
  haveI := isIso_extendScalarsOplaxMonoidal_η φ
  haveI := isIso_extendScalarsOplaxMonoidal_δ φ
  (Functor.CoreMonoidal.ofOplaxMonoidal _).toMonoidal

lemma extendScalarsMonoidal_toOplaxMonoidal :
    (extendScalarsMonoidal φ).toOplaxMonoidal = extendScalarsOplaxMonoidal φ :=
  rfl


end ExtendScalars

end CategoryTheory.Mod

/-! ### Compatibility with the braidings -/

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- Restriction of scalars is lax braided for the symmetric structures of
`Mod.symmetricCategory`. -/
@[instance_reducible]
noncomputable def comapLaxBraided : (comap φ : Mod C S ⥤ Mod C R).LaxBraided :=
  letI := comapLaxMonoidal φ
  { braided M N := by
      apply Mod.hom_ext
      rw [← cancel_epi (tensorObjπ ((comap φ).obj M) ((comap φ).obj N))]
      change tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ≫ (comapTensorHom φ M N).hom ≫
          braidingHomX M N =
        tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ≫
          braidingHomX ((comap φ).obj M) ((comap φ).obj N) ≫ (comapTensorHom φ N M).hom
      rw [tensorObjπ_comapTensorHom_hom_assoc, tensorObjπ_braidingHomX,
        tensorObjπ_braidingHomX_assoc, tensorObjπ_comapTensorHom_hom]
      rfl }

/-- The comonoidal structure of extension of scalars is compatible with the braidings. -/
lemma extendScalars_map_braiding_hom_δ (M N : Mod C R) :
    letI := extendScalarsMonoidal φ
    (extendScalars φ).map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ (extendScalars φ) N M =
      Functor.OplaxMonoidal.δ (extendScalars φ) M N ≫
        (β_ ((extendScalars φ).obj M) ((extendScalars φ).obj N)).hom := by
  let := comapLaxBraided φ
  exact ((extendRestrictAdjunction φ).leftAdjointOplaxMonoidal_δ_braiding M N).symm

end CategoryTheory.Mod

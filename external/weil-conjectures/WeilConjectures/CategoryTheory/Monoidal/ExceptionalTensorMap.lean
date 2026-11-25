/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The exceptional tensor map and exceptional base change

Let `L ⊣ R` be an adjunction (think `f_! ⊣ f^!`) with `L : 𝒳 ⥤ 𝒴`, let `F : 𝒴 ⥤ 𝒳` be a monoidal
functor (think `f^*`) and let `pf : L A ⊗ B ⟶ L (A ⊗ F B)` be a projection isomorphism.

## Main definitions

- `CategoryTheory.Adjunction.tensorMapOfProjection`: the map `R N ⊗ F K ⟶ R (N ⊗ K)`, the
  adjoint of `L (R N ⊗ F K) ≅ L R N ⊗ K ⟶ N ⊗ K`.
- `CategoryTheory.Adjunction.exceptionalTensorMap`: the map `F K ⊗ R 𝟙 ⟶ R K` (the purity map
  `f^* K ⊗ f^! 𝟙 ⟶ f^! K`).
- `CategoryTheory.Adjunction.exceptionalBaseChange`: for a square of adjunctions with an
  invertible base change `L ⋙ v ≅ u ⋙ L'`, the map `u R N ⟶ R' v N`
  (the exceptional base change `g'^* f^! ⟶ f'^! g^*`).

## Main statements

- `CategoryTheory.Adjunction.isIso_exceptionalTensorMap`: if `pf` is compatible with the unit and
  the tensor structure of `F` (the axioms of a module functor), the exceptional tensor map is an
  isomorphism on objects with a left dual.
- `CategoryTheory.Adjunction.isIso_exceptionalBaseChange`: if the right adjoints of `v` and `u`
  are fully faithful (the counits are isomorphisms), the exceptional base change is an
  isomorphism on objects in the essential image of the right adjoint of `v`.

## Implementation notes

Without the compatibilities of `pf` with the monoidal structure of `F` the exceptional tensor map
need not be an isomorphism on dualizable objects: in `Rep(S₃)` over `ℂ` with `F = 𝟭`,
`L = R = - ⊗ V` (`V` the two-dimensional irreducible representation, which is self-dual), the
standard projection isomorphism can be twisted by an arbitrary automorphism of `V ⊗ V ⊗ V` on the
`(V, V)`-isotypic component, which makes the map at `K = V` a non-invertible endomorphism of
`V ⊗ V`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Adjunction

section TensorMap

variable {𝒳 𝒴 : Type*} [Category* 𝒳] [Category* 𝒴] [MonoidalCategory 𝒳] [MonoidalCategory 𝒴]
  {F : 𝒴 ⥤ 𝒳} {L : 𝒳 ⥤ 𝒴} {R : 𝒴 ⥤ 𝒳} (adj : L ⊣ R)
  (pf : curriedTensorInsertFunctor₁ L ⟶
    curriedTensorPost L ⋙ (Functor.whiskeringLeft 𝒴 𝒳 𝒴).obj F)
  [∀ A B, IsIso ((pf.app A).app B)]

/-- The map `R N ⊗ F K ⟶ R (N ⊗ K)` induced by a projection isomorphism
`pf : L A ⊗ B ≅ L (A ⊗ F B)`: the adjoint of
`L (R N ⊗ F K) ≅ L R N ⊗ K --ε ⊗ 1--> N ⊗ K`. -/
noncomputable def tensorMapOfProjection (N K : 𝒴) : R.obj N ⊗ F.obj K ⟶ R.obj (N ⊗ K) :=
  adj.homEquiv _ _ (inv ((pf.app (R.obj N)).app K) ≫ adj.counit.app N ▷ K)

/-- The components `L A ⊗ K' ⟶ L (A ⊗ F K')` of a projection morphism at a fixed object `K'`, as
a natural transformation `L ⋙ (- ⊗ K') ⟶ (- ⊗ F K') ⋙ L`. -/
@[simps]
def projectionAt (K' : 𝒴) : L ⋙ tensorRight K' ⟶ tensorRight (F.obj K') ⋙ L where
  app A := (pf.app A).app K'
  naturality _ _ φ := NatTrans.congr_app (pf.naturality φ) K'

instance (K' : 𝒴) (A : 𝒳) : IsIso ((projectionAt pf K').app A) := by
  rw [projectionAt_app]
  infer_instance

instance (K' : 𝒴) : IsIso (projectionAt pf K') :=
  NatIso.isIso_of_isIso_app _

/-- If `K'` is a left dual of `K` and `pf` is compatible with the unit and the tensor structure
of `F`, then `tensorMapOfProjection` at `K` is the conjugate of the projection isomorphism at
`K'`, for the adjunctions `L ⋙ (- ⊗ K') ⊣ (- ⊗ K) ⋙ R` and `(- ⊗ F K') ⋙ L ⊣ R ⋙ (- ⊗ F K)`. -/
lemma tensorMapOfProjection_eq_conjugateEquiv [F.Monoidal]
    (hunit : ∀ A, (pf.app A).app (𝟙_ 𝒴) = (ρ_ (L.obj A)).hom ≫ L.map ((ρ_ A).inv ≫ A ◁ ε F))
    (hassoc : ∀ A B C, (pf.app A).app (B ⊗ C) = (α_ _ _ _).inv ≫ ((pf.app A).app B ▷ C) ≫
      (pf.app (A ⊗ F.obj B)).app C ≫ L.map ((α_ _ _ _).hom ≫ A ◁ μ F B C))
    (K' K : 𝒴) [ExactPairing K' K] (N : 𝒴) :
    letI := ExactPairing.map F K' K
    adj.tensorMapOfProjection pf N K =
      (conjugateEquiv ((tensorRightAdjunction (F.obj K') (F.obj K)).comp adj)
        (adj.comp (tensorRightAdjunction K' K)) (projectionAt pf K')).app N := by
  let := ExactPairing.map F K' K
  apply ((adj.comp (tensorRightAdjunction K' K)).homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, conjugateEquiv_counit]
  have hev : ε_ (F.obj K') (F.obj K) = μ F K K' ≫ F.map (ε_ K' K) ≫ η F := rfl
  have h₁ : L.map (adj.tensorMapOfProjection pf N K) ≫ adj.counit.app (N ⊗ K) =
      inv ((pf.app (R.obj N)).app K) ≫ adj.counit.app N ▷ K :=
    (adj.homEquiv _ _).symm_apply_apply _
  have h₂ : (pf.app (R.obj N ⊗ F.obj K)).app K' ≫
      L.map ((α_ _ _ _).hom ≫ R.obj N ◁ μ F K K') =
      inv ((pf.app (R.obj N)).app K) ▷ K' ≫ (α_ _ _ _).hom ≫ (pf.app (R.obj N)).app (K ⊗ K') := by
    rw [hassoc]
    simp
  have h₃ := ((pf.app (R.obj N)).naturality (ε_ K' K)).symm
  have h₄ : (pf.app (R.obj N)).app (𝟙_ 𝒴) ≫ L.map (R.obj N ◁ η F ≫ (ρ_ _).hom) =
      (ρ_ _).hom := by
    rw [hunit, Category.assoc, ← L.map_comp]
    simp
  dsimp at h₃
  dsimp
  simp only [comp_counit_app, projectionAt_app, Functor.flip_obj_map, curriedTensor_map_app,
    Functor.flip_obj_obj, curriedTensor_obj_obj,
    tensorRightAdjunction_counit_app, hev,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [← comp_whiskerRight_assoc, h₁, ← L.map_comp_assoc, reassoc_of% h₂, reassoc_of% h₃,
    ← L.map_comp_assoc, reassoc_of% h₄, comp_whiskerRight_assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- If `K'` is a left dual of `K` and `pf` is compatible with the unit and the tensor structure
of `F`, then `tensorMapOfProjection : R N ⊗ F K ⟶ R (N ⊗ K)` is an isomorphism. -/
theorem isIso_tensorMapOfProjection [F.Monoidal]
    (hunit : ∀ A, (pf.app A).app (𝟙_ 𝒴) = (ρ_ (L.obj A)).hom ≫ L.map ((ρ_ A).inv ≫ A ◁ ε F))
    (hassoc : ∀ A B C, (pf.app A).app (B ⊗ C) = (α_ _ _ _).inv ≫ ((pf.app A).app B ▷ C) ≫
      (pf.app (A ⊗ F.obj B)).app C ≫ L.map ((α_ _ _ _).hom ≫ A ◁ μ F B C))
    (K' K : 𝒴) [ExactPairing K' K] (N : 𝒴) :
    IsIso (adj.tensorMapOfProjection pf N K) := by
  rw [tensorMapOfProjection_eq_conjugateEquiv adj pf hunit hassoc K' K]
  infer_instance

end TensorMap

section ExceptionalTensorMap

variable {𝒳 𝒴 : Type*} [Category* 𝒳] [Category* 𝒴] [MonoidalCategory 𝒳] [MonoidalCategory 𝒴]
  [BraidedCategory 𝒳] {F : 𝒴 ⥤ 𝒳} {L : 𝒳 ⥤ 𝒴} {R : 𝒴 ⥤ 𝒳} (adj : L ⊣ R)
  (pf : curriedTensorInsertFunctor₁ L ⟶
    curriedTensorPost L ⋙ (Functor.whiskeringLeft 𝒴 𝒳 𝒴).obj F)
  [∀ A B, IsIso ((pf.app A).app B)]

/-- The **exceptional tensor map** `F K ⊗ R 𝟙 ⟶ R K` (the purity map
`f^* K ⊗ f^! 𝟙 ⟶ f^! K`): the adjoint of
```
L (F K ⊗ R 𝟙) ≅ L (R 𝟙 ⊗ F K) ≅ L R 𝟙 ⊗ K --ε ⊗ 1--> 𝟙 ⊗ K ≅ K.
``` -/
noncomputable def exceptionalTensorMap (K : 𝒴) : F.obj K ⊗ R.obj (𝟙_ 𝒴) ⟶ R.obj K :=
  adj.homEquiv _ _ (L.map (β_ _ _).hom ≫ inv ((pf.app (R.obj (𝟙_ 𝒴))).app K) ≫
    (adj.counit.app (𝟙_ 𝒴) ▷ K) ≫ (λ_ K).hom)

/-- The exceptional tensor map is the braiding followed by `tensorMapOfProjection` at `𝟙` and the
left unitor. -/
lemma exceptionalTensorMap_eq (K : 𝒴) :
    adj.exceptionalTensorMap pf K =
      (β_ (F.obj K) (R.obj (𝟙_ 𝒴))).hom ≫ adj.tensorMapOfProjection pf (𝟙_ 𝒴) K ≫
        R.map (λ_ K).hom := by
  rw [exceptionalTensorMap, tensorMapOfProjection, ← homEquiv_naturality_right,
    ← homEquiv_naturality_left, Category.assoc]

/-- **The exceptional tensor map is an isomorphism on dualizable objects**: if `K'` is a left dual
of `K` and the projection isomorphism `pf : L A ⊗ B ≅ L (A ⊗ F B)` is compatible with the unit
and the tensor structure of `F` (the axioms of a module functor), then
`F K ⊗ R 𝟙 ⟶ R K` is an isomorphism. -/
theorem isIso_exceptionalTensorMap [F.Monoidal]
    (hunit : ∀ A, (pf.app A).app (𝟙_ 𝒴) = (ρ_ (L.obj A)).hom ≫ L.map ((ρ_ A).inv ≫ A ◁ ε F))
    (hassoc : ∀ A B C, (pf.app A).app (B ⊗ C) = (α_ _ _ _).inv ≫ ((pf.app A).app B ▷ C) ≫
      (pf.app (A ⊗ F.obj B)).app C ≫ L.map ((α_ _ _ _).hom ≫ A ◁ μ F B C))
    (K' K : 𝒴) [ExactPairing K' K] :
    IsIso (adj.exceptionalTensorMap pf K) := by
  have := isIso_tensorMapOfProjection adj pf hunit hassoc K' K (𝟙_ 𝒴)
  rw [exceptionalTensorMap_eq]
  infer_instance

end ExceptionalTensorMap

section ExceptionalBaseChange

variable {𝒳 𝒴 𝒳' 𝒴' : Type*} [Category* 𝒳] [Category* 𝒴] [Category* 𝒳'] [Category* 𝒴']
  {L : 𝒳 ⥤ 𝒴} {R : 𝒴 ⥤ 𝒳} {L' : 𝒳' ⥤ 𝒴'} {R' : 𝒴' ⥤ 𝒳'} {v : 𝒴 ⥤ 𝒴'} {vs : 𝒴' ⥤ 𝒴}
  {u : 𝒳 ⥤ 𝒳'} {us : 𝒳' ⥤ 𝒳} (a : L ⊣ R) (a' : L' ⊣ R') (av : v ⊣ vs) (au : u ⊣ us)
  (bc : L ⋙ v ⟶ u ⋙ L') [IsIso bc]

/-- The **exceptional base change** `u R N ⟶ R' v N` (the map `g'^* f^! ⟶ f'^! g^*`) of an
invertible base change `bc : L ⋙ v ≅ u ⋙ L'`: the adjoint of
`L' u R N ≅ v L R N --v ε--> v N`. -/
noncomputable def exceptionalBaseChange (N : 𝒴) : u.obj (R.obj N) ⟶ R'.obj (v.obj N) :=
  a'.homEquiv _ _ (inv (bc.app (R.obj N)) ≫ v.map (a.counit.app N))

/-- The exceptional base change at `vs N` followed by `R'` of the counit of `v ⊣ vs` is `u` of the
conjugate `vs ⋙ R ⟶ R' ⋙ us` of the inverse of `bc` followed by the counit of `u ⊣ us`. -/
lemma exceptionalBaseChange_comp_map_counit (N : 𝒴') :
    exceptionalBaseChange a a' bc (vs.obj N) ≫ R'.map (av.counit.app N) =
      u.map ((conjugateEquiv (a.comp av) (au.comp a') (inv bc)).app N) ≫
        au.counit.app (R'.obj N) := by
  apply (a'.homEquiv _ _).symm.injective
  have h := conjugateEquiv_counit (a.comp av) (au.comp a') (inv bc) N
  simp only [Functor.comp_obj, Functor.comp_map, comp_counit_app] at h
  have h₂ : L'.map (exceptionalBaseChange a a' bc (vs.obj N)) ≫ a'.counit.app _ =
      inv (bc.app _) ≫ v.map (a.counit.app _) :=
    (a'.homEquiv _ _).symm_apply_apply _
  rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc]
  refine Eq.trans ?_ h.symm
  simp [reassoc_of% h₂]

/-- **Exceptional base change along fully faithful right adjoints**: if the counits of `v ⊣ vs`
and `u ⊣ us` are isomorphisms, the exceptional base change is an isomorphism at every `vs N`. -/
theorem isIso_exceptionalBaseChange [IsIso av.counit] [IsIso au.counit] (N : 𝒴') :
    IsIso (exceptionalBaseChange a a' bc (vs.obj N)) := by
  have h := exceptionalBaseChange_comp_map_counit a a' av au bc N
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

end ExceptionalBaseChange

section UnitIso

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- If the counit of `L ⊣ R` is an isomorphism at `Y`, then the unit is an isomorphism at every
object isomorphic to `R Y`. -/
lemma isIso_unit_app_of_iso_of_isIso_counit_app (adj : L ⊣ R) {X : C} {Y : D} (e : X ≅ R.obj Y)
    [IsIso (adj.counit.app Y)] : IsIso (adj.unit.app X) := by
  have := adj.isIso_unit_app_obj_of_isIso_counit_app Y
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  infer_instance

/-- **Detection of isomorphisms between objects with invertible unit**: if the unit of `L ⊣ R`
is an isomorphism at `X` and at `X'`, then `f : X ⟶ X'` is an isomorphism as soon as `L f` is,
since `f = η_X ≫ R (L f) ≫ η_{X'}⁻¹`. -/
lemma isIso_of_isIso_map_of_isIso_unit_app (adj : L ⊣ R) {X X' : C} (f : X ⟶ X')
    [IsIso (adj.unit.app X)] [IsIso (adj.unit.app X')] [IsIso (L.map f)] : IsIso f := by
  rw [(IsIso.eq_comp_inv _).mpr (adj.unit_naturality f).symm]
  infer_instance

end UnitIso

end Adjunction

end CategoryTheory

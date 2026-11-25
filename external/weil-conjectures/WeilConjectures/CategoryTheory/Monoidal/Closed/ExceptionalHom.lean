/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Abstract

/-!

# Exceptional internal hom and classes of correspondences for an abstract adjunction

This file continues `WeilConjectures.PoincareDuality.Abstract`, in the same
abstract setting: `C` (for `D(C)`) and `D` (for `D(Z)`) are braided monoidal closed categories,
`F : D ⥤ C` plays the role of `Lc^*`, `adj' : P ⊣ S` the role of `Rc_! ⊣ Rc^!` and
```
pf : (K, B) ↦ P K ⊗ B ⟶ (K, B) ↦ P (K ⊗ F B)
```
the role of the exceptional projection morphism `PF^!`, for a morphism `c : C ⟶ Z`.

## Main definitions

* `CategoryTheory.Verdier.leftProjection`: the projection morphism with the test object on the
  right, `M ⊗ P T ⟶ P (F M ⊗ T)`, obtained from `pf` by the braidings.
* `CategoryTheory.Verdier.exceptionalHomMap`: the exchange morphism
  `RHom(F M, S N) ⟶ S RHom(M, N)`, i.e. `RHom(c^* M, c^! N) ⟶ c^! RHom(M, N)`.
* `CategoryTheory.Verdier.correspondenceClassEquiv`: the bijection
  `Hom(P 𝟙, RHom(M, N)) ≃ Hom(F M, S N)`, i.e.
  `Hom(Rc_! Λ_C, RHom(M, N)) ≃ Hom(Lc^* M, Rc^! N)`, by tensor–hom adjunction, the projection
  formula and the exceptional adjunction.

## Main results

* `CategoryTheory.Verdier.isIso_exceptionalHomMap_of_isIso`: the exchange morphism is an
  isomorphism if the projection morphisms `pf` at `(T, M)` are, by the Yoneda lemma.
* `CategoryTheory.Verdier.curry'_comp_exceptionalHomMap`: the exchange morphism sends the mate
  of `u : F M ⟶ S N` to the exceptional adjoint of its class.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory

section IhomIso

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [MonoidalClosed 𝒞]

/-- The isomorphism `RHom(A, B) ≅ RHom(A', B')` induced by isomorphisms `A ≅ A'` and
`B ≅ B'`. -/
noncomputable def ihomIsoOfIso {A A' B B' : 𝒞} (eA : A ≅ A') (eB : B ≅ B') :
    (ihom A).obj B ≅ (ihom A').obj B' :=
  (ihom A).mapIso eB ≪≫ (internalHom.mapIso eA.symm.op).app B'

/-- Transporting the mate `𝟙 ⟶ RHom(A, B)` of `u : A ⟶ B` along `RHom(A, B) ≅ RHom(A', B')` gives
the mate of the transported map `A' ⟶ A ⟶ B ⟶ B'`. -/
lemma curry'_comp_ihomIsoOfIso_hom {A A' B B' : 𝒞} (u : A ⟶ B) (eA : A ≅ A') (eB : B ≅ B') :
    curry' u ≫ (ihomIsoOfIso eA eB).hom = curry' (eA.inv ≫ u ≫ eB.hom) := by
  rw [ihomIsoOfIso, Iso.trans_hom, Functor.mapIso_hom, curry', ← Category.assoc,
    ← curry_natural_right]
  change curry _ ≫ (pre eA.inv).app B' = _
  rw [curry_pre_app, curry', ← rightUnitor_naturality_assoc]
  simp only [Category.assoc]

end IhomIso

namespace Verdier

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

variable [BraidedCategory C] [BraidedCategory D]
  {F : D ⥤ C} {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S)
  (pf : curriedTensorInsertFunctor₁ P ⟶
    curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)

section LeftProjection

/-- The projection morphism with the test object on the right, `M ⊗ P T ⟶ P (F M ⊗ T)`, i.e.
`M ⊗ Rc_! T ⟶ Rc_! (Lc^* M ⊗ T)`: the projection morphism `pf` conjugated by the braidings. -/
noncomputable def leftProjection (M : D) (T : C) : M ⊗ P.obj T ⟶ P.obj (F.obj M ⊗ T) :=
  (β_ M (P.obj T)).hom ≫ (pf.app T).app M ≫ P.map (β_ T (F.obj M)).hom

/-- Naturality of `leftProjection` in the test object. -/
@[reassoc]
lemma leftProjection_naturality (M : D) {T T' : C} (u : T ⟶ T') :
    M ◁ P.map u ≫ leftProjection pf M T' = leftProjection pf M T ≫ P.map (F.obj M ◁ u) := by
  have h := congrArg (fun φ ↦ NatTrans.app φ M) (pf.naturality u)
  dsimp at h
  simp only [leftProjection, BraidedCategory.braiding_naturality_right_assoc, Category.assoc]
  rw [reassoc_of% h, ← P.map_comp, ← P.map_comp, BraidedCategory.braiding_naturality_left]

instance isIso_leftProjection (M : D) (T : C) [IsIso ((pf.app T).app M)] :
    IsIso (leftProjection pf M T) := by
  dsimp only [leftProjection]
  infer_instance

end LeftProjection

variable [MonoidalClosed C] [MonoidalClosed D]

section ExceptionalHom

/-- The pairing `M ⊗ P RHom(F M, S N) ⟶ N` whose transpose is the exceptional internal hom
exchange: the projection morphism `leftProjection`, the evaluation
`F M ⊗ RHom(F M, S N) ⟶ S N` and the counit `P S ⟶ 𝟭`. -/
noncomputable def exceptionalHomPairing (M N : D) :
    M ⊗ P.obj ((ihom (F.obj M)).obj (S.obj N)) ⟶ N :=
  leftProjection pf M _ ≫ P.map ((ihom.ev (F.obj M)).app (S.obj N)) ≫ adj'.counit.app N

/-- The **exceptional internal hom exchange** `RHom(F M, S N) ⟶ S RHom(M, N)`, i.e.
`RHom(Lc^* M, Rc^! N) ⟶ Rc^! RHom(M, N)`: the exceptional adjoint of the transpose of
`exceptionalHomPairing`. -/
noncomputable def exceptionalHomMap (M N : D) :
    (ihom (F.obj M)).obj (S.obj N) ⟶ S.obj ((ihom M).obj N) :=
  adj'.homEquiv _ _ (curry (exceptionalHomPairing adj' pf M N))

/-- Composing with the exceptional internal hom exchange, read through the adjunctions, is
precomposition with the projection morphism. -/
lemma exceptionalHomMap_comp_eq {T : C} (M N : D) (u : T ⟶ (ihom (F.obj M)).obj (S.obj N)) :
    u ≫ exceptionalHomMap adj' pf M N = adj'.homEquiv _ _
      (curry (leftProjection pf M T ≫ (adj'.homEquiv _ _).symm (uncurry u))) := by
  rw [exceptionalHomMap, ← Adjunction.homEquiv_naturality_left, ← curry_natural_left,
    exceptionalHomPairing, leftProjection_naturality_assoc, Adjunction.homEquiv_counit,
    uncurry_eq, Functor.map_comp, Category.assoc]

/-- **The exceptional internal hom exchange is an isomorphism** (blueprint
`lemma-external-duality-trace-morphism--2`) as soon as the projection morphisms
`(pf.app T).app M` are, for every `T`: by the Yoneda lemma, composing with it is the chain of
bijections
```
Hom(T, RHom(F M, S N)) ≃ Hom(F M ⊗ T, S N) ≃ Hom(P (F M ⊗ T), N) ≃ Hom(M ⊗ P T, N)
  ≃ Hom(P T, RHom(M, N)) ≃ Hom(T, S RHom(M, N)),
```
the third one being precomposition with the isomorphism `leftProjection`. -/
theorem isIso_exceptionalHomMap_of_isIso (M N : D) [∀ T, IsIso ((pf.app T).app M)] :
    IsIso (exceptionalHomMap adj' pf M N) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have e : (fun u : T ⟶ (ihom (F.obj M)).obj (S.obj N) ↦ u ≫ exceptionalHomMap adj' pf M N) =
      adj'.homEquiv _ _ ∘ curry ∘ (fun x ↦ leftProjection pf M T ≫ x) ∘
        (adj'.homEquiv _ _).symm ∘ uncurry := by
    funext u
    exact exceptionalHomMap_comp_eq adj' pf M N u
  rw [e]
  refine (Equiv.bijective _).comp (Function.Bijective.comp
    ⟨curry_injective, fun g ↦ ⟨uncurry g, curry_uncurry g⟩⟩
    (Function.Bijective.comp ⟨fun a b h ↦ (cancel_epi (leftProjection pf M T)).1 h,
      fun y ↦ ⟨inv (leftProjection pf M T) ≫ y, by simp⟩⟩ ((Equiv.bijective _).comp
        ⟨uncurry_injective, fun g ↦ ⟨curry g, uncurry_curry g⟩⟩)))

end ExceptionalHom

section CorrespondenceClass

/-- The bijection `Hom(P 𝟙, RHom(M, N)) ≃ Hom(F M, S N)`, i.e.
`Hom(Rc_! Λ_C, RHom(M, N)) ≃ Hom(Lc^* M, Rc^! N)`: the tensor–hom adjunction, the inverse of the
projection morphism `M ⊗ P 𝟙 ≅ P (F M ⊗ 𝟙)`, the right unitor and the exceptional adjunction
(blueprint `lemma-external-duality-trace-morphism--2`). -/
noncomputable def correspondenceClassEquiv (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)] :
    (P.obj (𝟙_ C) ⟶ (ihom M).obj N) ≃ (F.obj M ⟶ S.obj N) :=
  ((ihom.adjunction M).homEquiv _ _).symm.trans
    (((asIso (leftProjection pf M (𝟙_ C))).trans (P.mapIso (ρ_ (F.obj M)))).homCongr
      (Iso.refl N) |>.trans (adj'.homEquiv _ _))

omit [MonoidalClosed C] in
lemma correspondenceClassEquiv_apply (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    (g : P.obj (𝟙_ C) ⟶ (ihom M).obj N) :
    correspondenceClassEquiv adj' pf M N g = adj'.homEquiv _ _
      (P.map (ρ_ (F.obj M)).inv ≫ inv (leftProjection pf M (𝟙_ C)) ≫ uncurry g) := by
  simp [correspondenceClassEquiv, Iso.homCongr_apply, uncurry_eq]
  rfl

/-- **The exchange of the mate is the adjoint of the class** (blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 1): for `u : F M ⟶ S N` with class
`[u] = correspondenceClassEquiv.symm u`, the exceptional internal hom exchange sends the mate
`𝟙 ⟶ RHom(F M, S N)` of `u` to the exceptional adjoint `𝟙 ⟶ S RHom(M, N)` of `[u]`. -/
theorem curry'_comp_exceptionalHomMap (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    (u : F.obj M ⟶ S.obj N) :
    curry' u ≫ exceptionalHomMap adj' pf M N =
      adj'.homEquiv _ _ ((correspondenceClassEquiv adj' pf M N).symm u) := by
  rw [exceptionalHomMap_comp_eq]
  congr 1
  apply (correspondenceClassEquiv adj' pf M N).injective
  rw [Equiv.apply_symm_apply, correspondenceClassEquiv_apply, uncurry_curry,
    IsIso.inv_hom_id_assoc, curry', uncurry_curry, Adjunction.homEquiv_counit,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc, ← Adjunction.homEquiv_counit,
    Equiv.apply_symm_apply]

/-- The exceptional adjoint of a transported mate followed by the exceptional internal hom exchange
and `S g` is the class of the transported map followed by `g`. -/
lemma homEquiv_symm_curry'_comp_exceptionalHomMap (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    {A B : C} (u : A ⟶ B) (eA : A ≅ F.obj M) (eB : B ≅ S.obj N) {N' : D} (g : (ihom M).obj N ⟶ N') :
    (adj'.homEquiv _ _).symm (curry' u ≫ (ihomIsoOfIso eA eB).hom ≫
        exceptionalHomMap adj' pf M N ≫ S.map g) =
      (correspondenceClassEquiv adj' pf M N).symm (eA.inv ≫ u ≫ eB.hom) ≫ g := by
  rw [← Category.assoc, curry'_comp_ihomIsoOfIso_hom, ← Category.assoc,
    curry'_comp_exceptionalHomMap, ← Adjunction.homEquiv_naturality_right, Equiv.symm_apply_apply]

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- Naturality of `leftProjection` in the object `M`. -/
@[reassoc]
lemma leftProjection_naturality_left {M M' : D} (a : M' ⟶ M) (T : C) :
    a ▷ P.obj T ≫ leftProjection pf M T = leftProjection pf M' T ≫ P.map (F.map a ▷ T) := by
  have h := (pf.app T).naturality a
  dsimp at h
  simp only [leftProjection, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc, reassoc_of% h, ← P.map_comp,
    ← P.map_comp, BraidedCategory.braiding_naturality_right]

omit [MonoidalClosed C] in
/-- The class bijection is natural in the target `N` (blueprint
`lemma-external-duality-trace-morphism--2`). -/
lemma correspondenceClassEquiv_naturality_right (M : D) {N N' : D}
    [IsIso ((pf.app (𝟙_ C)).app M)] (b : N ⟶ N') (g : P.obj (𝟙_ C) ⟶ (ihom M).obj N) :
    correspondenceClassEquiv adj' pf M N' (g ≫ (ihom M).map b) =
      correspondenceClassEquiv adj' pf M N g ≫ S.map b := by
  rw [correspondenceClassEquiv_apply, correspondenceClassEquiv_apply, uncurry_natural_right,
    ← Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]

omit [MonoidalClosed C] in
/-- The class bijection is natural in the source `M` (blueprint
`lemma-external-duality-trace-morphism--2`): precomposing a class with `RHom(a, N)` corresponds to
precomposing with `F a`. -/
lemma correspondenceClassEquiv_naturality_left {M M' : D} (N : D)
    [IsIso ((pf.app (𝟙_ C)).app M)] [IsIso ((pf.app (𝟙_ C)).app M')] (a : M' ⟶ M)
    (g : P.obj (𝟙_ C) ⟶ (ihom M).obj N) :
    correspondenceClassEquiv adj' pf M' N (g ≫ (pre a).app N) =
      F.map a ≫ correspondenceClassEquiv adj' pf M N g := by
  rw [correspondenceClassEquiv_apply, correspondenceClassEquiv_apply, uncurry_pre_app,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  have h := leftProjection_naturality_left pf a (𝟙_ C)
  rw [← cancel_epi (P.map (ρ_ (F.obj M')).hom)]
  simp only [← P.map_comp_assoc, Iso.hom_inv_id, P.map_id, Category.id_comp]
  have hρ : (ρ_ (F.obj M')).hom ≫ F.map a ≫ (ρ_ (F.obj M)).inv = F.map a ▷ 𝟙_ C := by
    rw [MonoidalCategory.rightUnitor_inv_naturality, Iso.hom_inv_id_assoc]
  rw [← cancel_epi (leftProjection pf M' (𝟙_ C)), IsIso.hom_inv_id_assoc, hρ, ← reassoc_of% h,
    IsIso.hom_inv_id_assoc]

omit [MonoidalClosed C] in
/-- `correspondenceClassEquiv_naturality_right` conjugated by a morphism `A ⟶ F M` and a natural
isomorphism `G ≅ H ⋙ S`, in the form used for the concrete six functors. -/
lemma correspondenceClassEquiv_naturality_right_conj (M : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    {E' : Type*} [Category E'] {G : E' ⥤ C} {H : E' ⥤ D} (e : G ≅ H ⋙ S) {A : C}
    (eA : A ⟶ F.obj M) {N N' : E'} (b : N ⟶ N') (g : P.obj (𝟙_ C) ⟶ (ihom M).obj (H.obj N)) :
    eA ≫ correspondenceClassEquiv adj' pf M (H.obj N') (g ≫ (ihom M).map (H.map b)) ≫
        e.inv.app N' =
      (eA ≫ correspondenceClassEquiv adj' pf M (H.obj N) g ≫ e.inv.app N) ≫ G.map b := by
  have h := e.inv.naturality b
  rw [Functor.comp_map] at h
  rw [correspondenceClassEquiv_naturality_right, Category.assoc, Category.assoc,
    Category.assoc, h]

omit [MonoidalClosed C] in
/-- `correspondenceClassEquiv_naturality_left` conjugated by a natural isomorphism `G ≅ H ⋙ F`
and a morphism `S N ⟶ B`, in the form used for the concrete six functors. -/
lemma correspondenceClassEquiv_naturality_left_conj (N : D) {E' : Type*} [Category E']
    {G : E' ⥤ C} {H : E' ⥤ D} (e : G ≅ H ⋙ F) {B : C} (eB : S.obj N ⟶ B) {M M' : E'}
    [IsIso ((pf.app (𝟙_ C)).app (H.obj M))] [IsIso ((pf.app (𝟙_ C)).app (H.obj M'))]
    (a : M' ⟶ M) (g : P.obj (𝟙_ C) ⟶ (ihom (H.obj M)).obj N) :
    e.hom.app M' ≫ correspondenceClassEquiv adj' pf (H.obj M') N (g ≫ (pre (H.map a)).app N) ≫
        eB =
      G.map a ≫ e.hom.app M ≫ correspondenceClassEquiv adj' pf (H.obj M) N g ≫ eB := by
  have h := e.hom.naturality a
  rw [Functor.comp_map] at h
  rw [correspondenceClassEquiv_naturality_left, Category.assoc, reassoc_of% h]

end CorrespondenceClass

end Verdier

end CategoryTheory

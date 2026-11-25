/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Yoneda

/-!
# Units of adjunctions on essential images

For an adjunction `L ⊣ R` whose counit is an isomorphism at `L X`, the two maps
`R (L X) ⟶ R (L (R (L X)))` given by `R (L (η X))` and by `η (R (L X))` agree: both are right
inverse to the isomorphism `R (ε (L X))`.

Let `F ⊣ G` be an adjunction between `C` and `D`, and let `J : U ⥤ C` be a fully faithful functor
with a right adjoint `J'`, such that `J ⋙ F` is again fully faithful. Then the unit
`η : K ⟶ G (F K)` is invisible to `J'` on the essential image of `J`: the map
`J' (η_{J K}) : J' (J K) ⟶ J' (G (F (J K)))` is an isomorphism.

The typical instance is an extension by zero `J = j_!` along an open immersion, with `J' = j^*`,
and `F = q^*` the pullback along a morphism `q` which is an isomorphism over the open subset, so
that `q^* j_! = j'_!` is again fully faithful.

## Main statements

- `CategoryTheory.Adjunction.map_bijective_of_isIso_unit_app`: if the unit is invertible at `B`,
  then `L` is bijective on morphisms with target `B`.
- `CategoryTheory.Adjunction.map_map_unit_app_eq`: `R (L (η X)) = η (R (L X))` when `ε (L X)` is
  an isomorphism.
- `CategoryTheory.Adjunction.isIso_map_unit_app_obj`: `J' (η_{J K})` is an isomorphism.
- `CategoryTheory.Adjunction.isIso_map_counit_app_of_isIso_unit`: `R ε_Y` is an isomorphism when
  the unit is.
- `CategoryTheory.Adjunction.iso_ext_of_inv_app_comp_counit`: an isomorphism `L ≅ 𝟭` from a
  left adjoint `L ⊣ R` with `R ≅ 𝟭` is determined by its composite with the counit.
- `CategoryTheory.Adjunction.isIso_unit_of_fullyFaithful_comp`: the unit of `F ⊣ G` is an
  isomorphism if `F ⋙ F'` is fully faithful and the unit of `F' ⊣ G'` is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C D U : Type*} [Category C] [Category D] [Category U]
  {F : C ⥤ D} {G : D ⥤ C} {J : U ⥤ C} {J' : C ⥤ U}

namespace Adjunction

/-- Let `F ⊣ G`, and let `J` be a fully faithful functor with right adjoint `J'` such that
`J ⋙ F` is fully faithful. Then for every `K`, composing with the unit `η_{J K}` is a bijection
`(J T ⟶ J K) ≃ (J T ⟶ G (F (J K)))` for every `T`. Under the adjunction bijection it is
`f ↦ F f`, which is bijective as `J` and `J ⋙ F` are fully faithful:
```
  (J T ⟶ J K) --(- ≫ η_{J K})--> (J T ⟶ G (F (J K)))
       |                                  |
       F                                  ≅ adj
       v                                  v
  (F (J T) ⟶ F (J K)) ========== (F (J T) ⟶ F (J K))
```
-/
lemma bijective_comp_unit_app_obj (adj : F ⊣ G) [J.Full] [J.Faithful] [(J ⋙ F).Full]
    [(J ⋙ F).Faithful] (T K : U) :
    Function.Bijective (fun f : J.obj T ⟶ J.obj K ↦ f ≫ adj.unit.app (J.obj K)) := by
  have hF : Function.Bijective (fun f : J.obj T ⟶ J.obj K ↦ F.map f) := by
    have e : (fun f : J.obj T ⟶ J.obj K ↦ F.map f) =
        (fun g : T ⟶ K ↦ (J ⋙ F).map g) ∘ (fun f ↦ J.preimage f) := by
      funext f
      simp
    rw [e]
    exact (Functor.FullyFaithful.ofFullyFaithful (J ⋙ F)).map_bijective _ _ |>.comp
      ((Functor.FullyFaithful.ofFullyFaithful J).homEquiv.symm.bijective)
  have e : (fun f : J.obj T ⟶ J.obj K ↦ f ≫ adj.unit.app (J.obj K)) =
      (adj.homEquiv _ _) ∘ (fun f ↦ F.map f) := by
    funext f
    simp [Adjunction.homEquiv_unit]
  rw [e]
  exact (adj.homEquiv _ _).bijective.comp hF

/-- Let `F ⊣ G`, and let `J` be a fully faithful functor with right adjoint `J'` such that
`J ⋙ F` is fully faithful. Then `J'` sends the unit `η_{J K} : J K ⟶ G (F (J K))` to an
isomorphism. By Yoneda it suffices that composing with `J' η_{J K}` is a bijection on maps out
of every `T`; through the bijections of `J ⊣ J'` this is composing with `η_{J K}`, which is
`CategoryTheory.Adjunction.bijective_comp_unit_app_obj`:
```
  (T ⟶ J' (J K)) --(- ≫ J' η_{J K})--> (T ⟶ J' (G (F (J K))))
        |                                       |
        ≅ adjJ                                  ≅ adjJ
        v                                       v
  (J T ⟶ J K) -----(- ≫ η_{J K})-----> (J T ⟶ G (F (J K)))
```
-/
lemma isIso_map_unit_app_obj (adj : F ⊣ G) (adjJ : J ⊣ J') [J.Full] [J.Faithful]
    [(J ⋙ F).Full] [(J ⋙ F).Faithful] (K : U) :
    IsIso (J'.map (adj.unit.app (J.obj K))) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have e : (fun x : T ⟶ J'.obj (J.obj K) ↦ x ≫ J'.map (adj.unit.app (J.obj K))) =
      (adjJ.homEquiv T (G.obj (F.obj (J.obj K)))) ∘ (fun f ↦ f ≫ adj.unit.app (J.obj K)) ∘
        (adjJ.homEquiv T (J.obj K)).symm := by
    funext x
    simp [Adjunction.homEquiv_naturality_right]
  exact (congrArg Function.Bijective e).mpr ((adjJ.homEquiv _ _).bijective.comp
    ((adj.bijective_comp_unit_app_obj T K).comp (adjJ.homEquiv _ _).symm.bijective))

/-- For an adjunction whose counit is an isomorphism at `L X`, the image of the unit at `X`
under `L ⋙ R` is the unit at `R (L X)`. -/
lemma map_map_unit_app_eq {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : C)
    [IsIso (adj.counit.app (L.obj X))] :
    R.map (L.map (adj.unit.app X)) = adj.unit.app (R.obj (L.obj X)) := by
  rw [← cancel_mono (R.map (adj.counit.app (L.obj X)))]
  simp [← R.map_comp]

section UnitIso

variable {L : C ⥤ D} {R : D ⥤ C}

/-- Under the adjunction bijection, `L f` corresponds to `f ≫ η_B`. -/
lemma homEquiv_map (adj : L ⊣ R) {A B : C} (f : A ⟶ B) :
    adj.homEquiv A (L.obj B) (L.map f) = f ≫ adj.unit.app B := by
  rw [adj.homEquiv_unit, adj.unit_naturality]

/-- If the unit `η_B` of `L ⊣ R` is an isomorphism, then `L` is bijective on morphisms with
target `B`. -/
lemma map_bijective_of_isIso_unit_app (adj : L ⊣ R) (A : C) {B : C}
    [IsIso (adj.unit.app B)] :
    Function.Bijective (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B)) := by
  have h : (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B)) =
      (adj.homEquiv A (L.obj B)).symm ∘ fun f ↦ f ≫ adj.unit.app B := by
    ext1 f
    exact ((adj.homEquiv _ _).symm_apply_apply _).symm.trans (congrArg _ (homEquiv_map adj f))
  rw [h]
  exact (adj.homEquiv A (L.obj B)).symm.bijective.comp
    ((asIso (adj.unit.app B)).homToEquiv (Z := A)).bijective

/-- For an adjunction `L ⊣ R` with invertible unit, `R` inverts the counit: by the triangle
identity, `R ε_Y` is a retraction of the invertible `η_{R Y}`. -/
lemma isIso_map_counit_app_of_isIso_unit (adj : L ⊣ R) [IsIso adj.unit] (Y : D) :
    IsIso (R.map (adj.counit.app Y)) := by
  have h := adj.right_triangle_components Y
  have : IsIso (adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y)) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (adj.unit.app (R.obj Y)) _

end UnitIso

/-- An isomorphism `σ : L ≅ 𝟭` from a left adjoint `L ⊣ R` with `R ≅ 𝟭` is determined by the
composite `σ⁻¹_{R W} ≫ ε_W`. -/
lemma iso_ext_of_inv_app_comp_counit {𝒜 : Type*} [Category* 𝒜]
    {L R : 𝒜 ⥤ 𝒜} (adj : L ⊣ R) (e : R ≅ 𝟭 𝒜) (σ σ' : L ≅ 𝟭 𝒜)
    (h : ∀ W, σ.inv.app (R.obj W) ≫ adj.counit.app W = e.hom.app W)
    (h' : ∀ W, σ'.inv.app (R.obj W) ≫ adj.counit.app W = e.hom.app W) : σ = σ' := by
  have : R.Full := Functor.Full.of_iso e.symm
  have : R.Faithful := Functor.Faithful.of_iso e.symm
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  have key : ∀ W, σ.inv.app (R.obj W) = σ'.inv.app (R.obj W) := fun W ↦ by
    rw [← cancel_mono (adj.counit.app W), h, h']
  ext1
  rw [← Iso.inv_eq_inv σ σ']
  ext M
  have hn := σ.inv.naturality (e.hom.app M)
  have hn' := σ'.inv.naturality (e.hom.app M)
  simp only [Functor.id_map] at hn hn'
  rw [← cancel_epi (e.hom.app M)]
  erw [hn, hn', key]

/-- Let `F ⊣ G` and `F' ⊣ G'` be adjunctions such that the left adjoint `F ⋙ F'` of the composite
adjunction is fully faithful and the unit of `F' ⊣ G'` is an isomorphism. Then the unit of
`F ⊣ G` is an isomorphism: the unit of the composite adjunction is
```
  X --η_X--> G (F X) --G (η'_{F X})--> G (G' (F' (F X)))
```
which is an isomorphism, and so is its second factor. -/
lemma isIso_unit_of_fullyFaithful_comp {E : Type*} [Category E] {F' : D ⥤ E} {G' : E ⥤ D}
    (adj : F ⊣ G) (adj' : F' ⊣ G') [IsIso adj'.unit] [(F ⋙ F').Full] [(F ⋙ F').Faithful] :
    IsIso adj.unit := by
  have := (adj.comp adj').unit_isIso_of_L_fully_faithful
  have (X : C) : IsIso (adj.unit.app X) := by
    have h := Adjunction.comp_unit_app adj adj' X
    have : IsIso ((adj.comp adj').unit.app X) := inferInstance
    rw [h] at this
    exact IsIso.of_isIso_comp_right _ (G.map (adj'.unit.app (F.obj X)))
  exact NatIso.isIso_of_isIso_app _

end Adjunction

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.HomCongr

/-! # Internal Hom from a support projection formula

The formal argument of steps 9--11 of the open/closed internal Hom calculation.
-/

@[expose] public section

set_option autoImplicit false

universe v w u u'

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{w} D]

/-- A natural equivalence of all represented Hom sets gives an isomorphism.
This is the explicit Yoneda argument in proof step 11. -/
noncomputable def isoOfNaturalHomEquiv {A B : C}
    (E : ∀ T : C, (T ⟶ A) ≃ (T ⟶ B))
    (h : ∀ {S T : C} (f : S ⟶ T) (g : T ⟶ A), E S (f ≫ g) = f ≫ E T g) :
    A ≅ B where
  hom := E A (𝟙 A)
  inv := (E B).symm (𝟙 B)
  hom_inv_id := by
    apply (E A).injective
    rw [h]
    simp only [Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    simpa using (h ((E B).symm (𝟙 B)) (𝟙 A)).symm

variable (tC : C ⥤ C ⥤ C) (hC : Cᵒᵖ ⥤ C ⥤ C)
  (tD : D ⥤ D ⥤ D) (hD : Dᵒᵖ ⥤ D ⥤ D)
  (aC : tC ⊣₂ hC) (aD : tD ⊣₂ hD)
  (e : D ⥤ C) (r : C ⥤ D) (s : C ⥤ D) (q : D ⥤ C)
  (ae : e ⊣ s) (ar : r ⊣ q)
  (φ : ∀ (L : D) (T : C), e.obj ((tD.obj L).obj (r.obj T)) ⟶
    (tC.obj (e.obj L)).obj T)

/-- The comparison is the three successive adjunction transposes of evaluation. -/
noncomputable def projectionInternalHomMap (L : D) (N : C) :
    (hC.obj (op (e.obj L))).obj N ⟶ q.obj ((hD.obj (op L)).obj (s.obj N)) :=
  ar.homEquiv _ _ ((aD.adj L).homEquiv _ _ (ae.homEquiv _ _
    (φ L _ ≫ (aC.adj (e.obj L)).counit.app N)))

/-- Projection isomorphisms give an isomorphism of internal Hom objects.
Source: Bhatt--Scholze Lemma 6.7.13, formal adjunction argument, steps 9--11.
(blueprint: lem-sfb-projection-internal-hom-formal)
Proof: tensor-Hom, projection, e adjoint to s, tensor-Hom and r adjoint to q give
natural bijections on Hom from every test object. Apply the bijections to identities;
naturality proves the inverse identities. The hom is the evaluation transpose. -/
theorem projectionInternalHomMap_isIso
    (hφ : ∀ L T, IsIso (φ L T))
    (hn : ∀ (L : D) {T T' : C} (f : T ⟶ T'),
      e.map ((tD.obj L).map (r.map f)) ≫ φ L T' =
        φ L T ≫ (tC.obj (e.obj L)).map f)
    (L : D) (N : C) :
    IsIso (projectionInternalHomMap tC hC tD hD aC aD e r s q ae ar φ L N) := by
  let _ := hφ L
  let E := fun T : C ↦ ((aC.adj (e.obj L)).homEquiv T N).symm.trans
    ((Iso.homCongr (asIso (φ L T)) (Iso.refl N)).symm.trans
      ((ae.homEquiv _ N).trans
        (((aD.adj L).homEquiv _ (s.obj N)).trans (ar.homEquiv T _))))
  have hnE : ∀ {S T : C} (f : S ⟶ T)
      (g : T ⟶ (hC.obj (op (e.obj L))).obj N), E S (f ≫ g) = f ≫ E T g := by
    intro S T f g
    dsimp [E]
    simp only [Iso.homCongr_apply, Iso.symm_inv, asIso_hom, Iso.refl_hom, Category.comp_id]
    rw [Adjunction.homEquiv_naturality_left_symm]
    rw [← Category.assoc, ← hn L f, Category.assoc]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_left]
  let iso := isoOfNaturalHomEquiv E hnE
  have hh : iso.hom =
      projectionInternalHomMap tC hC tD hD aC aD e r s q ae ar φ L N := by
    simp [iso, isoOfNaturalHomEquiv, E, projectionInternalHomMap,
      Adjunction.homEquiv_counit]
  rw [← hh]
  infer_instance

/-- Transposing a comparison after a test map is projection followed by evaluation. -/
theorem projectionInternalHomMap_transpose
    (hn : ∀ (L : D) {T T' : C} (f : T ⟶ T'),
      e.map ((tD.obj L).map (r.map f)) ≫ φ L T' =
        φ L T ≫ (tC.obj (e.obj L)).map f)
    (L : D) (N T : C) (k : T ⟶ (hC.obj (op (e.obj L))).obj N) :
    (ae.homEquiv _ _).symm ((aD.adj L).homEquiv _ _ |>.symm
      ((ar.homEquiv _ _).symm
        (k ≫ projectionInternalHomMap tC hC tD hD aC aD e r s q ae ar φ L N))) =
      φ L T ≫ ((aC.adj (e.obj L)).homEquiv _ _).symm k := by
  simp only [projectionInternalHomMap, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  rw [← Category.assoc, hn L k, Category.assoc, Adjunction.homEquiv_counit]

/-- The evaluation transpose is natural in both internal Hom variables. -/
theorem projectionInternalHomMap_naturality
    (hn : ∀ (L : D) {T T' : C} (f : T ⟶ T'),
      e.map ((tD.obj L).map (r.map f)) ≫ φ L T' =
        φ L T ≫ (tC.obj (e.obj L)).map f)
    (hl : ∀ {L L' : D} (a : L' ⟶ L) (T : C),
      e.map ((tD.map a).app (r.obj T)) ≫ φ L T =
        φ L' T ≫ (tC.map (e.map a)).app T)
    (L L' : D) (N N' : C) (a : L' ⟶ L) (b : N ⟶ N') :
    ((hC.map (e.map a).op).app N ≫ (hC.obj (op (e.obj L'))).map b) ≫
        projectionInternalHomMap tC hC tD hD aC aD e r s q ae ar φ L' N' =
      projectionInternalHomMap tC hC tD hD aC aD e r s q ae ar φ L N ≫
        q.map ((hD.map a.op).app (s.obj N) ≫ (hD.obj (op L')).map (s.map b)) := by
  apply (ar.homEquiv _ _).symm.injective
  apply ((aD.adj L').homEquiv _ _).symm.injective
  apply (ae.homEquiv _ _).symm.injective
  rw [projectionInternalHomMap_transpose tC hC tD hD aC aD e r s q ae ar φ hn]
  simp only [Functor.map_comp, Adjunction.homEquiv_naturality_right_symm,
    ← Category.assoc]
  simp only [← ParametrizedAdjunction.homEquiv_eq,
    ParametrizedAdjunction.homEquiv_symm_naturality_one]
  have hv : aC.homEquiv.symm ((hC.map (e.map a).op).app N) =
      (tC.map (e.map a)).app _ ≫ (aC.adj (e.obj L)).counit.app N := by
    simpa only [Category.id_comp, ParametrizedAdjunction.homEquiv_eq,
      Adjunction.homEquiv_symm_id] using
      aC.homEquiv_symm_naturality_one (e.map a)
        (𝟙 ((hC.obj (op (e.obj L))).obj N))
  rw [hv]
  simp only [ParametrizedAdjunction.homEquiv_eq,
    Adjunction.homEquiv_naturality_left_symm, projectionInternalHomMap,
    Equiv.symm_apply_apply]
  rw [← Category.assoc, ← hl a _]
  simp only [Category.assoc]

end CategoryTheory

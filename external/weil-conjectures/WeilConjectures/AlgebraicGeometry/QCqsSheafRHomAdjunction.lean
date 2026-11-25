/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionMate
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Coherated sheaf derived Hom adjunction

Source: Stacks Project, Duality for Schemes, Lemma 48.3.6 (Tag 0A9Q), with
equation-sheafy-trace (48.3.5.1) defining the sheafy trace
(blueprint: lem-pc-qcqs-sheaf-rhom-adjunction).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Detection of an isomorphism by Hom and a right adjoint.
Source: the Yoneda step of Stacks, Tag 0A9Q. -/
private theorem rightAdjoint_map_isIso_of_bijective
    {C D : Type*} [Category* C] [Category* D]
    {i : D ⥤ C} {r : C ⥤ D} (coh : i ⊣ r)
    {U V : C} (q : U ⟶ V)
    (hb : ∀ M : D, Function.Bijective (fun α : i.obj M ⟶ U ↦ α ≫ q)) :
    IsIso (r.map q) := by
  apply isIso_of_yoneda_map_bijective
  intro M
  let eU := coh.homEquiv M U
  let eV := coh.homEquiv M V
  have h (α : i.obj M ⟶ U) : eV (α ≫ q) = eU α ≫ r.map q :=
    coh.homEquiv_naturality_right α q
  constructor
  · intro α β hab
    apply eU.symm.injective
    apply (hb M).injective
    apply eV.injective
    simpa only [h, Equiv.apply_symm_apply] using hab
  · intro β
    obtain ⟨α, hα⟩ := (hb M).surjective (eV.symm β)
    refine ⟨eU α, ?_⟩
    change eU α ≫ r.map q = β
    change α ≫ q = eV.symm β at hα
    rw [← h, hα, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The five Hom bijections in the proof of Stacks, Tag 0A9Q.
The mate equation identifies their composite with postcomposition by the trace. -/
private theorem trace_bijective_of_projection
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : D ⥤ C) (R : C ⥤ D) (hR : ∀ E, P E → Q (R.obj E))
    (a : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ R) (fun E ↦ hR E.obj E.property) ⊣ a)
    (p : F ⊣ R) (L : P.FullSubcategory) (K M : Q.FullSubcategory)
    (hS : P (F.obj M.obj ⊗ L.obj))
    (bX : tensorRight L.obj ⊣ (Functor.curry.obj H).obj (op L.obj))
    (bY : tensorRight (R.obj L.obj) ⊣ (Functor.curry.obj J).obj (op (R.obj L.obj)))
    (d : F.obj (M.obj ⊗ R.obj L.obj) ⟶ F.obj M.obj ⊗ F.obj (R.obj L.obj))
    (c : R.obj (H.obj (op L.obj, (a.obj K).obj)) ⟶
      J.obj (op (R.obj L.obj), R.obj (a.obj K).obj))
    (hc : ∀ α : M.obj ⟶ R.obj (H.obj (op L.obj, (a.obj K).obj)),
      (bY.homEquiv M.obj (R.obj (a.obj K).obj)).symm (α ≫ c) =
        p.homEquiv _ _ (d ≫ (𝟙 _ ⊗ₘ p.counit.app L.obj) ≫
          (bX.homEquiv _ _).symm ((p.homEquiv _ _).symm α)))
    (hpf : IsIso (p.homEquiv _ (F.obj M.obj ⊗ L.obj)
      (d ≫ (𝟙 _ ⊗ₘ p.counit.app L.obj)))) :
    Function.Bijective (fun α : M.obj ⟶ R.obj (H.obj (op L.obj, (a.obj K).obj)) ↦
      α ≫ c ≫ J.map (𝟙 _ ×ₘ (adj.counit.app K).hom)) := by
  let S : P.FullSubcategory := ⟨F.obj M.obj ⊗ L.obj, hS⟩
  let pf : M.obj ⊗ R.obj L.obj ⟶ R.obj S.obj :=
    p.homEquiv _ _ (d ≫ (𝟙 _ ⊗ₘ p.counit.app L.obj))
  have : IsIso pf := hpf
  let e₁ := (p.homEquiv M.obj (H.obj (op L.obj, (a.obj K).obj))).symm
  let e₂ := (bX.homEquiv (F.obj M.obj) (a.obj K).obj).symm
  let e₃ : (S.obj ⟶ (a.obj K).obj) ≃ (R.obj S.obj ⟶ K.obj) :=
    (P.fullyFaithfulι.homEquiv.symm.trans (adj.homEquiv S K).symm).trans
      Q.fullyFaithfulι.homEquiv
  let e₄ : (R.obj S.obj ⟶ K.obj) ≃ (M.obj ⊗ R.obj L.obj ⟶ K.obj) :=
    Iso.homCongr (asIso pf).symm (Iso.refl K.obj)
  let e₅ := bY.homEquiv M.obj K.obj
  let e := (((e₁.trans e₂).trans e₃).trans e₄).trans e₅
  have he (α : M.obj ⟶ R.obj (H.obj (op L.obj, (a.obj K).obj))) :
      α ≫ c ≫ J.map (𝟙 _ ×ₘ (adj.counit.app K).hom) = e α := by
    apply e₅.symm.injective
    rw [← Category.assoc]
    change (bY.homEquiv M.obj K.obj).symm
      ((α ≫ c) ≫ ((Functor.curry.obj J).obj (op (R.obj L.obj))).map
        (adj.counit.app K).hom) = _
    rw [bY.homEquiv_naturality_right_symm, hc]
    dsimp only [e, Equiv.trans_apply, e₅, Equiv.symm_apply_apply]
    change p.homEquiv _ _ (d ≫ (𝟙 _ ⊗ₘ p.counit.app L.obj) ≫ e₂ (e₁ α)) ≫
      (adj.counit.app K).hom = _
    rw [← Category.assoc, p.homEquiv_naturality_right]
    change _ = e₅.symm (e₅ (e₄ (e₃ (e₂ (e₁ α)))))
    rw [e₅.symm_apply_apply]
    change (pf ≫ R.map (e₂ (e₁ α))) ≫ (adj.counit.app K).hom =
      pf ≫ (R.map (e₂ (e₁ α)) ≫ (adj.counit.app K).hom) ≫ 𝟙 _
    simp only [Category.assoc, Category.comp_id]
  exact (show (fun α ↦ α ≫ c ≫ J.map (𝟙 _ ×ₘ (adj.counit.app K).hom)) = e
    from funext he) ▸ e.bijective

/-- Naturality of the trace is a categorical identity, independent of derived tensor structures. -/
private theorem trace_naturality_of_counit
    {C D : Type*} [Category* C] [Category* D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (R : C ⥤ D) (hR : ∀ E, P E → Q (R.obj E))
    (a : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ R) (fun E ↦ hR E.obj E.property) ⊣ a)
    (c : H ⋙ R ⟶ R.op.prod R ⋙ J)
    (L L' : P.FullSubcategory) (K K' : Q.FullSubcategory)
    (g : L' ⟶ L) (h : K ⟶ K') :
    R.map (H.map (g.hom.op ×ₘ (a.map h).hom)) ≫
        c.app (op L'.obj, (a.obj K').obj) ≫ J.map (𝟙 _ ×ₘ (adj.counit.app K').hom) =
      (c.app (op L.obj, (a.obj K).obj) ≫ J.map (𝟙 _ ×ₘ (adj.counit.app K).hom)) ≫
        J.map ((R.map g.hom).op ×ₘ h.hom) := by
  have hn := c.naturality (g.hom.op ×ₘ (a.map h).hom)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← J.map_comp,
    Category.assoc, ← J.map_comp]
  congr 2
  apply Prod.ext
  · simp
  · exact congrArg (fun z ↦ z.hom) (adj.counit.naturality h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For qcqs schemes and a qcqs morphism `f`, let `adj : Rf_* ⊣ a` be the restricted
adjunction on `D_QCoh` and let `c` be the internal-Hom comparison
`Rf_* RHom_X(L, M) ⟶ RHom_Y(Rf_* L, Rf_* M)`, tied by the mate equation `hc` of
`exists_derivedDirectImage_internalHom_comparison` (lem-pc-sheaf-rhom-projection-formula).
The sheafy trace `c(L, aK) ≫ RHom_Y(Rf_* L, ε_K)` is natural in `L` and `K`, and it becomes
invertible after applying the coherator `DQ`.
Source: Stacks Project, Tag 0A9Q and equation 48.3.5.1
(blueprint: lem-pc-qcqs-sheaf-rhom-adjunction).

Proof:
1. Naturality of c and the restricted adjunction counit give the naturality square.
2. The coherator adjunction and Yoneda reduce invertibility to bijectivity of
   postcomposition on Hom from each quasi-coherent M.
3. Derived pullback preserves quasi-coherence, and
   canonical_derivedTensor_preserve_QCoh puts Lf*M tensor L in the full subcategory.
4. Compose pullback/direct-image, tensor-Hom and restricted adjunction equivalences.
   Precomposition with qcqsDerivedProjectionMate_isIso supplies the fourth Hom
   bijection; the target tensor-Hom adjunction supplies the fifth.
5. The supplied mate equation hc, naturality of the tensor-Hom and pullback
   adjunctions, and the counit formula for the restricted adjunction identify
   this composite equivalence with postcomposition by the trace. -/
theorem qcqsSheafRHomAdjunction (X Y : Scheme.{u₁})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ hpres E.obj E.property) ⊣ a)
    (DQ : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y)
    (coh : (schemeDerivedQCohProperty Y).ι ⊣ DQ)
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (bX : ∀ L : schemeDerivedCategory X, tensorRight L ⊣
      (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)).obj
          (op L))
    (bY : ∀ L : schemeDerivedCategory Y, tensorRight L ⊣
      (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op L))
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (c : derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf ⋙
        schemeDerivedDirectImage f ⟶
      (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
        derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)
    (hc : ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
      (α : A ⟶ (schemeDerivedDirectImage f).obj
        ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).obj
          (op L, M))),
      ((bY ((schemeDerivedDirectImage f).obj L)).homEquiv A
        ((schemeDerivedDirectImage f).obj M)).symm (α ≫ c.app (op L, M)) =
      p.homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
        (t.hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
          (𝟙 ((derivedPullback f).obj A) ⊗ₘ p.counit.app L) ≫
          ((bX L).homEquiv ((derivedPullback f).obj A) M).symm
            ((p.homEquiv A
              ((derivedInternalHom (Opens.grothendieckTopology X)
                X.toRingedSpace.sheaf).obj (op L, M))).symm α))) :
    (∀ (L L' : schemeDerivedQCohCategory X) (K K' : schemeDerivedQCohCategory Y)
        (g : L' ⟶ L) (h : K ⟶ K'),
        (schemeDerivedDirectImage f).map
            ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).map
              (g.hom.op ×ₘ (a.map h).hom)) ≫
          c.app (op L'.obj, (a.obj K').obj) ≫
            (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
              (𝟙 _ ×ₘ (adj.counit.app K').hom) =
        (c.app (op L.obj, (a.obj K).obj) ≫
            (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
              (𝟙 _ ×ₘ (adj.counit.app K).hom)) ≫
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
            (((schemeDerivedDirectImage f).map g.hom).op ×ₘ h.hom)) ∧
      (∀ (L : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y),
        IsIso (DQ.map (c.app (op L.obj, (a.obj K).obj) ≫
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
            (𝟙 _ ×ₘ (adj.counit.app K).hom)))) := by
  constructor
  · intro L L' K K' g h
    exact trace_naturality_of_counit
      (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)
      (schemeDerivedQCohProperty X) (schemeDerivedQCohProperty Y)
      (schemeDerivedDirectImage f) hpres a adj c L L' K K' g h
  · intro L K
    let HX := derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf
    let HY := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let R := schemeDerivedDirectImage f
    let F := derivedPullback f
    let trace := c.app (op L.obj, (a.obj K).obj) ≫
      HY.map (𝟙 _ ×ₘ (adj.counit.app K).hom)
    have hb (M : schemeDerivedQCohCategory Y) :
        Function.Bijective (fun α : M.obj ⟶ R.obj (HX.obj (op L.obj, (a.obj K).obj)) ↦
          α ≫ trace) := by
      have hS := canonical_derivedTensor_preserve_QCoh X (F.obj M.obj) L.obj
        ((derivedPullback_tensor_preserve_QCoh f).1 M.obj M.property) L.property
      have hpf := qcqsDerivedProjectionMate_isIso X Y f p t M L
      simpa only [trace, Category.assoc, Functor.op_obj] using
        trace_bijective_of_projection HX HY
          (schemeDerivedQCohProperty X) (schemeDerivedQCohProperty Y)
          F R hpres a adj p L K M hS (bX L.obj) (bY (R.obj L.obj))
          (t.hom.app (M.obj, R.obj L.obj)) (c.app (op L.obj, (a.obj K).obj))
          (hc L.obj (a.obj K).obj M.obj) hpf
    exact rightAdjoint_map_isIso_of_bijective coh trace hb

end AlgebraicGeometry

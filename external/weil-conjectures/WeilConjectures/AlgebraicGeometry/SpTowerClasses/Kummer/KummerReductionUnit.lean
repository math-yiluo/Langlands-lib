/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemReductionTriangle
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The unshifted Kummer comparison and its adjunction unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors

private theorem forget_faithful (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) : F.F.Faithful := by
  constructor
  intro M N f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, V⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hfg := congrArg (fun z ↦ (((z.app (op n)).hom.app (op V)).hom)) h
  have hh := (F.morphisms f n (op V)).symm.trans
    (hfg.heq.trans (F.morphisms g n (op V)))
  exact congrArg (fun z ↦ z x) (eq_of_heq hh)

private theorem lift_shifted_single
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G.Faithful] (X : DerivedCategory B) (Z : A)
    (e : G.mapDerivedCategory.obj X ≅
      ((DerivedCategory.singleFunctor A 0).obj Z)⟦(1 : ℤ)⟧) :
    ∃ (M : B) (i : G.obj M ≅ Z)
      (a : X ≅ ((DerivedCategory.singleFunctor B 0).obj M)⟦(1 : ℤ)⟧),
      G.mapDerivedCategory.map a.hom ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor B 0).obj M) ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map i.hom)⟦(1 : ℤ)⟧' = e.hom := by
  have : (((DerivedCategory.singleFunctor A 0).obj Z)⟦(1 : ℤ)⟧).IsGE (-1) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by decide)
  have : (((DerivedCategory.singleFunctor A 0).obj Z)⟦(1 : ℤ)⟧).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by decide)
  have hge : (G.mapDerivedCategory.obj X).IsGE (-1) :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm (-1)
  have hle : (G.mapDerivedCategory.obj X).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm (-1)
  obtain ⟨hge', hle'⟩ :=
    G.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj ⟨hge, hle⟩
  let := hge'
  let := hle'
  obtain ⟨M, ⟨a₀⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X (-1)
  let a := a₀ ≪≫ (((DerivedCategory.singleFunctors B).shiftIso
    (1 : ℤ) (-1) 0 (by decide)).app M).symm
  let b : G.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor B 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor A 0).obj (G.obj M))⟦(1 : ℤ)⟧ :=
    (G.mapDerivedCategory.commShiftIso (1 : ℤ)).app
        ((DerivedCategory.singleFunctor B 0).obj M) ≪≫
      (shiftFunctor (DerivedCategory A) (1 : ℤ)).mapIso
        ((G.mapDerivedCategorySingleFunctor 0).app M)
  let S := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor (DerivedCategory A) (1 : ℤ)
  let q : S.obj (G.obj M) ≅ S.obj Z :=
    b.symm ≪≫ G.mapDerivedCategory.mapIso a.symm ≪≫ e
  let i : G.obj M ≅ Z := S.preimageIso q
  refine ⟨M, i, a, ?_⟩
  have hi : S.map i.hom = q.hom := S.map_preimage _
  have h : G.mapDerivedCategory.map a.hom ≫ b.hom ≫ S.map i.hom = e.hom := by
    rw [hi]
    simp only [q, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_assoc]
    rw [← G.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [b, S, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.comp_map, Category.assoc] using h

private theorem boundary_comparison
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    (S : ShortComplex A) (hS : S.ShortExact) (X : DerivedCategory A)
    (η : (DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ X)
    (δ : X ⟶ ((DerivedCategory.singleFunctor A 0).obj S.X₂)⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk
      ((DerivedCategory.singleFunctor A 0).map S.g) η δ ∈
        distTriang (DerivedCategory A)) :
    ∃ e : X ≅ ((DerivedCategory.singleFunctor A 0).obj S.X₁)⟦(1 : ℤ)⟧,
      η ≫ e.hom = hS.singleδ := by
  let U := Triangle.mk ((DerivedCategory.singleFunctor A 0).map S.g) η δ
  let V := hS.singleTriangle.rotate
  have hV := CategoryTheory.Pretriangulated.rot_of_distTriang _
    hS.singleTriangle_distinguished
  obtain ⟨c, hc₁, hc₂⟩ :=
    CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism U V hδ hV
      (𝟙 _) (𝟙 _) (by
        change (DerivedCategory.singleFunctor A 0).map S.g ≫
          𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₃) =
          𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₂) ≫
          (DerivedCategory.singleFunctor A 0).map S.g
        rw [Category.comp_id, Category.id_comp])
  dsimp [U, V, Triangle.rotate, ShortComplex.ShortExact.singleTriangle] at c hc₁ hc₂
  let φ : U ⟶ V :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := c
      comm₁ := by
        change (DerivedCategory.singleFunctor A 0).map S.g ≫
          𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₃) =
          𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₂) ≫
          (DerivedCategory.singleFunctor A 0).map S.g
        rw [Category.comp_id, Category.id_comp]
      comm₂ := hc₁
      comm₃ := hc₂ }
  have hc : IsIso φ.hom₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ φ hδ hV
    (IsIso.id _) (IsIso.id _)
  refine ⟨@asIso (DerivedCategory A) _ U.obj₃ V.obj₃ c hc, ?_⟩
  change η ≫ c = 𝟙 _ ≫ hS.singleδ at hc₁
  change η ≫ c = hS.singleδ
  simpa only [Category.id_comp] using hc₁

private theorem assemble_reduction
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G.Faithful] (L : DerivedCategory A ⥤ DerivedCategory B)
    (adj : L ⊣ G.mapDerivedCategory) {X₁ X₂ X₃ : A}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact)
    (h : ∃ δ, Triangle.mk ((DerivedCategory.singleFunctor A 0).map g)
      (adj.unit.app ((DerivedCategory.singleFunctor A 0).obj X₃)) δ ∈
        distTriang (DerivedCategory A)) :
    ∃ (M : B) (i : G.obj M ≅ X₁)
      (a : L.obj ((DerivedCategory.singleFunctor A 0).obj X₃) ≅
        ((DerivedCategory.singleFunctor B 0).obj M)⟦(1 : ℤ)⟧),
      (adj.homEquiv _ _) a.hom ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor B 0).obj M) ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map i.hom)⟦(1 : ℤ)⟧' = hS.singleδ := by
  obtain ⟨δ, hδ⟩ := h
  obtain ⟨e, he⟩ := boundary_comparison (ShortComplex.mk f g w) hS _ _ δ hδ
  obtain ⟨M, i, a, ha⟩ := lift_shifted_single G _ X₁ e
  refine ⟨M, i, a, ?_⟩
  simpa only [Adjunction.homEquiv_unit, Category.assoc] using
    (congrArg (fun f ↦ adj.unit.app ((DerivedCategory.singleFunctor A 0).obj X₃) ≫ f)
      ha).trans he

/-- Reduction of units is the roots module shifted once, with the unshifted positive
Kummer boundary as its adjunct. No comparison on the integer source is involved.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
and NormalizedKummerReduction proof steps 3--4.
(blueprint: lem-sfb-kummer-reduction-unit).

Proof: apply the coefficient-resolution unit triangle. Compare it by TR3 with the
rotation of the distinguished single triangle of the supplied Kummer short exact
sequence, using identities on its first two objects. The triangulated five lemma
makes the third comparison an isomorphism to the roots object shifted once, and the
second square identifies the actual adjunction unit with the positive Kummer boundary.
The supplied forgetting functor is faithful: its morphism specification identifies
all section maps, which determine a sheaf-of-modules morphism. Exact faithful
forgetting reflects concentration of homology in degree -1. Hence the derived
reduction is isomorphic to a single coefficient module shifted once. Compare its
underlying shifted single object with roots by the preceding triangle isomorphism;
full faithfulness of the shifted single functor recovers the required abelian
isomorphism i. Its preimage equation gives the stated comparison after composing
with the unit, by the adjunction formula for homEquiv. No faithfulness of the derived
forgetting functor or detection of derived morphisms by individual evaluations is
used. The zero roots object, the empty scheme, l=2 and level n=0 require no separate
argument. -/
theorem exists_kummerReductionUnit (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (k : Kummer l T)
    (r : Reduction T (Rrings l T)) :
    ∃ (M : Systems T (Rrings l T)) (i : r.forget.F.obj M ≅ roots l T)
      (a : r.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T)) ≅
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj M)⟦(1 : ℤ)⟧),
      (r.derivedAdjunction.homEquiv _ _) a.hom ≫
        (r.forget.F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj M) ≫
        ((r.forget.F.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor (Ab T) 0).map i.hom)⟦(1 : ℤ)⟧' =
          k.exact.singleδ := by
  have _ := hT
  clear hT
  have : r.forget.F.Faithful := forget_faithful T (Rrings l T) r.forget
  exact assemble_reduction r.forget.F r.derived r.derivedAdjunction
    k.inclusion k.power k.zero k.exact
    (powerSystem_reduction_triangle l T r k.power k.power_eq)

end AlgebraicGeometry.ProEtale.SpTowerClasses

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Total right derived functors from enough K-injective complexes

Source: Stacks Project, Derived Categories, Tag 070K, lemma-enough-K-injectives-implies,
and Tag 070Y, lemma-K-injective-defined (blueprint: lem-weil-pbc-kinjective-total-derived).
-/

@[expose] public section

universe w v u vT uT

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Enough K-injective complexes give a total right derived functor, computed on every
K-injective complex. Source: Stacks Project, Derived Categories, Tag 070K,
lemma-enough-K-injectives-implies; Tag 070Y, lemma-K-injective-defined
(blueprint: lem-weil-pbc-kinjective-total-derived).

Proof plan:
1. Choose a representative of each derived object and a K-injective replacement of its
   underlying complex. The replacement and the quotient-to-derived comparison give an
   isomorphism e_X : X ≅ Qh (R X), where R X is K-injective.
2. Use the Hom bijection into K-injective targets to lift
   e_X.inv ≫ a ≫ e_Y.hom, defining a functor R : D(A) → K(A). Injectivity of that
   bijection proves preservation of identities and composition.
3. Lift e_(Qh K).hom to a natural transformation u : 𝟭 → Qh ⋙ R, and set
   η = whiskerRight u F. The same injectivity proves naturality of u.
4. For K-injective K, lift e_(Qh (π K)).inv and use the two inverse identities of e to
   prove that u_(π K) and hence η_(π K) are invertible.
5. Given α : F → Qh ⋙ G, define β_X = α_(R X) ≫ G(e_X.inv). The formulas for R and
   u prove that β is natural and is the inverse to composition with η. Evaluating an
   equality at R X and cancelling the invertible component at that object proves
   uniqueness. -/
theorem exists_rightDerived_of_enough_isKInjective
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ T)
    [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ (RF : DerivedCategory A ⥤ T) (η : F ⟶ DerivedCategory.Qh ⋙ RF),
      (∀ G : DerivedCategory A ⥤ T,
        Function.Bijective
          (fun β : RF ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Qh β)) ∧
      (∀ (J : CochainComplex A ℤ), J.IsKInjective →
        IsIso (η.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J))) := by
  classical
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Q : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A := DerivedCategory.Qh
  -- Resolve a chosen representative of each derived object. The chosen localization
  -- need not have the same objects as the category of complexes.
  choose J f hJ hf using h
  let j (X : DerivedCategory A) := J (DerivedCategory.Q.objPreimage X)
  have hj (X : DerivedCategory A) : (j X).IsKInjective := hJ _
  have hq (K : CochainComplex A ℤ) : IsIso (DerivedCategory.Q.map (f K)) := by
    have := hf K
    infer_instance
  let e (X : DerivedCategory A) : X ≅ Q.obj (π.obj (j X)) :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
      asIso (DerivedCategory.Q.map (f (DerivedCategory.Q.objPreimage X))) ≪≫
      (DerivedCategory.quotientCompQhIso A).symm.app (j X)
  let lift {K : HomotopyCategory A (ComplexShape.up ℤ)} {X : DerivedCategory A}
      (a : Q.obj K ⟶ Q.obj (π.obj (j X))) : K ⟶ π.obj (j X) :=
    (Equiv.ofBijective Q.map (CochainComplex.IsKInjective.Qh_map_bijective K (j X))).symm a
  have lift_spec {K : HomotopyCategory A (ComplexShape.up ℤ)} {X : DerivedCategory A}
      (a : Q.obj K ⟶ Q.obj (π.obj (j X))) : Q.map (lift a) = a := by
    exact (Equiv.ofBijective Q.map
      (CochainComplex.IsKInjective.Qh_map_bijective K (j X))).apply_symm_apply a
  -- Lift conjugated derived morphisms uniquely into K-injective targets.
  let R : DerivedCategory A ⥤ HomotopyCategory A (ComplexShape.up ℤ) :=
    { obj := fun X ↦ π.obj (j X)
      map := fun {X Y} a ↦ lift ((e X).inv ≫ a ≫ (e Y).hom)
      map_id := by
        intro X
        apply (CochainComplex.IsKInjective.Qh_map_bijective _ (j X)).injective
        change Q.map (lift ((e X).inv ≫ 𝟙 X ≫ (e X).hom)) = Q.map (𝟙 _)
        rw [lift_spec, Q.map_id]
        simp
      map_comp := by
        intro X Y Z a b
        apply (CochainComplex.IsKInjective.Qh_map_bijective _ (j Z)).injective
        change Q.map (lift ((e X).inv ≫ (a ≫ b) ≫ (e Z).hom)) =
          Q.map (lift ((e X).inv ≫ a ≫ (e Y).hom) ≫
            lift ((e Y).inv ≫ b ≫ (e Z).hom))
        rw [Q.map_comp, lift_spec, lift_spec, lift_spec]
        simp }
  have R_map {X Y : DerivedCategory A} (a : X ⟶ Y) :
      Q.map (R.map a) = (e X).inv ≫ a ≫ (e Y).hom := lift_spec _
  -- Lift the replacement isomorphism to obtain the comparison before applying F.
  let u : 𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) ⟶ Q ⋙ R :=
    { app := fun K ↦ lift ((e (Q.obj K)).hom)
      naturality := by
        intro K L a
        apply (CochainComplex.IsKInjective.Qh_map_bijective _ (j (Q.obj L))).injective
        change Q.map (a ≫ lift (e (Q.obj L)).hom) =
          Q.map (lift (e (Q.obj K)).hom ≫ R.map (Q.map a))
        rw [Q.map_comp, Q.map_comp, lift_spec, lift_spec, R_map]
        simp }
  have u_map (K : HomotopyCategory A (ComplexShape.up ℤ)) :
      Q.map (u.app K) = (e (Q.obj K)).hom := lift_spec _
  -- If the source is also K-injective, lift the inverse and check both identities.
  have u_iso (K : CochainComplex A ℤ) [K.IsKInjective] : IsIso (u.app (π.obj K)) := by
    let g : R.obj (Q.obj (π.obj K)) ⟶ π.obj K :=
      (Equiv.ofBijective Q.map
        (CochainComplex.IsKInjective.Qh_map_bijective _ K)).symm
          (e (Q.obj (π.obj K))).inv
    have hg : Q.map g = (e (Q.obj (π.obj K))).inv :=
      (Equiv.ofBijective Q.map
        (CochainComplex.IsKInjective.Qh_map_bijective _ K)).apply_symm_apply _
    refine ⟨g, ?_, ?_⟩
    · apply (CochainComplex.IsKInjective.Qh_map_bijective _ K).injective
      change Q.map (u.app (π.obj K) ≫ g) = Q.map (𝟙 _)
      rw [Q.map_comp, u_map, hg, Q.map_id]
      exact (e (Q.obj (π.obj K))).hom_inv_id
    · apply (CochainComplex.IsKInjective.Qh_map_bijective _ (j (Q.obj (π.obj K)))).injective
      change Q.map (g ≫ u.app (π.obj K)) = Q.map (𝟙 _)
      rw [Q.map_comp, u_map, hg, Q.map_id]
      exact (e (Q.obj (π.obj K))).inv_hom_id
  let η : F ⟶ Q ⋙ (R ⋙ F) := Functor.whiskerRight u F
  refine ⟨R ⋙ F, η, ?_, ?_⟩
  · intro G
    constructor
    · intro β γ heq
      apply NatTrans.ext
      funext X
      -- Compare on a K-injective replacement, then transport along e X.
      have hc := NatTrans.congr_app heq (R.obj X)
      have hi : IsIso (u.app (R.obj X)) := u_iso (j X)
      have hi' : IsIso (η.app (R.obj X)) := F.map_isIso (u.app (R.obj X))
      have he : β.app (Q.obj (R.obj X)) = γ.app (Q.obj (R.obj X)) := by
        exact (cancel_epi (η.app (R.obj X))).mp hc
      apply (cancel_mono (G.map (e X).hom)).mp
      rw [← β.naturality, ← γ.naturality, he]
    · intro α
      -- This is the explicit inverse to composition with the comparison.
      let β : R ⋙ F ⟶ G :=
        { app := fun X ↦ α.app (R.obj X) ≫ G.map (e X).inv
          naturality := by
            intro X Y a
            dsimp
            rw [← Category.assoc, α.naturality, Category.assoc, Functor.comp_map, R_map]
            simp [Functor.map_comp] }
      refine ⟨β, ?_⟩
      apply NatTrans.ext
      funext K
      change F.map (u.app K) ≫ (α.app (R.obj (Q.obj K)) ≫
        G.map (e (Q.obj K)).inv) = α.app K
      have ha : F.map (u.app K) ≫ α.app (R.obj (Q.obj K)) =
          α.app K ≫ G.map (Q.map (u.app K)) := α.naturality (u.app K)
      rw [← Category.assoc, ha, Category.assoc, u_map]
      simp [← G.map_comp]
  · intro K hK
    have := u_iso K
    exact F.map_isIso (u.app (π.obj K))

end CategoryTheory

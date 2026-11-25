/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.UnboundedInjectiveModel

/-!
# The normalized boundary on the unbounded derived category

Source: Stacks Project, Tags 079P and 0152.
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

/-- A short complex of additive functors exact on injectives has a unique natural
boundary on the unbounded derived category normalized by short exact complexes.
Source: Stacks Project, Tags 079P and 0152.
(blueprint: lem-pur-unbounded-derived-boundary).

Proof: Model each derived object by a termwise injective K-injective complex. Conjugate
the canonical boundary of the resulting short exact complex by the computation
isomorphisms. The K-injective Hom bijection lifts every derived morphism to a chain map,
so naturality of short exact complex boundaries proves naturality and independence
of the model. Comparison with the identity model proves the normalization. Naturality
along the model isomorphism and normalization prove uniqueness. -/
theorem exists_unique_unboundedDerivedBoundary
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (S : ShortComplex (C ⥤ D)) [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    (hS : S.ShortExactOnInjectives) :
    ∃! δ : S.X₃.rightDerivedFunctor ⟶
        S.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ),
      ∀ (I : CochainComplex C ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
        δ.app (DerivedCategory.Q.obj I) ≫
            (S.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
          (S.X₃.rightDerivedFunctorObjQIso I).hom ≫
            DerivedCategory.triangleOfSESδ (hS.shortExact_mapCochainComplex I) := by
  classical
  let R (M : DerivedCategory C) : M.InjectiveModel :=
    Classical.choice (DerivedCategory.nonempty_injectiveModel C M)
  let δ : S.X₃.rightDerivedFunctor ⟶
      S.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ) := {
    app M := rightDerivedδAux hS M (R M)
    naturality M N f := rightDerivedδAux_naturality hS (R M) (R N) f }
  have hδ (I : CochainComplex C ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)] :
      δ.app (DerivedCategory.Q.obj I) ≫
          (S.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS.shortExact_mapCochainComplex I) := by
    let RI : (DerivedCategory.Q.obj I).InjectiveModel := { I := I, iso := Iso.refl _ }
    have h := rightDerivedδAux_naturality hS (R (DerivedCategory.Q.obj I)) RI (𝟙 _)
    simp only [Functor.map_id, Category.id_comp, Category.comp_id] at h
    change rightDerivedδAux hS _ (R _) ≫ _ = _
    rw [← h]
    simp [rightDerivedδAux, RI, rightDerivedδQObj, ← Functor.map_comp]
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  apply NatTrans.ext
  funext M
  have hI : δ'.app (DerivedCategory.Q.obj (R M).I) =
      δ.app (DerivedCategory.Q.obj (R M).I) := by
    apply (cancel_mono ((S.X₁.rightDerivedFunctorObjQIso (R M).I).hom⟦(1 : ℤ)⟧')).1
    exact (hδ' (R M).I).trans (hδ (R M).I).symm
  apply (cancel_epi (S.X₃.rightDerivedFunctor.map (R M).iso.hom)).1
  rw [δ'.naturality, hI, δ.naturality]

end CategoryTheory.ShortComplex

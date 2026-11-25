/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact transport of the cyclic conjugation action

Source: Stacks Project, Derived Categories, Tag 0152; the exact-functor part of
steps 5--6 of `lem-sf-cyclic-derived-hom-exact-sequence`.
(blueprint: lem-sf-cyclic-derived-exact-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]
  (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private theorem conjugation_transport
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (P : A ⥤ A) (R : B ⥤ B) (H : A ⥤ B)
    [P.CommShift ℤ] [R.CommShift ℤ] [H.CommShift ℤ]
    (β : H ⋙ R ≅ P ⋙ H) [NatTrans.CommShift β.hom ℤ]
    {XM XN : A} {YM YN : B}
    (θM : P.obj XM ≅ XM) (θN : P.obj XN ≅ XN)
    (ψM : R.obj YM ≅ YM) (ψN : R.obj YN ≅ YN)
    (αM : YM ≅ H.obj XM) (αN : YN ≅ H.obj XN)
    (hM : R.map αM.hom ≫ β.hom.app XM ≫ H.map θM.hom = ψM.hom ≫ αM.hom)
    (hN : R.map αN.hom ≫ β.hom.app XN ≫ H.map θN.hom = ψN.hom ≫ αN.hom)
    (r : ℤ) (u : XM ⟶ XN⟦r⟧) :
    αM.hom ≫ H.map (θM.inv ≫ P.map u ≫ (P.commShiftIso r).hom.app XN ≫
        θN.hom⟦r⟧') ≫ (H.commShiftIso r).hom.app XN ≫ αN.inv⟦r⟧' =
      ψM.inv ≫ R.map (αM.hom ≫ H.map u ≫ (H.commShiftIso r).hom.app XN ≫
        αN.inv⟦r⟧') ≫ (R.commShiftIso r).hom.app YN ≫ ψN.hom⟦r⟧' := by
  have hMi : αM.hom ≫ H.map θM.inv =
      ψM.inv ≫ R.map αM.hom ≫ β.hom.app XM := by
    have h := congrArg (fun f ↦ ψM.inv ≫ f ≫ H.map θM.inv) hM
    simp only [Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
      Iso.inv_hom_id_assoc] at h
    erw [Category.comp_id] at h
    exact h.symm
  have hNi : β.hom.app XN ≫ H.map θN.hom ≫ αN.inv =
      R.map αN.inv ≫ ψN.hom := by
    have h := congrArg (fun f ↦ R.map αN.inv ≫ f ≫ αN.inv) hN
    simpa only [Category.assoc, ← R.map_comp_assoc, Iso.inv_hom_id, R.map_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id] using h
  have hb := NatTrans.shift_app_comm β.hom r XN
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  have ht := congrArg (fun f ↦ f⟦r⟧') hNi
  simp only [Functor.map_comp] at ht
  simp only [H.map_comp, R.map_comp, Category.assoc]
  rw [reassoc_of% hMi, ← reassoc_of% (β.hom.naturality u)]
  rw [H.commShiftIso_hom_naturality_assoc, ← reassoc_of% hb, ht]
  rw [← R.commShiftIso_hom_naturality_assoc]

private theorem structure_fac
    (K : CochainComplex (IsoAlgebra F) ℤ) :
    (cyclicDerivedStructure F).hom.app (DerivedCategory.Q.obj K) ≫
        (forget F).mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((forget F).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app K) := by
  change ((Functor.mapDerivedCategoryCompIso (forget F) F).hom.app _ ≫
      (Functor.mapDerivedCategoryNatIso (strNatIso F)).hom.app _) ≫ _ = _
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors (forget F) F K]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem square_fac
    {A B E H : Type*} [Category A] [Category B] [Category E] [Category H]
    [Abelian A] [Abelian B] [Abelian E] [Abelian H]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory E] [HasDerivedCategory H]
    (a : A ⥤ B) (b : B ⥤ H) (c : A ⥤ E) (d : E ⥤ H)
    [a.Additive] [b.Additive] [c.Additive] [d.Additive]
    [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits c] [PreservesFiniteColimits c]
    [PreservesFiniteLimits d] [PreservesFiniteColimits d]
    (q : a ⋙ b ≅ c ⋙ d) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso q).hom.app (DerivedCategory.Q.obj K) ≫
        d.mapDerivedCategory.map (c.mapDerivedCategoryFactors.hom.app K) ≫
        d.mapDerivedCategoryFactors.hom.app ((c.mapHomologicalComplex (.up ℤ)).obj K) =
      b.mapDerivedCategory.map (a.mapDerivedCategoryFactors.hom.app K) ≫
        b.mapDerivedCategoryFactors.hom.app ((a.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors a b K]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private def actionComparison :
    L.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ L.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

private theorem action_structure (M : DerivedCategory (IsoAlgebra F)) :
    G.mapDerivedCategory.map ((cyclicDerivedExactForgetComparison F G L e).hom.app M) ≫
        (actionComparison F G L e).hom.app ((forget F).mapDerivedCategory.obj M) ≫
        L.mapDerivedCategory.map ((cyclicDerivedStructure F).hom.app M) =
      (cyclicDerivedStructure G).hom.app ((mapOfNatIso e).mapDerivedCategory.obj M) ≫
        (cyclicDerivedExactForgetComparison F G L e).hom.app M := by
  let a := mapOfNatIso e
  let U := forget F
  let V := forget G
  let α := cyclicDerivedExactForgetComparison F G L e
  let β := actionComparison F G L e
  let θ := cyclicDerivedStructure F
  let ψ := cyclicDerivedStructure G
  suffices he :
      Functor.whiskerRight α.hom G.mapDerivedCategory ≫
          Functor.whiskerLeft U.mapDerivedCategory β.hom ≫
          Functor.whiskerRight θ.hom L.mapDerivedCategory =
        Functor.whiskerLeft a.mapDerivedCategory ψ.hom ≫ α.hom by
    exact congr_app he M
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  let UK := (U.mapHomologicalComplex (.up ℤ)).obj K
  let AK := (a.mapHomologicalComplex (.up ℤ)).obj K
  have hα : α.hom.app (DerivedCategory.Q.obj K) ≫
      L.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
      L.mapDerivedCategoryFactors.hom.app UK =
      V.mapDerivedCategory.map (a.mapDerivedCategoryFactors.hom.app K) ≫
        V.mapDerivedCategoryFactors.hom.app AK := by
    have h := square_fac a V U L (mapOfNatIsoCompForgetIso e) K
    have hi : DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (mapOfNatIsoCompForgetIso e).hom (.up ℤ)).app K) =
        𝟙 _ := by
      change DerivedCategory.Q.map (𝟙 _) = 𝟙 _
      exact DerivedCategory.Q.map_id _
    erw [hi, Category.comp_id] at h
    exact h
  have hβ := square_fac L G F L e UK
  have hθ := structure_fac F K
  have hψ := structure_fac G AK
  have hnθ := L.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app K)
  have hnβ := β.hom.naturality (U.mapDerivedCategoryFactors.hom.app K)
  have hnψ := ψ.hom.naturality (a.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hnθ hnβ hnψ
  apply (cancel_mono (L.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
    L.mapDerivedCategoryFactors.hom.app UK)).1
  simp only [Category.assoc]
  -- Move to complexes using the canonical factorization equations.
  rw [← L.mapDerivedCategory.map_comp_assoc, hθ]
  simp only [L.mapDerivedCategory.map_comp, Category.assoc]
  erw [hnθ, ← reassoc_of% hnβ, reassoc_of% hβ]
  rw [← G.mapDerivedCategory.map_comp_assoc,
    ← G.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc, hα, G.mapDerivedCategory.map_comp]
  rw [← reassoc_of% hnψ, hψ]
  have he : (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app UK ≫
      (L.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex (strNatIso G).hom (.up ℤ)).app AK := by
    ext n
    rfl
  erw [← DerivedCategory.Q.map_comp, he]
  rfl

private theorem action_apply (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ)
    (u : CyclicDerivedHom F M N r) :
    cyclicDerivedHomAction F M N r u =
      ((cyclicDerivedStructure F).inv.app M ≫ F.mapDerivedCategory.map u) ≫
        ((F.mapDerivedCategory.commShiftIso r).hom.app
            ((forget F).mapDerivedCategory.obj N) ≫
          ((cyclicDerivedStructure F).hom.app N)⟦r⟧') := rfl

/-- Exact equivariant transport commutes with the conjugation action in every degree.

Proof: let J=D(mapOfNatIso e), H=D(L), U=D(forget F), V=D(forget G),
P=D(F), R=D(G), alpha the prescribed comparison, and
beta=(mapDerivedCategoryCompIso L G).symm followed by D(e) followed by
mapDerivedCategoryCompIso F L. The ordinary equation defining mapOfNatIso gives
R(alpha_M) beta_(UM) H(theta_M) = theta_(JM) alpha_M after localization.
It is verified on complexes using mapDerivedCategoryNatIso_fac and
mapDerivedCategoryCompIso_fac; naturality transports it to every derived object.
The exact-functor composition and natural-isomorphism comparisons commute with shifts,
so beta does too. Expand the two conjugations. The structure equation at M gives
alpha_M H(theta_M inverse) = theta_(JM) inverse R(alpha_M) beta_(UM).
Naturality of beta moves H(P(u)) across beta. Its shift equation identifies the
canonical shift factors. The structure equation at N gives
beta_(UN) H(theta_N) alpha_N inverse = R(alpha_N inverse) theta_(JN).
Shift this last equality by r. Associativity and the inverse-isomorphism equations
now identify all four factors of the two expressions. No boundedness or resolution
hypothesis enters this calculation.

Source: the action calculation in step 7 of the parent node; the termwise structure
equation of def-weil-endofunctor-fixed-pair-category, localized by
situation-conventions. This algebraic expansion is agent-written;
Stacks derived.tex, Tag 0152 supplies the surrounding canonical-boundary construction.
(blueprint: lem-sf-cyclic-derived-exact-action). -/
theorem cyclicDerivedHomTransport_exact_action
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ)
    (u : CyclicDerivedHom F M N r) :
    cyclicDerivedHomTransport F G (mapOfNatIso e).mapDerivedCategory
      L.mapDerivedCategory (fun r ↦ L.mapDerivedCategory.commShiftIso r)
      (cyclicDerivedExactForgetComparison F G L e) M N r
      (cyclicDerivedHomAction F M N r u) =
      cyclicDerivedHomAction G ((mapOfNatIso e).mapDerivedCategory.obj M)
        ((mapOfNatIso e).mapDerivedCategory.obj N) r
        (cyclicDerivedHomTransport F G (mapOfNatIso e).mapDerivedCategory
          L.mapDerivedCategory (fun r ↦ L.mapDerivedCategory.commShiftIso r)
          (cyclicDerivedExactForgetComparison F G L e) M N r u) := by
  have : NatTrans.CommShift (actionComparison F G L e).hom ℤ := by
    dsimp only [actionComparison, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  simp only [cyclicDerivedHomTransport, action_apply, Category.assoc]
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using
    conjugation_transport F.mapDerivedCategory G.mapDerivedCategory L.mapDerivedCategory
    (actionComparison F G L e)
    ((cyclicDerivedStructure F).app M) ((cyclicDerivedStructure F).app N)
    ((cyclicDerivedStructure G).app ((mapOfNatIso e).mapDerivedCategory.obj M))
    ((cyclicDerivedStructure G).app ((mapOfNatIso e).mapDerivedCategory.obj N))
    ((cyclicDerivedExactForgetComparison F G L e).app M)
    ((cyclicDerivedExactForgetComparison F G L e).app N)
    (action_structure F G L e M) (action_structure F G L e N) r u

end CategoryTheory.Endofunctor.IsoAlgebra

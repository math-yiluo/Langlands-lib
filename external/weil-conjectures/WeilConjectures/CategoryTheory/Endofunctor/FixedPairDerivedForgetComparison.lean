/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.KInjectiveExactSquare.KInjectiveExactSquareComparison
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Derived forgetting of fixed pairs

Source: `WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean`, Free and
isGrothendieckAbelian; `DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean`,
Free.preservesHomology_functor and rightDerivedFunctorMapOfNatIsoCompForgetIso;
`DerivedCategory/RightDerivedFunctor/IsoAlgebraComp.lean`, derived conservativity
(blueprint: lem-sf-fixed-pair-derived-forget-comparison).

The fixed-pair category is the existing full subcategory `Endofunctor.IsoAlgebra`.
Right derivation uses the recorded arbitrary-quasi-isomorphism interface. The comparison
is characterized by its derived units; evaluating its equation on the homotopy class
of a degree-zero complex gives the requested comparison of maps from single objects.
-/

@[expose] public section

set_option autoImplicit false

universe uC uD vC vD wC wD wF wH

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- Structural clauses for forgetting fixed pairs. Source: Endofunctor/IsoAlgebra.lean,
Free.adjunction and isGrothendieckAbelian; RightDerivedFunctor/IsoAlgebra.lean,
Free.preservesHomology_functor and preservesKInjectiveComplexes_forget; IsoAlgebraComp.lean,
isIso_of_isIso_forget_mapDerivedCategory_map
(blueprint: lem-sf-fixed-pair-derived-forget-comparison).

Proof plan (steps 1--8 of the node): create limits and colimits on underlying objects,
using preservation by the autoequivalence. Addition of commuting maps gives the
preadditive structure; created kernels and cokernels give abelianness and exactness.
An invertible commuting map has a commuting inverse. Construct the free pair as the
coproduct of integer powers, using the quasi-inverse in negative degrees and shifting
summands. Maps out of it are determined by their degree-zero summand, with positive
and negative recursion giving the adjunction. Its value on a generator is a generator;
filtered colimits are exact after forgetting, giving the Grothendieck property
(lem-sfb-grothendieck-filtered-finite-limits, lem-galois-equivalence-preserves-limits).
Direct sums are filtered colimits of finite sums, so the free functor is exact. Its
right adjoint preserves injectives and K-injectives (lem-exc-rg-right-adjoint-preserves-
injectives, lem-weil-pbc-right-adjoint-preserves-kinjective). Finally, forgetting
commutes with cohomology and detects its isomorphisms, hence detects derived
isomorphisms (situation-conventions,
lem-weil-pbc-unbounded-derived-iso-cohomology). -/
theorem fixedPair_forget_properties
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wF} (IsoAlgebra F)] :
    IsGrothendieckAbelian.{vC} (IsoAlgebra F) ∧
      PreservesFiniteLimits (forget F) ∧ PreservesFiniteColimits (forget F) ∧
      (forget F).ReflectsIsomorphisms ∧
      Nonempty (Free.functor F ⊣ forget F) ∧
      PreservesFiniteLimits (Free.functor F) ∧ PreservesFiniteColimits (Free.functor F) ∧
      (∀ M : C, ((Free.functor F).obj M).carrier = ∐ (Free.obj F M)) ∧
      (∀ (M : C) (n : ℤ),
        F.map (Sigma.ι (Free.obj F M) n) ≫ ((Free.functor F).obj M).str.hom =
          (Free.objSucc F M n).hom ≫ Sigma.ι (Free.obj F M) (n + 1)) ∧
      (forget F).PreservesInjectiveObjects ∧ (forget F).PreservesKInjectiveComplexes ∧
      (forget F).mapDerivedCategory.ReflectsIsomorphisms := by
  have hfree : PreservesFiniteLimits (Free.functor F) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have hinj : (forget F).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Free.adjunction F)
  have hreflect : (forget F).mapDerivedCategory.ReflectsIsomorphisms :=
    ⟨fun f _ ↦ by
      rw [DerivedCategory.isIso_iff]
      intro n
      have : IsIso ((forget F).map ((DerivedCategory.homologyFunctor _ n).map f)) :=
        (NatIso.isIso_map_iff ((forget F).mapDerivedCategoryHomologyFunctorIso n) f).2
          (by rw [Functor.comp_map]; infer_instance)
      exact isIso_of_reflects_iso _ (forget F)⟩
  exact ⟨isGrothendieckAbelian F, inferInstance, inferInstance, inferInstance,
    ⟨Free.adjunction F⟩, hfree, inferInstance, fun _ ↦ rfl,
    fun M n ↦ Free.map_ι_comp_str F M n, hinj, inferInstance, hreflect⟩

-- Naturality propagates an equality of units along arbitrary K-injective resolutions.
private theorem homotopy_unit_ext
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {T : Type uD} [Category.{vD} T]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {S : HomotopyCategory C (.up ℤ) ⥤ T} {G : DerivedCategory C ⥤ T}
    (a b : S ⟶ DerivedCategory.Qh ⋙ G)
    (he : ∀ (I : CochainComplex C ℤ), I.IsKInjective →
      a.app ((HomotopyCategory.quotient C (.up ℤ)).obj I) =
        b.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) : a = b := by
  ext K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, s, hI, hs⟩ := h K
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (.up ℤ)).map s)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) s).2 inferInstance
  apply (cancel_mono (G.map (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (.up ℤ)).map s)))).1
  have ha := a.naturality ((HomotopyCategory.quotient C (.up ℤ)).map s)
  have hb := b.naturality ((HomotopyCategory.quotient C (.up ℤ)).map s)
  dsimp only [Functor.comp_map] at ha hb
  rw [← ha, ← hb, he I hI]

/-- Canonical comparison, including its unit normalization. Source:
RightDerivedFunctor/IsoAlgebra.lean, rightDerivedFunctorMapOfNatIsoCompForgetIso,
normalized on the common K-injective resolution, as in the node's final paragraph
(blueprint: lem-sf-fixed-pair-derived-forget-comparison).

Proof plan (steps 9--12 of the node): `mapOfNatIso e` sends a pair to the stated pair
and a morphism to L of that morphism; naturality of e gives the commuting equation.
The forgetful functor creates finite limits, so this lift is left exact. For a
K-injective replacement K → I of a fixed-pair complex, forgetting gives a K-injective
replacement of its underlying complex (lem-weil-pbc-kinjective-functorial-existence
and the structural clauses above). Both derived functors are computed by the same
complex L(U_F I) (lem-weil-pbc-kinjective-total-derived), so the identity of that
complex gives the comparison. Derived morphisms into I are chain maps modulo homotopy
(lem-weil-pbc-kinjective-hom-derived); applying L U_F to those maps proves naturality
and independence of resolution. Both units are L U_F of the replacement map. Thus
the displayed equation holds on every homotopy object, in particular on M[0]; the
unit-compatible universal property of def-sfb-right-derived-functor gives uniqueness.
The two resolution witnesses below are universally quantified choices, not extra
existence hypotheses; Grothendieck categories have such witnesses by the cited
functorial-existence node. -/
theorem exists_fixedPairDerivedForgetComparison
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    (H : D ⥤ D) [H.Additive] [H.IsEquivalence]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] (e : L ⋙ H ≅ F ⋙ L)
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasDerivedCategory.{wF} (IsoAlgebra F)] [HasDerivedCategory.{wH} (IsoAlgebra H)] :
    ∀ (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
        ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
      (hC : ∀ K : CochainComplex C ℤ,
        ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s),
    ∃! α : (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF ⋙
        (forget H).mapDerivedCategory ≅
          (forget F).mapDerivedCategory ⋙ L.rightDerivedFunctorOfQuasiIsoResolutions hC,
      ∀ K : HomotopyCategory (IsoAlgebra F) (ComplexShape.up ℤ),
        (forget H).mapDerivedCategory.map
            (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF).app K) ≫
          α.hom.app (DerivedCategory.Qh.obj K) ≫
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
            ((forget F).mapDerivedCategoryFactorsh.hom.app K) =
        (forget H).mapDerivedCategoryFactorsh.hom.app
            (((mapOfNatIso e).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (mapOfNatIsoCompForgetIso e)
              (ComplexShape.up ℤ)).hom.app K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ L))
              (ComplexShape.up ℤ)).inv.app K) ≫
          (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app
            (((forget F).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  intro hF hC
  let P := mapOfNatIso e
  let r := forget F
  let s := forget H
  let RP := P.rightDerivedFunctorOfQuasiIsoResolutions hF
  let RL := L.rightDerivedFunctorOfQuasiIsoResolutions hC
  let ηP := P.rightDerivedFunctorOfQuasiIsoResolutionsUnit hF
  let ηL := L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC
  have : r.PreservesKInjectiveComplexes := inferInstance
  let c := KInjectiveExactSquare.sourceIso P L r s (rfl : P ⋙ s = r ⋙ L)
  let A := RP ⋙ s.mapDerivedCategory
  let B := r.mapDerivedCategory ⋙ RL
  let a : r.mapHomotopyCategory (.up ℤ) ⋙
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ A :=
    Functor.whiskerRight c.hom DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (P.mapHomotopyCategory (.up ℤ)) s.mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ηP s.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  let b : r.mapHomotopyCategory (.up ℤ) ⋙
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ B :=
    Functor.whiskerLeft (r.mapHomotopyCategory (.up ℤ)) ηL ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight r.mapDerivedCategoryFactorsh.inv RL ≫
      (Functor.associator _ _ _).hom
  obtain ⟨ha, hb, β, hβ, huniq, _⟩ :=
    KInjectiveExactSquare.existsUnique_normalized P L r s rfl RP RL ηP ηL hF hC
      (fun I hI ↦ by have := hI; infer_instance)
      (P.rightDerivedFunctorOfQuasiIsoResolutions_universal hF)
      (L.rightDerivedFunctorOfQuasiIsoResolutions_universal hC)
  have hab : a ≫ Functor.whiskerLeft DerivedCategory.Qh β.hom = b := by
    apply homotopy_unit_ext hF
    intro I hI
    simpa [a, b, c, KInjectiveExactSquare.leftUnit,
      KInjectiveExactSquare.rightUnit] using hβ I hI
  have hnormalized (γ : A ≅ B) :
      (a ≫ Functor.whiskerLeft DerivedCategory.Qh γ.hom = b) ↔
      ∀ K : HomotopyCategory (IsoAlgebra F) (.up ℤ),
        s.mapDerivedCategory.map (ηP.app K) ≫ γ.hom.app (DerivedCategory.Qh.obj K) ≫
            RL.map (r.mapDerivedCategoryFactorsh.hom.app K) =
          s.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (mapOfNatIsoCompForgetIso e)
                (.up ℤ)).hom.app K) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ L))
                (.up ℤ)).inv.app K) ≫
            ηL.app ((r.mapHomotopyCategory (.up ℤ)).obj K) := by
    have hc (K : HomotopyCategory (IsoAlgebra F) (.up ℤ)) :
        DerivedCategory.Qh.map (c.inv.app K) =
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (mapOfNatIsoCompForgetIso e)
                (.up ℤ)).hom.app K) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ L))
                (.up ℤ)).inv.app K) := by
      rw [← Functor.map_comp]
      rfl
    simp_rw [← reassoc_of% hc]
    constructor
    · intro he K
      have ht := congrArg (fun t ↦
        s.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map (c.inv.app K) ≫ t ≫
            RL.map (r.mapDerivedCategoryFactorsh.hom.app K)) (congr_app he K)
      simp only [Functor.comp_obj, Category.assoc, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Category.id_comp, cancelIso,
        Iso.hom_inv_id_app_assoc, Category.comp_id, ← Functor.map_comp,
        Iso.inv_hom_id_app, Functor.map_id, a, b] at ht
      dsimp only [A, B, Functor.comp_obj] at ht
      rw [Category.comp_id] at ht
      simpa only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.assoc] using ht
    · intro he
      ext K
      have ht := congrArg (fun t ↦ DerivedCategory.Qh.map (c.hom.app K) ≫
        s.mapDerivedCategoryFactorsh.inv.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
          t ≫ RL.map (r.mapDerivedCategoryFactorsh.inv.app K)) (he K)
      simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, Functor.map_id, Iso.inv_hom_id_app_assoc, cancelIso] at ht
      dsimp only [A, B, Functor.comp_obj] at ht
      rw [Category.comp_id] at ht
      simpa [a, b] using ht
  refine ⟨β, (hnormalized β).1 hab, ?_⟩
  intro γ hγ
  apply huniq γ
  intro I hI
  have he := congr_app ((hnormalized γ).2 hγ)
    ((HomotopyCategory.quotient (IsoAlgebra F) (.up ℤ)).obj I)
  simpa [a, b, c, KInjectiveExactSquare.leftUnit,
    KInjectiveExactSquare.rightUnit] using he

end CategoryTheory.Endofunctor.IsoAlgebra

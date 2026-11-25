/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Bijectivity of the normalized comparison on an injective complex

Source: Stacks Tags 06XR (1) and 070I
(blueprint: lem-sc-p1-rhom-injective-cocycle-bijective).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- The cocycle normalization forces a comparison on an injective complex to be bijective.
Source: Stacks Tags 06XR (1) and 070I
(blueprint: lem-sc-p1-rhom-injective-cocycle-bijective).

Proof: The inverse cohomology-to-Q isomorphism followed by the derived unit induces
an isomorphism from Hⁿ(Hom(M,I)) to Hⁿ(RHom(M,QI)), since I is degreewise injective.
Every cohomology class is represented by a cocycle M → Iⁿ. Its class vanishes exactly
when that cocycle is a boundary. HomComplexSingle identifies these boundaries with
null-homotopic maps M[0] → I[n], and identifies all such maps with these cocycles.
A bounded below injective complex is K-injective, so Qh_map_bijective identifies
homotopy classes with all derived-category maps into I[n]. The quotient comparison
isomorphism does not change bijectivity. Consequently the prescribed values on
cocycles identify β with this bijection, proving both injectivity and surjectivity.
This also covers negative degrees and zero complexes: the same quotient description
has no degree restriction. -/
theorem rhom_injective_cocycle_map_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}] (M : C)
    (I : CochainComplex.Plus C)
    (_hi : ∀ k : ℤ, Injective (I.obj.X k)) (n : ℤ) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    ∀ β : (H n).obj (RV.obj ((DerivedCategory.Plus.Q (C := C)).obj I)) →+
        (S ⟶ ((DerivedCategory.Plus.Q (C := C)).obj I).obj⟦n⟧),
      (∀ (f : M ⟶ I.obj.X n) (hf : f ≫ I.obj.d n (n + 1) = 0),
        let J := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
        let a := J.homologyπ n ((J.sc n).abCyclesIso.inv
          ⟨f, by
            change f ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0
            rw [CochainComplex.next]
            exact hf⟩)
        let b := (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj I) n).inv a
        let η := V.rightDerivedFunctorPlusUnit.app I
        β ((H n).map η b) =
          ShiftedHom.map (Cocycle.equivHomShift.symm
              (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
            ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧') → Function.Bijective β := by
  classical
  dsimp only
  intro β hβ
  let V := preadditiveCoyoneda.obj (op M)
  let J := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
  let K := (CochainComplex.singleFunctor C 0).obj M
  let := _hi
  obtain ⟨m, hm⟩ := I.2
  let := hm
  have : I.obj.IsKInjective := CochainComplex.isKInjective_of_injective I.obj m
  have : Localization.HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K I.obj := fun a b ↦
    Localization.hasSmallLocalizedHom_of_isLocalization _ DerivedCategory.Q
  let E₀ : CohomologyClass K I.obj n ≃
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj I.obj)⟦n⟧) :=
    (CohomologyClass.equivOfIsKInjective.{w}).trans
      (Localization.SmallShiftedHom.equiv.{w} _ DerivedCategory.Q)
  let E := E₀.trans (Iso.homCongr (Iso.refl _)
    ((shiftFunctor (DerivedCategory C) n).mapIso
      ((DerivedCategory.Plus.QCompιIso C).symm.app I)))
  have hE (f : M ⟶ I.obj.X n) (hf : f ≫ I.obj.d n (n + 1) = 0) :
      E (CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) =
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
            ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧' := by
    simp [E, E₀, CohomologyClass.equivOfIsKInjective,
      CohomologyClass.equiv_toSmallShiftedHom_mk]
    rfl
  let T := (J.sc n).abCyclesIso.inv ≫ J.homologyπ n ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso (V.mapCochainComplexPlus.obj I) n).inv ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).map
      (V.rightDerivedFunctorPlusUnit.app I)
  have : IsIso (V.rightDerivedFunctorPlusUnit.app I) := by
    obtain ⟨L, m, hm⟩ := I
    let L' : CochainComplex (InjectiveObject C) ℤ :=
      HomologicalComplex.liftObjectProperty _ L _hi
    have hL' : L'.IsStrictlyGE m := by
      rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι _)]
    exact inferInstanceAs (IsIso (V.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj ⟨L', m, hL'⟩)))
  have hT : Function.Surjective T :=
    (AddCommGrpCat.epi_iff_surjective T).1 inferInstance
  have hcycle (x : AddMonoidHom.ker (J.sc n).g.hom) :
      x.val ≫ I.obj.d n (n + 1) = 0 := by
    have hx := x.property
    change x.val ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0 at hx
    rw [CochainComplex.next] at hx
    exact hx
  have hval (x : AddMonoidHom.ker (J.sc n).g.hom) :
      β (T x) = E (CohomologyClass.mk
        (Cocycle.fromSingleMk x.val (zero_add n) (n + 1) rfl
          (hcycle x))) := by
    rw [hE]
    exact hβ x.val (hcycle x)
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := hT a
    obtain ⟨y, rfl⟩ := hT b
    have hc := E.injective ((hval x).symm.trans (hab.trans (hval y)))
    have hz : CohomologyClass.mk
        (Cocycle.fromSingleMk (x.val - y.val) (zero_add n) (n + 1) rfl
          (by rw [Preadditive.sub_comp, hcycle x, hcycle y, sub_self])) = 0 := by
      rw [Cocycle.fromSingleMk_sub x.val y.val (zero_add n) (n + 1) rfl
        (hcycle x) (hcycle y), CohomologyClass.mk_sub, hc, sub_self]
    rw [CohomologyClass.mk_eq_zero_iff,
      Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _
        ((ComplexShape.up ℤ).prev n) (by rw [CochainComplex.prev]; simp)] at hz
    obtain ⟨g, hg⟩ := hz
    have hr : x - y ∈ AddMonoidHom.range (J.sc n).abToCycles := by
      refine ⟨g, ?_⟩
      ext
      change g ≫ I.obj.d ((ComplexShape.up ℤ).prev n) n = x.val - y.val
      exact hg
    have hq : (J.sc n).abLeftHomologyData.π (x - y) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hr
    have hp := ConcreteCategory.congr_hom
      (J.sc n).abLeftHomologyData.π_comp_homologyIso_inv (x - y)
    have hpz : J.homologyπ n ((J.sc n).abCyclesIso.inv (x - y)) = 0 := by
      change (J.sc n).homologyπ
        ((J.sc n).abLeftHomologyData.cyclesIso.inv (x - y)) = 0
      simpa only [AddCommGrpCat.comp_apply, hq, map_zero] using hp.symm
    have ht : T (x - y) = 0 := by
      change ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).map
        (V.rightDerivedFunctorPlusUnit.app I))
          ((DerivedCategory.Plus.homologyFunctorObjQIso
            (V.mapCochainComplexPlus.obj I) n).inv
              (J.homologyπ n ((J.sc n).abCyclesIso.inv (x - y)))) = 0
      rw [hpz, map_zero, map_zero]
    rw [_root_.map_sub T.hom, sub_eq_zero] at ht
    exact ht
  · intro b
    obtain ⟨α, hα⟩ := E.surjective b
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective α
    obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α n (zero_add n) (n + 1) rfl
    refine ⟨T ⟨f, ?_⟩, ?_⟩
    · change f ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0
      rw [CochainComplex.next]
      exact hf
    · exact (hval _).trans hα

end CategoryTheory.Functor

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.R.RHomInjectiveCocycleFamily

/-!
# Construction on bounded-below complexes of injectives

The cocycle construction and its compatibility with maps of injective complexes
are isolated here.  The proof follows Stacks Tags 06XR (1) and 070I.
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private lemma quotientComparison_hom (K : CochainComplex.Plus C) :
    (DerivedCategory.Plus.QCompιIso C).inv.app K = 𝟙 _ := rfl

private abbrev cycleComplex (M : C) (I : CochainComplex.Plus C) :=
  ((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj

omit [HasDerivedCategory C] in
private lemma cycleCondition (M : C) (I : CochainComplex.Plus C) (n : ℤ)
    (x : AddMonoidHom.ker ((cycleComplex M I).sc n).g.hom) :
    x.val ≫ I.obj.d n (n + 1) = 0 := by
  have hx := x.property
  change x.val ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0 at hx
  rw [CochainComplex.next] at hx
  exact hx

private noncomputable def cycleToDerived (M : C) (I : CochainComplex.Plus C) (n : ℤ) :
    AddMonoidHom.ker ((cycleComplex M I).sc n).g.hom →+
      ((DerivedCategory.singleFunctor C 0).obj M ⟶
        ((DerivedCategory.Plus.Q (C := C)).obj I).obj⟦n⟧) :=
  AddMonoidHom.mk' (fun x ↦
    ShiftedHom.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk x.val (zero_add n) (n + 1) rfl
        (cycleCondition M I n x))) DerivedCategory.Q ≫
      ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧') (by
    intro x y
    change ShiftedHom.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk (x.val + y.val) (zero_add n) (n + 1) rfl _)) _ ≫ _ = _
    rw [Cocycle.fromSingleMk_add x.val y.val (zero_add n) (n + 1) rfl
      (cycleCondition M I n x) (cycleCondition M I n y)]
    simp only [AddEquiv.map_add, ShiftedHom.map_add, Preadditive.add_comp])

private lemma cycleToDerived_apply (M : C) (I : CochainComplex.Plus C) (n : ℤ)
    (x : AddMonoidHom.ker ((cycleComplex M I).sc n).g.hom) :
    cycleToDerived M I n x =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk x.val (zero_add n) (n + 1) rfl
          (cycleCondition M I n x))) DerivedCategory.Q ≫
        ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧' := rfl

private lemma cycleToDerived_boundary (M : C) (I : CochainComplex.Plus C) (n : ℤ) :
    AddMonoidHom.range ((cycleComplex M I).sc n).abToCycles ≤
      (cycleToDerived M I n).ker := by
  rintro x ⟨g, rfl⟩
  let z := Cocycle.fromSingleMk
    (((cycleComplex M I).sc n).abToCycles g).val (zero_add n) (n + 1) rfl
      (cycleCondition M I n (((cycleComplex M I).sc n).abToCycles g))
  have hz : CohomologyClass.mk z = 0 := by
    rw [CohomologyClass.mk_eq_zero_iff]
    apply (Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _
      ((ComplexShape.up ℤ).prev n) (by rw [CochainComplex.prev]; simp)).2
    exact ⟨g, rfl⟩
  have hh : (HomotopyCategory.quotient C (.up ℤ)).map
      (Cocycle.equivHomShift.symm z) = 0 := by
    rw [← CohomologyClass.toHom_mk, hz, map_zero]
  have hQ := DerivedCategory.Q_map_eq_of_homotopy C
    ((HomotopyCategory.quotient_map_eq_zero_iff _).1 hh).some
  change ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q ≫ _ = 0
  simp only [ShiftedHom.map, hQ, Functor.map_zero, Limits.zero_comp]

private noncomputable def homologyToDerived (M : C) (I : CochainComplex.Plus C) (n : ℤ) :
    (cycleComplex M I).homology n →+
      ((DerivedCategory.singleFunctor C 0).obj M ⟶
        ((DerivedCategory.Plus.Q (C := C)).obj I).obj⟦n⟧) :=
  (QuotientAddGroup.lift _ (cycleToDerived M I n) (cycleToDerived_boundary M I n)).comp
    ((cycleComplex M I).sc n).abHomologyIso.hom.hom

private lemma homologyToDerived_cycle (M : C) (I : CochainComplex.Plus C) (n : ℤ)
    (x : AddMonoidHom.ker ((cycleComplex M I).sc n).g.hom) :
    homologyToDerived M I n ((cycleComplex M I).homologyπ n
      (((cycleComplex M I).sc n).abCyclesIso.inv x)) = cycleToDerived M I n x := by
  have h := ConcreteCategory.congr_hom
    ((cycleComplex M I).sc n).abLeftHomologyData.π_comp_homologyIso_inv x
  change ((cycleComplex M I).sc n).abHomologyIso.inv (QuotientAddGroup.mk x) =
    (cycleComplex M I).homologyπ n
      (((cycleComplex M I).sc n).abCyclesIso.inv x) at h
  change (QuotientAddGroup.lift _ (cycleToDerived M I n)
    (cycleToDerived_boundary M I n))
    (((cycleComplex M I).sc n).abHomologyIso.hom _) = _
  rw [← h]
  let e := ((cycleComplex M I).sc n).abHomologyIso.addCommGroupIsoToAddEquiv
  change (QuotientAddGroup.lift _ (cycleToDerived M I n)
    (cycleToDerived_boundary M I n)) (e (e.symm (QuotientAddGroup.mk x))) = _
  rw [e.apply_symm_apply]
  rfl

private lemma homologyToDerived_natural (M : C) (I J : CochainComplex.Plus C)
    (φ : I.obj ⟶ J.obj) (n : ℤ) (a : (cycleComplex M I).homology n) :
    homologyToDerived M J n
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).map φ) n a) =
      homologyToDerived M I n a ≫
        ((DerivedCategory.Plus.ι (C := C)).map
          ((DerivedCategory.Plus.Q (C := C)).map (ObjectProperty.homMk φ)))⟦n⟧' := by
  let V := preadditiveCoyoneda.obj (op M)
  let φ' := (V.mapHomologicalComplex (.up ℤ)).map φ
  have hsurj : Function.Surjective
      (((cycleComplex M I).sc n).abCyclesIso.inv ≫ (cycleComplex M I).homologyπ n) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, rfl⟩ := hsurj a
  let y : AddMonoidHom.ker ((cycleComplex M J).sc n).g.hom :=
    ⟨x.val ≫ φ.f n, by
      change (x.val ≫ φ.f n) ≫ J.obj.d n ((ComplexShape.up ℤ).next n) = 0
      erw [Category.assoc, φ.comm n ((ComplexShape.up ℤ).next n), ← Category.assoc]
      have hx := x.property
      change x.val ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0 at hx
      rw [hx, Limits.zero_comp]⟩
  have hy : HomologicalComplex.cyclesMap φ' n
      (((cycleComplex M I).sc n).abCyclesIso.inv x) =
        ((cycleComplex M J).sc n).abCyclesIso.inv y := by
    apply (AddCommGrpCat.mono_iff_injective ((cycleComplex M J).iCycles n)).1 inferInstance
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ' n)
      (((cycleComplex M I).sc n).abCyclesIso.inv x)
    simp only [AddCommGrpCat.comp_apply] at h
    change (cycleComplex M J).iCycles n
        (HomologicalComplex.cyclesMap φ' n
          (((cycleComplex M I).sc n).abCyclesIso.inv x)) =
      (cycleComplex M J).iCycles n
        (((cycleComplex M J).sc n).abCyclesIso.inv y)
    erw [ShortComplex.abCyclesIso_inv_apply_iCycles]
    change (cycleComplex M J).iCycles n
        (HomologicalComplex.cyclesMap φ' n
          (((cycleComplex M I).sc n).abCyclesIso.inv x)) = x.val ≫ φ.f n
    rw [h]
    erw [ShortComplex.abCyclesIso_inv_apply_iCycles]
    rfl
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality φ' n)
      (((cycleComplex M I).sc n).abCyclesIso.inv x)
  simp only [AddCommGrpCat.comp_apply, hy] at hmap
  change homologyToDerived M J n
      (HomologicalComplex.homologyMap φ' n
        ((cycleComplex M I).homologyπ n
          (((cycleComplex M I).sc n).abCyclesIso.inv x))) = _
  erw [AddCommGrpCat.comp_apply, hmap, homologyToDerived_cycle, homologyToDerived_cycle]
  have hq : (DerivedCategory.Plus.ι (C := C)).map
      ((DerivedCategory.Plus.Q (C := C)).map (ObjectProperty.homMk φ)) =
        DerivedCategory.Q.map φ := by
    rfl
  rw [cycleToDerived_apply, cycleToDerived_apply]
  erw [quotientComparison_hom, Functor.map_id, Category.comp_id,
    quotientComparison_hom, Functor.map_id, Category.comp_id]
  rw [hq]
  change ShiftedHom.map (Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk (x.val ≫ φ.f n) (zero_add n) (n + 1) rfl _)) _ = _
  rw [Cocycle.fromSingleMk_postcomp x.val (zero_add n) (n + 1) rfl
    (cycleCondition M I n x) φ, Cocycle.equivHomShift_symm_postcomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

end

/-- The normalized cocycle comparison exists on all bounded-below complexes of
injectives, and is compatible with maps between such complexes.
Source: Stacks Tags 06XR (1) and 070I.
Proof: send a concrete cycle `f` in the complex `Hom(M,I)` to the localized
shifted morphism of `Cocycle.fromSingleMk f`. This is additive. A boundary gives
a zero cohomology class, hence a null-homotopic morphism and a zero derived
morphism. Descend through the quotient of cycles by boundaries using
`QuotientAddGroup.lift`, and identify that quotient with abstract homology via
`ShortComplex.abHomologyIso`. Naturality of the homology projection and the
single-source cocycle constructor prove compatibility with chain maps, since
every homology class has a cycle representative. For injective complexes,
precompose with the homology comparison induced by the invertible derived unit.
The two inverse comparisons cancel in the normalization formula. Naturality of
the unit and of the homology-to-Q comparison gives compatibility after this
transport. No restriction on the integer degree is used.
(blueprint: lem-sc-p1-rhom-natural-cocycle-map-injective-family)
-/
theorem exists_rhom_injective_cocycle_family
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}]
    (M : C) :
    Nonempty (RhomInjectiveCocycleFamily M) := by
  classical
  let V := preadditiveCoyoneda.obj (op M)
  let RV := V.rightDerivedFunctorPlus
  let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
  let S := (DerivedCategory.singleFunctor C 0).obj M
  let Q := DerivedCategory.Plus.Q (C := C)
  let β (I : CochainComplex.Plus C) (hi : ∀ k : ℤ, Injective (I.obj.X k)) (n : ℤ) :
      (H n).obj (RV.obj (Q.obj I)) →+ (S ⟶ (Q.obj I).obj⟦n⟧) := by
    let := hi
    exact (homologyToDerived M I n).comp
      (V.homologyRightDerivedFunctorPlusObjQIsoOfInjective I n).hom.hom
  have hβ (I : CochainComplex.Plus C) (hi : ∀ k : ℤ, Injective (I.obj.X k))
      (n : ℤ) (f : M ⟶ I.obj.X n) (hf : f ≫ I.obj.d n (n + 1) = 0) :
      let J := (V.mapHomologicalComplex (.up ℤ)).obj I.obj
      let a := J.homologyπ n ((J.sc n).abCyclesIso.inv
        ⟨f, by
          change f ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0
          rw [CochainComplex.next]
          exact hf⟩)
      let b := (DerivedCategory.Plus.homologyFunctorObjQIso
        (V.mapCochainComplexPlus.obj I) n).inv a
      let η := V.rightDerivedFunctorPlusUnit.app I
      β I hi n ((H n).map η b) =
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
          ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧' := by
    let := hi
    dsimp only
    let E := V.homologyRightDerivedFunctorPlusObjQIsoOfInjective I n
    change homologyToDerived M I n (E.hom (E.inv _)) = _
    rw [← AddCommGrpCat.comp_apply, Iso.inv_hom_id, AddCommGrpCat.id_apply]
    refine (homologyToDerived_cycle M I n _).trans ?_
    rw [cycleToDerived_apply]
  refine ⟨{ map := β, normalize := hβ, natural := ?_ }⟩
  dsimp only
  intro I J hi hj n φ a
  let := hi
  let := hj
  let eI := V.homologyRightDerivedFunctorPlusObjQIsoOfInjective I n
  let eJ := V.homologyRightDerivedFunctorPlusObjQIsoOfInjective J n
  let φp : I ⟶ J := ObjectProperty.homMk φ
  let φ' := (V.mapHomologicalComplex (.up ℤ)).map φ
  let γ := V.mapCochainComplexPlus.map φp
  let eQI := DerivedCategory.Plus.homologyFunctorObjQIso (V.mapCochainComplexPlus.obj I) n
  let eQJ := DerivedCategory.Plus.homologyFunctorObjQIso (V.mapCochainComplexPlus.obj J) n
  let ηI := V.rightDerivedFunctorPlusUnit.app I
  let ηJ := V.rightDerivedFunctorPlusUnit.app J
  have heQ : HomologicalComplex.homologyMap φ' n ≫ eQJ.inv =
      eQI.inv ≫ (H n).map ((DerivedCategory.Plus.Q (C := AddCommGrpCat.{v})).map γ) := by
    apply (cancel_epi eQI.hom).1
    rw [Iso.hom_inv_id_assoc]
    erw [← DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality_assoc γ n]
    change (H n).map ((DerivedCategory.Plus.Q (C := AddCommGrpCat.{v})).map γ) ≫
      (eQJ.hom ≫ eQJ.inv) = _
    rw [Iso.hom_inv_id, Category.comp_id]
  have hη := congrArg ((H n).map)
    (V.rightDerivedFunctorPlusUnit.naturality φp)
  change (H n).map ((DerivedCategory.Plus.Q (C := AddCommGrpCat.{v})).map γ ≫ ηJ) =
    (H n).map (ηI ≫ RV.map (Q.map φp)) at hη
  simp only [Functor.map_comp] at hη
  have he : eI.inv ≫ (H n).map (RV.map (Q.map φp)) =
      HomologicalComplex.homologyMap φ' n ≫ eJ.inv := by
    change (eQI.inv ≫ (H n).map ηI) ≫ _ =
      HomologicalComplex.homologyMap φ' n ≫ (eQJ.inv ≫ (H n).map ηJ)
    rw [Category.assoc, ← hη, ← Category.assoc, ← heQ]
    simp only [Category.assoc]
  have he' : (H n).map (RV.map (Q.map φp)) ≫ eJ.hom =
      eI.hom ≫ HomologicalComplex.homologyMap φ' n := by
    apply (cancel_epi eI.inv).1
    rw [← Category.assoc, he]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  change homologyToDerived M J n (eJ.hom ((H n).map (RV.map (Q.map φp)) a)) =
    homologyToDerived M I n (eI.hom a) ≫ _
  have ha := ConcreteCategory.congr_hom he' a
  simp only [AddCommGrpCat.comp_apply] at ha
  rw [ha]
  exact homologyToDerived_natural M I J φ n (eI.hom a)

end CategoryTheory.Functor

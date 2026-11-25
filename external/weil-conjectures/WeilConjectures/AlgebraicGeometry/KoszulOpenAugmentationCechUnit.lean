/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSectionsUnit

/-! # The ordinary augmented Koszul cycle is the Cech unit

Source: Stacks Project, Tag 08D1, the signed fraction formula.
(blueprint: lem-sc-koszul-open-augmentation-cech-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem cycle_class_map
    {A : Type u} [CommRing A] {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : K ⟶ L) (x : (K.sc 0).moduleCatLeftHomologyData.K)
    (y : L.cycles 0) (h : g.f 0 x.val = L.iCycles 0 y) :
    HomologicalComplex.homologyMap g 0
      (((K.sc 0).moduleCatCyclesIso.inv ≫ K.homologyπ 0) x) =
        L.homologyπ 0 y := by
  have hc : HomologicalComplex.cyclesMap g 0 ((K.sc 0).moduleCatCyclesIso.inv x) = y := by
    apply (ModuleCat.mono_iff_injective (L.iCycles 0)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
    rw [ConcreteCategory.comp_apply]
    have hx : K.iCycles 0 ((K.sc 0).moduleCatCyclesIso.inv x) = x.val := by
      exact ConcreteCategory.congr_hom (K.sc 0).moduleCatCyclesIso_inv_iCycles x
    rw [hx]
    exact h
  change (HomologicalComplex.homologyMap g 0)
    (K.homologyπ 0 ((K.sc 0).moduleCatCyclesIso.inv x)) = _
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality]
  rw [ConcreteCategory.comp_apply, hc]

set_option backward.isDefEq.respectTransparency false in
private theorem contraction (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (j : Fin r) :
    koszulOpenAugmentationComponent A r f 0
      (exteriorPower.ιMulti A 1 (fun _ ↦ Finsupp.single j (1 : A))) = f j := by
  change exteriorPower.zeroEquiv A (Fin r →₀ A)
    (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (0 + 1)) 0
      (exteriorPower.ιMulti A 1 (fun _ ↦ Finsupp.single j (1 : A)))) = _
  have h : ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (0 + 1)) 0
      (exteriorPower.ιMulti A 1 (fun _ ↦ Finsupp.single j (1 : A))) =
      (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm (f j) := by
    apply Subtype.ext
    simp [ExteriorAlgebra.koszulBoundary, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      CliffordAlgebra.contractLeft_ι, Finsupp.linearCombination_single,
      exteriorPower.zeroEquiv_symm_apply, Algebra.algebraMap_eq_smul_one]
  rw [h, LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The singleton comparison value of the augmentation cochain is restriction of one.
Source: Stacks Project, Tag 08D1, signed fraction formula; Tag 08D0, singleton formula.
(blueprint: lem-sc-koszul-open-augmentation-cech-unit).

Proof: Transpose the tilde augmentation using the tilde/sections adjunction unit.
Its value on the singleton wedge e_j is f_j times the top-open image of one:
the Koszul contraction evaluates the defining linear form on e_j and the
exterior-degree-zero equivalence identifies its value with f_j. Rewrite the
stage-zero colimit injection followed by the comparison using colimit.ι_desc.
Apply the defining fraction equation of koszulCechCocone_exists. On a singleton
its denominator is f_j and its sign is positive. Restriction commutes with the
tilde unit, so the numerator is f_j times the restricted unit. Cancel f_j, which
acts invertibly on sections over D(f_j). The representative of one is
obtained by the inverse single-term X iso and the inverse extension X iso,
followed by the termwise tilde unit. There is no j when r=0. If f_j=0 its
principal open has zero sections; cancellation still holds, also for the
zero ring.
This calculation concerns only degree-zero cochains, before applying cycles or homology. -/
private theorem koszulOpen_augmentation_cech_value
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (j : Fin r) :
    let C := openStructureSheafComplex A
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj C
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    let L := openStructureModuleComplex A
    let η := (NatTrans.mapHomologicalComplex
      (affineOpenTildeSectionsUnit A (koszulOpen A r f)) (.up ℤ)).app L
    let x : L.X 0 := (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv
      ((HomologicalComplex.singleObjXSelf (.down ℕ) 0 (ModuleCat.of A A)).inv (1 : A))
    let t := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
        ComplexShape.embeddingDownNat)
    let k := (koszulCechHomObjIso A r f M 0).inv ≫
      colimit.ι (koszulCechHomDiagram A r f M) 0 ≫ koszulCechComparison A r f C
    ((k ≫ (principalCechObjIso r f C).hom).f 0)
      (CochainComplex.HomComplex.Cochain.ofHom
        (koszulOpenHomTranspose A r f C 0 t)) ⟨{j}, by simp⟩ =
      (((principalCechAugmentation r f).app C ≫
        (principalCechObjIso r f C).hom).f 0) (η.f 0 x) ⟨{j}, by simp⟩ := by
  dsimp only
  let C := openStructureSheafComplex A
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj C
  let t := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
      ComplexShape.embeddingDownNat)
  let z := CochainComplex.HomComplex.Cochain.ofHom
    (koszulOpenHomTranspose A r f C 0 t)
  let k := (koszulCechHomObjIso A r f M 0).inv ≫
    colimit.ι (koszulCechHomDiagram A r f M) 0 ≫ koszulCechComparison A r f C
  have hf := (koszulCechCocone_exists A r f C).choose_spec.2 0 0 z
    ⟨{j}, by simp⟩ (koszulCechCocone_exists A r f C).choose_spec.1
  simp only [Finset.prod_singleton, Finset.card_singleton, Nat.sub_self,
    zero_mul, Nat.zero_div, Int.natCast_zero, zero_add, Int.negOnePow_zero,
    one_smul, pow_one] at hf
  have hk : (koszulCechHomObjIso A r f M 0).inv ≫
      (koszulCechCocone A r f C).ι.app 0 ≫
        eqToHom (koszulCechCocone_exists A r f C).choose_spec.1 ≫
          (principalCechObjIso r f C).hom = k ≫ (principalCechObjIso r f C).hom := by
    dsimp only [k, M, koszulCechComparison]
    simp only [Category.assoc, colimit.ι_desc_assoc]
  erw [hk] at hf
  change f j • ((k ≫ (principalCechObjIso r f C).hom).f 0) z ⟨{j}, by simp⟩ =
    (modulesSpecToSheaf.obj (C.X 0)).obj.map
      (homOfLE (le_top : principalCechIntersection r f {j} ≤ ⊤)).op
      ((koszulOpenHomTranspose A r f C 0 t).f 0
        (koszulCechBasis A r f 0 {j} (by simp))) at hf
  let L := openStructureModuleComplex A
  let ηtop : L ⟶ M := (NatTrans.mapHomologicalComplex
    (affineOpenTildeSectionsUnit A ⊤) (.up ℤ)).app L
  let a := HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
    ComplexShape.embeddingDownNat
  have ht : koszulOpenHomTranspose A r f C 0 t = a ≫ ηtop := by
    let : (tilde.functor (.of A)).Additive :=
      ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
    let : (moduleSpecΓFunctor (R := .of A)).Additive :=
      ⟨fun {_ _} _ _ ↦ rfl⟩
    change ((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)).homEquiv
      _ _ (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).map a) = _
    rw [← Category.comp_id (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).map a),
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
    rfl
  rw [ht] at hf
  let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let x : L.X 0 := (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv
    ((HomologicalComplex.singleObjXSelf (.down ℕ) 0 (ModuleCat.of A A)).inv (1 : A))
  have hb : a.f 0 (koszulCechBasis A r f 0 {j} (by simp)) = f j • x := by
    dsimp only [a]
    rw [HomologicalComplex.extendMap_f _ _ (show
      ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)]
    simp only [koszulOpenAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    have hvec : koszulCechBasis A r f 0 {j} (by simp) =
        ((koszulOpenTail A r f 0).extendXIso ComplexShape.embeddingDownNat
          (i := 0) rfl).inv
            (exteriorPower.ιMulti A 1 (fun _ ↦ Finsupp.single j (1 : A))) := by
      dsimp only [koszulCechBasis]
      congr 2
      funext i
      congr 1
      exact Finset.orderEmbOfFin_singleton j i
    rw [hvec]
    simp only [ModuleCat.comp_apply]
    erw [Iso.inv_hom_id_apply, contraction]
    change (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv (f j) =
      f j • (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv (1 : A)
    erw [← map_smul]
    congr 1
    exact (mul_one (f j)).symm
  let U := koszulOpen A r f
  let S := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj C
  let η : L ⟶ S := (NatTrans.mapHomologicalComplex
    (affineOpenTildeSectionsUnit A U) (.up ℤ)).app L
  let resT := (modulesSpecToSheaf.obj (C.X 0)).obj.map
    (homOfLE (le_top : principalCechIntersection r f {j} ≤ ⊤)).op
  let resU := (modulesSpecToSheaf.obj (C.X 0)).obj.map
    (homOfLE (principalCechIntersection_singleton_le r f j)).op
  have ha := (principalCechAugmentation_exists r f).choose_spec.1 C 0 (η.f 0 x) j
  change (((principalCechAugmentation r f).app C ≫
    (principalCechObjIso r f C).hom).f 0) (η.f 0 x) ⟨{j}, by simp⟩ =
      resU (η.f 0 x) at ha
  have hres : resT (ηtop.f 0 x) = resU (η.f 0 x) := by
    rfl
  change f j • ((k ≫ (principalCechObjIso r f C).hom).f 0) z ⟨{j}, by simp⟩ =
    resT (ηtop.f 0 (a.f 0 (koszulCechBasis A r f 0 {j} (by simp)))) at hf
  rw [hb, map_smul, map_smul, hres, ← ha] at hf
  let N := (affineOpenSections A (principalCechIntersection r f {j})).obj (C.X 0)
  have hu : IsUnit (algebraMap A (Module.End A (↑N)) (f j)) :=
    Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := C.X 0) (f j)
      (by simp [principalCechIntersection])
  have hinj : Function.Injective (fun s : N ↦ f j • s) :=
    ((Module.End.isUnit_iff _).mp hu).1
  exact hinj hf

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation cycle and restriction of one have the same ordinary Cech class.
Source: Stacks Project, Tag 08D1, proof, the isomorphisms psi^{p,q} and the sign
(-1)^(pq+p(p-1)/2); Tag 08D0, singleton fraction formula.
(blueprint: lem-sc-koszul-open-augmentation-cech-unit).

Proof: Transpose the exponent-one augmentation through the tilde/sections
adjunction. On each singleton wedge e_j it gives f_j times the global unit.
The structure complex is zero outside degree zero. Consequently its degree-zero
Cech component can be nonzero only on singletons, where p=q=0 and the totalization
sign is +1. By the defining koszulCechCocone fraction equation, its value there
multiplied by f_j equals restriction of f_j. Multiplication by f_j is invertible
on D(f_j), so its value is restriction of one. For larger subsets the target
coefficient degree 1-card(J) is nonzero, and its sections module is zero. Thus
this cycle equals the Cech augmentation of the ordinary sections cycle of one.
The ordinary class openStructureUnitClass is represented by that same cycle:
extendHomologyIso and singleObjHomologySelfIso send 1 to its degree-zero unit,
and the termwise tilde.toOpen map restricts it to the chosen open. The naturality
of the short-complex cycles iso and homology projection sends these equal cycles
to the equality below. For r=0 the target Cech complex is zero; zero f_j and the
zero ring cause zero localization modules, so cancellation remains valid.
This is entirely a calculation of ordinary complex homology: no localization
of categories, derived functor, evaluation equivalence or inverse augmentation
is asserted. -/
theorem koszulOpen_augmentation_cech_unit
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    let C := openStructureSheafComplex A
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj C
    let t := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
        ComplexShape.embeddingDownNat)
    let k := (koszulCechHomObjIso A r f M 0).inv ≫
      colimit.ι (koszulCechHomDiagram A r f M) 0 ≫ koszulCechComparison A r f C
    HomologicalComplex.homologyMap k 0
        (koszulHomChainClass (koszulOpenHomTranspose A r f C 0 t)) =
      HomologicalComplex.homologyMap ((principalCechAugmentation r f).app C) 0
        (openStructureUnitClass A (koszulOpen A r f)) := by
  let C := openStructureSheafComplex A
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj C
  let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let L := openStructureModuleComplex A
  let S := ((affineOpenSections A (koszulOpen A r f)).mapHomologicalComplex (.up ℤ)).obj C
  let η : L ⟶ S := (NatTrans.mapHomologicalComplex
    (affineOpenTildeSectionsUnit A (koszulOpen A r f)) (.up ℤ)).app L
  let c : K.cycles 0 ≅ ModuleCat.of A A :=
    HomologicalComplex.singleObjCyclesSelfIso (.down ℕ) 0 (ModuleCat.of A A)
  let e : L.cycles 0 ≅ K.cycles 0 :=
    K.extendCyclesIso ComplexShape.embeddingDownNat (j := 0) rfl
  let z : L.cycles 0 := e.inv (c.inv (1 : A))
  let y : S.cycles 0 := HomologicalComplex.cyclesMap η 0 z
  let t := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
      ComplexShape.embeddingDownNat)
  let k := (koszulCechHomObjIso A r f M 0).inv ≫
    colimit.ι (koszulCechHomDiagram A r f M) 0 ≫ koszulCechComparison A r f C
  let α := (principalCechAugmentation r f).app C
  have hz : L.iCycles 0 z =
      (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv
        ((HomologicalComplex.singleObjXSelf (.down ℕ) 0
          (ModuleCat.of A A)).inv (1 : A)) := by
    change (e.inv ≫ L.iCycles 0) (c.inv (1 : A)) = _
    erw [HomologicalComplex.extendCyclesIso_inv_iCycles]
    rw [ConcreteCategory.comp_apply]
    change (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv
      ((c.inv ≫ K.iCycles 0) (1 : A)) = _
    erw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
  have hy : S.homologyπ 0 y = openStructureUnitClass A (koszulOpen A r f) := by
    change (HomologicalComplex.cyclesMap η 0 ≫ S.homologyπ 0) z = _
    rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
    congr 1
    change (e.inv ≫ L.homologyπ 0) (c.inv (1 : A)) = _
    erw [← HomologicalComplex.homologyπ_extendHomologyIso_inv]
    rw [ConcreteCategory.comp_apply]
    change (K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl).inv
      ((c.inv ≫ K.homologyπ 0) (1 : A)) = _
    erw [HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
    rfl
  have hv : k.f 0 (CochainComplex.HomComplex.Cochain.ofHom
      (koszulOpenHomTranspose A r f C 0 t)) =
        ((principalCechFunctor r f).obj C).iCycles 0
          (HomologicalComplex.cyclesMap α 0 y) := by
    rw [show ((principalCechFunctor r f).obj C).iCycles 0
        (HomologicalComplex.cyclesMap α 0 y) = α.f 0 (S.iCycles 0 y) from
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i α 0) y]
    rw [show S.iCycles 0 y = η.f 0 (L.iCycles 0 z) from
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i η 0) z]
    rw [hz]
    apply (ModuleCat.mono_iff_injective
      ((principalCechObjIso r f C).hom.f 0)).mp inferInstance
    change ((k ≫ (principalCechObjIso r f C).hom).f 0)
        (CochainComplex.HomComplex.Cochain.ofHom
          (koszulOpenHomTranspose A r f C 0 t)) =
      ((α ≫ (principalCechObjIso r f C).hom).f 0) _
    funext J
    by_cases hJ : J.val.card = 1
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hJ
      rcases J with ⟨J, hnonempty⟩
      dsimp only at hj
      subst J
      exact koszulOpen_augmentation_cech_value A r f j
    · have hpos := J.property.card_pos
      have hn : J.val.card - 1 ≠ 0 := by omega
      have hd : ComplexShape.embeddingDownNat.f (J.val.card - 1) =
          (0 : ℤ) + 1 - (J.val.card : ℤ) := by
        simp only [ComplexShape.embeddingDownNat_f]
        omega
      have hL : IsZero (L.X ((0 : ℤ) + 1 - (J.val.card : ℤ))) :=
        (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0
          (ModuleCat.of A A) (J.val.card - 1) hn).of_iso
            (K.extendXIso ComplexShape.embeddingDownNat hd)
      have hC : IsZero (C.X ((0 : ℤ) + 1 - (J.val.card : ℤ))) :=
        (koszulOpenTilde A).map_isZero hL
      have hS := (affineOpenSections A (principalCechIntersection r f J.val)).map_isZero hC
      let := (ModuleCat.isZero_iff_subsingleton.mp hS)
      exact Subsingleton.elim _ _
  change HomologicalComplex.homologyMap k 0
    (koszulHomChainClass (koszulOpenHomTranspose A r f C 0 t)) = _
  rw [show HomologicalComplex.homologyMap k 0
      (koszulHomChainClass (koszulOpenHomTranspose A r f C 0 t)) =
        ((principalCechFunctor r f).obj C).homologyπ 0
          (HomologicalComplex.cyclesMap α 0 y) from cycle_class_map k _ _ hv]
  rw [← ConcreteCategory.comp_apply]
  change (HomologicalComplex.cyclesMap α 0 ≫
    ((principalCechFunctor r f).obj C).homologyπ 0) y = _
  rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  exact congrArg (HomologicalComplex.homologyMap α 0) hy

end AlgebraicGeometry

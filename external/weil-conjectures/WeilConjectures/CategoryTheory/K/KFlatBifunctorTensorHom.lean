/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.BifunctorFlip

set_option linter.privateModule false

/-! # Derived tensor--Hom representability for an additive bifunctor

Source: Stacks Project, Tags 0A96 and 08J9, the K-flat/K-injective proof of
unbounded tensor--Hom adjunction
(blueprint: lem-sf-kflat-bifunctor-tensor-hom).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace DerivedNativeTensorProof

open CochainComplex CochainComplex.HomComplex HomologicalComplex CategoryTheory.Category

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCountableProducts C] [HasCountableCoproducts C]
  {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}
  [T.Additive] [∀ A, (T.obj A).Additive]
  [H.Additive] [∀ A, (H.obj A).Additive]
  (adj : T ⊣₂ H)

private instance totalExists (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) :
    HomologicalComplex.HasMapBifunctor P K T (.up ℤ) := by
  intro n
  let J := (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) ⁻¹' {n}
  have : HasColimitsOfShape (Discrete J) C :=
    HasCountableCoproducts.out J
  exact HasColimitsOfShape.has_colimit _

private noncomputable abbrev total (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) :=
  CochainComplex.mapBifunctor P K T

private noncomputable abbrev curry {P K Y : C} :
    ((T.obj P).obj K ⟶ Y) ≃+ (K ⟶ (H.obj (op P)).obj Y) :=
  (adj.adj P).homAddEquiv K Y

private noncomputable abbrev uncurry {P K Y : C} :=
  (curry adj (P := P) (K := K) (Y := Y)).symm

private lemma curry_smul {P K Y : C} (r : ℤˣ) (f : (T.obj P).obj K ⟶ Y) :
    curry adj (r • f) = r • curry adj f :=
  by
  simpa only [Units.smul_def] using map_zsmul (curry adj) (r : ℤ) f

private lemma uncurry_smul {P K Y : C} (r : ℤˣ)
    (f : K ⟶ (H.obj (op P)).obj Y) :
    uncurry adj (r • f) = r • uncurry adj f :=
  by
  simpa only [Units.smul_def] using map_zsmul (uncurry adj) (r : ℤ) f

private lemma curry_one {P P' K Y : C} (f : P' ⟶ P)
    (g : (T.obj P).obj K ⟶ Y) :
    curry adj ((T.map f).app K ≫ g) = curry adj g ≫ (H.map f.op).app Y :=
  adj.homEquiv_naturality_one f g

private lemma curry_two {P K K' Y : C} (f : K' ⟶ K)
    (g : (T.obj P).obj K ⟶ Y) :
    curry adj ((T.obj P).map f ≫ g) = f ≫ curry adj g :=
  adj.homEquiv_naturality_two f g

private lemma curry_three {P K Y Y' : C} (g : (T.obj P).obj K ⟶ Y) (f : Y ⟶ Y') :
    curry adj (g ≫ f) = curry adj g ≫ (H.obj (op P)).map f :=
  adj.homEquiv_naturality_three f g

private lemma total_d (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) (p q r r' : ℤ)
    (h : p + q = r) (h' : r + 1 = r') :
    ιMapBifunctor P K T (.up ℤ) p q r h ≫ (total T P K).d r r' =
      (T.map (P.d p (p + 1))).app (K.X q) ≫
          ιMapBifunctor P K T (.up ℤ) (p + 1) q r' (by change p + 1 + q = r'; omega) +
        p.negOnePow • ((T.obj (P.X p)).map (K.d q (q + 1)) ≫
          ιMapBifunctor P K T (.up ℤ) p (q + 1) r' (by change p + (q + 1) = r'; omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (show p + 1 + q = r' by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (show p + (q + 1) = r' by omega)]
  simp

private lemma total_d_assoc (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) (p q r r' : ℤ)
    (h : p + q = r) (h' : r + 1 = r') {Z : C} (f : (total T P K).X r' ⟶ Z) :
    ιMapBifunctor P K T (.up ℤ) p q r h ≫ (total T P K).d r r' ≫ f =
      ((T.map (P.d p (p + 1))).app (K.X q) ≫
          ιMapBifunctor P K T (.up ℤ) (p + 1) q r' (by change p + 1 + q = r'; omega) +
        p.negOnePow • ((T.obj (P.X p)).map (K.d q (q + 1)) ≫
          ιMapBifunctor P K T (.up ℤ) p (q + 1) r' (by change p + (q + 1) = r'; omega))) ≫ f := by
  rw [← assoc, total_d T P K p q r r' h h']

variable {P Y K : CochainComplex C ℤ}

private noncomputable def curryCochain {n : ℤ} (z : Cochain (total T P K) Y n) :
    Cochain K (bifunctorHomObj H P Y) n :=
  Cochain.mk fun q _ _ ↦ Pi.lift fun t ↦ (t.p * n).negOnePow •
    curry adj (ιMapBifunctor P K T (.up ℤ) t.p q (t.p + q) rfl ≫
      z.v (t.p + q) t.q (by grind [t.hpq]))

private noncomputable def uncurryCochain {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) :
    Cochain (total T P K) Y n :=
  Cochain.mk fun r s hrs ↦ mapBifunctorDesc fun p q (hpq : p + q = r) ↦ (p * n).negOnePow •
    uncurry adj (w.v q (s - p) (by lia) ≫ bifunctorHomπ H P Y (s - p) p s (by lia))

@[reassoc]
private lemma curryCochain_v_π {n : ℤ} (z : Cochain (total T P K) Y n)
    (q q' : ℤ) (hqq' : q + n = q')
    (p s : ℤ) (hps : p + q' = s) (r : ℤ) (hr : p + q = r) (hrs : r + n = s) :
    (curryCochain adj z).v q q' hqq' ≫ bifunctorHomπ H P Y q' p s hps =
      (p * n).negOnePow • curry adj (ιMapBifunctor P K T (.up ℤ) p q r hr ≫ z.v r s hrs) := by
  subst hr
  exact Pi.lift_comp_π _ _

@[reassoc]
private lemma ι_uncurryCochain_v {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) (r s : ℤ)
    (hrs : r + n = s) (p q : ℤ) (hpq : p + q = r) (q' : ℤ) (hqq' : q + n = q')
    (hps : p + q' = s) :
    ιMapBifunctor P K T (.up ℤ) p q r hpq ≫ (uncurryCochain adj w).v r s hrs =
      (p * n).negOnePow • uncurry adj (w.v q q' hqq' ≫ bifunctorHomπ H P Y q' p s hps) := by
  obtain rfl : q' = s - p := by lia
  rw [uncurryCochain, Cochain.mk_v, ι_mapBifunctorDesc]

variable (P Y K) in
private noncomputable def cochainEquiv (n : ℤ) :
    Cochain (total T P K) Y n ≃+ Cochain K (bifunctorHomObj H P Y) n where
  toFun := curryCochain adj
  invFun := uncurryCochain adj
  left_inv z := by
    apply Cochain.ext
    intro r s hrs
    apply mapBifunctor.hom_ext
    intro p q hpq
    replace hpq : p + q = r := hpq
    rw [ι_uncurryCochain_v adj _ r s hrs p q hpq (q + n) rfl (by lia),
      curryCochain_v_π adj _ q (q + n) rfl p s (by lia) r hpq hrs,
      uncurry_smul adj, AddEquiv.symm_apply_apply (curry adj),
      smul_smul, Int.units_mul_self, one_smul]
  right_inv w := by
    ext q q' hqq' p s hps
    rw [curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      ι_uncurryCochain_v adj _ (p + q) s (by lia) p q rfl q' hqq' hps,
      curry_smul adj, AddEquiv.apply_symm_apply (curry adj),
      smul_smul, Int.units_mul_self, one_smul]
  map_add' z z' := by
    ext q q' hqq' p s hps
    rw [Cochain.add_v, Preadditive.add_comp,
      curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia), Cochain.add_v,
      Preadditive.comp_add, map_add (curry adj), smul_add]

@[simp]
private lemma cochainEquiv_apply {n : ℤ} (z : Cochain (total T P K) Y n) :
    cochainEquiv adj P Y K n z = curryCochain adj z := rfl

@[simp]
private lemma cochainEquiv_symm_apply {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) :
    (cochainEquiv adj P Y K n).symm w = uncurryCochain adj w := rfl

@[simp]
private lemma curryCochain_uncurryCochain {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) :
    curryCochain adj (uncurryCochain adj w) = w :=
  (cochainEquiv adj P Y K n).apply_symm_apply w

@[simp]
private lemma uncurryCochain_curryCochain {n : ℤ} (z : Cochain (total T P K) Y n) :
    uncurryCochain adj (curryCochain adj z) = z :=
  (cochainEquiv adj P Y K n).symm_apply_apply z

private lemma curryCochain_δ (n m : ℤ) (z : Cochain (total T P K) Y n) :
    curryCochain adj (δ n m z) = δ n m (curryCochain adj z) := by
  by_cases hnm : n + 1 = m
  · subst hnm
    ext q q' hqq' p s hps
    rw [curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      δ_v n (n + 1) rfl z (p + q) s (by lia) (s - 1) (p + q + 1) (by lia) rfl,
      δ_v n (n + 1) rfl (curryCochain adj z) q q' hqq' (q' - 1) (q + 1) rfl rfl,
      Preadditive.add_comp, assoc, bifunctorHomObj_d_π H P Y (q' - 1) q' p s hps (s - 1) (p + 1)
        (by lia) (by lia), Linear.units_smul_comp, assoc,
      curryCochain_v_π adj _ (q + 1) q' (by lia) p s hps (p + q + 1) (by lia) (by lia),
      Linear.comp_units_smul, Preadditive.comp_sub, ← assoc, ← assoc,
      curryCochain_v_π adj _ q (q' - 1) (by lia) p (s - 1) (by lia) (p + q) rfl (by lia),
      curryCochain_v_π adj _ q (q' - 1) (by lia) (p + 1) s (by lia) (p + q + 1) (by lia) (by lia)]
    simp only [← curry_three adj, ← curry_one adj, ← curry_two adj, Preadditive.comp_add,
      Linear.comp_units_smul, assoc, total_d_assoc T P K p q (p + q) (p + q + 1) rfl rfl,
      Linear.units_smul_comp, ← curry_smul adj, ← map_sub (curry adj), ← map_add (curry adj)]
    congr 1
    simp only [Preadditive.add_comp, Linear.units_smul_comp, assoc, smul_add, smul_sub, smul_smul,
      mul_add, add_mul, mul_one, one_mul, Int.negOnePow_add, Int.negOnePow_one, mul_neg, neg_mul,
      Units.neg_smul, smul_neg, mul_comm _ p.negOnePow, mul_left_comm _ p.negOnePow, ← mul_assoc,
      Int.units_mul_self, mul_comm n.negOnePow]
    abel
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    exact (cochainEquiv adj P Y K m).map_zero

private lemma uncurryCochain_δ (n m : ℤ) (w : Cochain K (bifunctorHomObj H P Y) n) :
    uncurryCochain adj (δ n m w) = δ n m (uncurryCochain adj w) :=
  (cochainEquiv adj P Y K m).injective (by
    rw [cochainEquiv_apply, cochainEquiv_apply, curryCochain_δ adj, curryCochain_uncurryCochain adj,
      curryCochain_uncurryCochain adj])

variable (P Y K) in
private noncomputable def internalHomEquiv : (total T P K ⟶ Y) ≃ (K ⟶ bifunctorHomObj H P Y) where
  toFun f := Cocycle.homOf (Cocycle.mk (curryCochain adj (Cochain.ofHom f)) 1 (zero_add 1) (by
    rw [← curryCochain_δ adj, δ_ofHom, ← cochainEquiv_apply, map_zero]))
  invFun g := Cocycle.homOf (Cocycle.mk (uncurryCochain adj (Cochain.ofHom g)) 1 (zero_add 1) (by
    rw [← uncurryCochain_δ adj, δ_ofHom, ← cochainEquiv_symm_apply, map_zero]))
  left_inv f := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, uncurryCochain_curryCochain adj])
  right_inv g := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, curryCochain_uncurryCochain adj])

@[simp]
private lemma ofHom_internalHomEquiv (f : total T P K ⟶ Y) :
    Cochain.ofHom (internalHomEquiv adj P Y K f) = curryCochain adj (Cochain.ofHom f) := by
  simp [internalHomEquiv]

@[simp]
private lemma ofHom_internalHomEquiv_symm (g : K ⟶ bifunctorHomObj H P Y) :
    Cochain.ofHom ((internalHomEquiv adj P Y K).symm g) = uncurryCochain adj (Cochain.ofHom g) := by
  simp [internalHomEquiv]

@[reassoc]
private lemma internalHomEquiv_f_π (g : total T P K ⟶ Y) (q p s : ℤ) (hps : p + q = s) :
    (internalHomEquiv adj P Y K g).f q ≫ bifunctorHomπ H P Y q p s hps =
      curry adj (HomologicalComplex.ιMapBifunctor P K T (.up ℤ) p q s hps ≫ g.f s) := by
  rw [← Cochain.ofHom_v, ofHom_internalHomEquiv adj,
    curryCochain_v_π adj _ q q (add_zero q) p s hps s hps (add_zero s), Cochain.ofHom_v, mul_zero,
    Int.negOnePow_zero, one_smul]

private noncomputable def curryHomotopy {f f' : total T P K ⟶ Y} (h : Homotopy f f') :
    Homotopy (internalHomEquiv adj P Y K f) (internalHomEquiv adj P Y K f') :=
  (Cochain.equivHomotopy _ _).symm ⟨curryCochain adj (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv adj, ofHom_internalHomEquiv adj,
      ← curryCochain_δ adj, δ_ofHomotopy,
      ← cochainEquiv_apply, ← cochainEquiv_apply, ← cochainEquiv_apply,
      ← map_add, sub_add_cancel]⟩

private noncomputable def uncurryHomotopy {g g' : K ⟶ bifunctorHomObj H P Y}
    (h : Homotopy g g') :
    Homotopy ((internalHomEquiv adj P Y K).symm g)
      ((internalHomEquiv adj P Y K).symm g') :=
  (Cochain.equivHomotopy _ _).symm ⟨uncurryCochain adj (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv_symm adj, ofHom_internalHomEquiv_symm adj,
      ← uncurryCochain_δ adj, δ_ofHomotopy,
      ← cochainEquiv_symm_apply, ← cochainEquiv_symm_apply, ← cochainEquiv_symm_apply,
      ← map_add, sub_add_cancel]⟩

private noncomputable def homotopyEquiv :
    ((HomotopyCategory.quotient C (.up ℤ)).obj (total T P K) ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj Y) ≃
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj (bifunctorHomObj H P Y)) where
  toFun := Quot.lift
    (fun f ↦ (HomotopyCategory.quotient C (.up ℤ)).map (internalHomEquiv adj P Y K f))
    (by
      intro f f' h
      obtain ⟨h⟩ := (HomRel.compClosure_iff_self _ _ _).1 h
      exact HomotopyCategory.eq_of_homotopy _ _ (curryHomotopy adj h))
  invFun := Quot.lift
    (fun g ↦ (HomotopyCategory.quotient C (.up ℤ)).map
      ((internalHomEquiv adj P Y K).symm g))
    (by
      intro g g' h
      obtain ⟨h⟩ := (HomRel.compClosure_iff_self _ _ _).1 h
      exact HomotopyCategory.eq_of_homotopy _ _ (uncurryHomotopy adj h))
  left_inv := by
    intro f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
    change (HomotopyCategory.quotient C (.up ℤ)).map
      ((internalHomEquiv adj P Y K).symm (internalHomEquiv adj P Y K f)) = _
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro g
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
    change (HomotopyCategory.quotient C (.up ℤ)).map
      (internalHomEquiv adj P Y K ((internalHomEquiv adj P Y K).symm g)) = _
    rw [Equiv.apply_symm_apply]

private theorem internalHomEquiv_naturality
    {P' K' Y' : CochainComplex C ℤ} (f : P' ⟶ P) (g : K' ⟶ K) (h : Y ⟶ Y')
    (a : total T P K ⟶ Y) :
    internalHomEquiv adj P' Y' K' (mapBifunctorMap f g T (.up ℤ) ≫ a ≫ h) =
      g ≫ internalHomEquiv adj P Y K a ≫
        (bifunctorHomMapLeft (H := H) (Y := Y) f ≫
          bifunctorHomMapRight (H := H) (K := P') h) := by
  ext q p s hps
  simp only [HomologicalComplex.comp_f, assoc, internalHomEquiv_f_π adj,
    bifunctorHomMapRight_f_π, bifunctorHomMapLeft_f_π_assoc,
    ι_mapBifunctorMap_assoc]
  rw [internalHomEquiv_f_π_assoc adj]
  simp only [← assoc]
  rw [curry_three adj]
  simp only [assoc, curry_one adj, curry_two adj]

private theorem total_map_zero (P : CochainComplex C ℤ) :
    (T.map₂CochainComplex.obj P).PreservesZeroMorphisms := by
  constructor
  intro K L
  change mapBifunctorMap (𝟙 P) (0 : K ⟶ L) T (.up ℤ) = 0
  ext n : 1
  apply mapBifunctor.hom_ext
  intro p q hpq
  rw [ι_mapBifunctorMap]
  simp only [Functor.map_zero, comp_zero, zero_comp, HomologicalComplex.zero_f]

private theorem total_map_id (P K : CochainComplex C ℤ) :
    mapBifunctorMap (𝟙 P) (𝟙 K) T (.up ℤ) = 𝟙 (total T P K) := by
  have h := (T.map₂CochainComplex.obj P).map_id K
  exact h

include adj in
private theorem hom_isKInjective (P Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ {K K' : CochainComplex C ℤ} (f : K ⟶ K'), QuasiIso f →
      QuasiIso (mapBifunctorMap (𝟙 P) f T (.up ℤ))) :
    (bifunctorHomObj H P Y).IsKInjective := by
  let := total_map_zero (T := T) P
  constructor
  intro K f hK
  have hzero : QuasiIso (0 : K ⟶ (HomologicalComplex.zero : CochainComplex C ℤ)) := by
    constructor
    intro n
    exact (quasiIsoAt_iff_exactAt _ _ (hK n)).2
      (HomologicalComplex.acyclic_of_isZero _ HomologicalComplex.isZero_zero n)
  have ht := hP (0 : K ⟶ (HomologicalComplex.zero : CochainComplex C ℤ)) hzero
  have htotal : (total T P K).Acyclic := by
    intro n
    exact (quasiIsoAt_iff_exactAt'
      (mapBifunctorMap (𝟙 P) (0 : K ⟶ (HomologicalComplex.zero : CochainComplex C ℤ)) T (.up ℤ)) n
      (HomologicalComplex.acyclic_of_isZero _
        (Functor.map_isZero (T.map₂CochainComplex.obj P) HomologicalComplex.isZero_zero) n)).1
      (by infer_instance)
  let a := (internalHomEquiv adj P Y K).symm f
  let h := IsKInjective.homotopyZero a htotal
  have hz : internalHomEquiv adj P Y K (0 : total T P K ⟶ Y) = 0 := by
    apply Cochain.ofHom_injective
    rw [ofHom_internalHomEquiv adj, Cochain.ofHom_zero, Cochain.ofHom_zero]
    change cochainEquiv adj P Y K 0 0 = 0
    exact map_zero _
  simpa only [a, Equiv.apply_symm_apply, hz] using
    (show Nonempty (Homotopy (internalHomEquiv adj P Y K a)
      (internalHomEquiv adj P Y K (0 : total T P K ⟶ Y))) from
        ⟨curryHomotopy adj h⟩)

private noncomputable def qHomEquiv [HasDerivedCategory.{v} C]
    (K Y : CochainComplex C ℤ) [Y.IsKInjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj Y) ≃
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj Y) :=
  (Equiv.ofBijective _ (IsKInjective.Qh_map_bijective _ Y)).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
      ((DerivedCategory.quotientCompQhIso C).app Y))

private theorem qHomEquiv_map [HasDerivedCategory.{v} C]
    (K Y : CochainComplex C ℤ) [Y.IsKInjective] (f : K ⟶ Y) :
    qHomEquiv K Y ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  change (DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app Y = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

private noncomputable def derivedEquiv
    [HasDerivedCategory.{v} C] (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD) (P K Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ {L L' : CochainComplex C ℤ} (f : L ⟶ L'), QuasiIso f →
      QuasiIso (mapBifunctorMap (𝟙 P) f T (.up ℤ))) :
    (DerivedCategory.Q.obj (mapBifunctor K P T.flip (.up ℤ)) ⟶ DerivedCategory.Q.obj Y) ≃
      (DerivedCategory.Q.obj K ⟶
        HD.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj Y)) := by
  let := hom_isKInjective adj P Y hP
  exact (DerivedCategory.Q.mapIso (mapBifunctorFlipIso P K T (.up ℤ))).homFromEquiv.trans
    ((qHomEquiv (total T P K) Y).symm.trans
      ((homotopyEquiv adj).trans
        ((qHomEquiv K (bifunctorHomObj H P Y)).trans
          (R.model P Y inferInstance).symm.homToEquiv)))

private theorem derivedEquiv_map
    [HasDerivedCategory.{v} C] (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD) (P K Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ {L L' : CochainComplex C ℤ} (f : L ⟶ L'), QuasiIso f →
      QuasiIso (mapBifunctorMap (𝟙 P) f T (.up ℤ)))
    (f : mapBifunctor K P T.flip (.up ℤ) ⟶ Y) :
    derivedEquiv adj HD R P K Y hP (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (internalHomEquiv adj P Y K
        ((mapBifunctorFlipIso P K T (.up ℤ)).inv ≫ f)) ≫
        (R.model P Y inferInstance).inv := by
  let := hom_isKInjective adj P Y hP
  change (qHomEquiv K (bifunctorHomObj H P Y))
      (homotopyEquiv adj ((qHomEquiv (total T P K) Y).symm
        (DerivedCategory.Q.map (mapBifunctorFlipIso P K T (.up ℤ)).inv ≫
          DerivedCategory.Q.map f))) ≫ _ = _
  rw [← Functor.map_comp, ← qHomEquiv_map, Equiv.symm_apply_apply]
  change qHomEquiv K (bifunctorHomObj H P Y)
    ((HomotopyCategory.quotient C (.up ℤ)).map _) ≫ _ = _
  rw [qHomEquiv_map]
  rfl

private theorem derivedEquiv_naturality
    [HasDerivedCategory.{v} C] (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD)
    (P P' K K' Y Y' : CochainComplex C ℤ) [Y.IsKInjective] [Y'.IsKInjective]
    (hP : ∀ {L L' : CochainComplex C ℤ} (f : L ⟶ L'), QuasiIso f →
      QuasiIso (mapBifunctorMap (𝟙 P) f T (.up ℤ)))
    (hP' : ∀ {L L' : CochainComplex C ℤ} (f : L ⟶ L'), QuasiIso f →
      QuasiIso (mapBifunctorMap (𝟙 P') f T (.up ℤ)))
    (f : P' ⟶ P) (g : K' ⟶ K) (h : Y ⟶ Y')
    (a : DerivedCategory.Q.obj (mapBifunctor K P T.flip (.up ℤ)) ⟶
      DerivedCategory.Q.obj Y) :
    derivedEquiv adj HD R P' K' Y' hP'
        (DerivedCategory.Q.map (mapBifunctorMap g f T.flip (.up ℤ)) ≫
          a ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map g ≫ derivedEquiv adj HD R P K Y hP a ≫
        HD.map (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map h)) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨a, rfl⟩ := (qHomEquiv (mapBifunctor K P T.flip (.up ℤ)) Y).surjective a
  obtain ⟨a, rfl⟩ := q.map_surjective a
  rw [qHomEquiv_map]
  simp only [← Functor.map_comp]
  rw [derivedEquiv_map, derivedEquiv_map]
  have hflip : (mapBifunctorFlipIso P' K' T (.up ℤ)).inv ≫
      mapBifunctorMap g f T.flip (.up ℤ) =
      mapBifunctorMap f g T (.up ℤ) ≫ (mapBifunctorFlipIso P K T (.up ℤ)).inv := by
    apply (cancel_mono (mapBifunctorFlipIso P K T (.up ℤ)).hom).1
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [mapBifunctorFlipIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [← assoc (mapBifunctorFlipIso P' K' T (.up ℤ)).inv, hflip]
  simp only [assoc]
  have hc := internalHomEquiv_naturality adj f g h
    ((mapBifunctorFlipIso P K T (.up ℤ)).inv ≫ a)
  simp only [assoc] at hc
  rw [hc]
  simp only [Functor.map_comp, assoc]
  have hr := R.naturality P' P Y Y' inferInstance inferInstance f h
  have hr' : DerivedCategory.Q.map
      (bifunctorHomMapLeft (H := H) (Y := Y) f ≫
        bifunctorHomMapRight (H := H) (K := P') h) ≫ (R.model P' Y' inferInstance).inv =
      (R.model P Y inferInstance).inv ≫
        HD.map (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map h)) := by
    apply (cancel_mono (R.model P' Y' inferInstance).hom).1
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [hr, Iso.inv_hom_id_assoc]
  simpa only [Functor.map_comp, assoc] using
    congrArg (fun z ↦ DerivedCategory.Q.map g ≫
      DerivedCategory.Q.map (internalHomEquiv adj P Y K
        ((mapBifunctorFlipIso P K T (.up ℤ)).inv ≫ a)) ≫ z) hr'

end DerivedNativeTensorProof

namespace CategoryTheory

end CategoryTheory

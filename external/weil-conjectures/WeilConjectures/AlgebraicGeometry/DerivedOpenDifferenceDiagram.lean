/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenIntersectionMateIso
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # The difference diagram before derived open gluing

Source: Stacks Project, Tag 08DG, the difference arrow and its split restrictions.
(blueprint: lem-sc-derived-open-difference-diagram).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_upper_triangular
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {P Q A D : C} (e : P ⟶ A) (a : P ⟶ D) (b : Q ⟶ D)
    [IsIso e] [IsIso b] : IsIso (Biprod.ofComponents e a 0 b) := by
  have h : Biprod.ofComponents e a 0 b =
      biprod.map e b ≫ (Biprod.unipotentUpper (inv e ≫ a)).hom := by
    ext <;> simp [Biprod.unipotentUpper, Biprod.ofComponents]
  rw [h]
  have : IsIso (biprod.map e b) := (biprod.mapIso (asIso e) (asIso b)).isIso_hom
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_lift_from_first
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {P Q Z : C} {A : D}
    (e : F.obj P ⟶ A) (d : P ⊞ Q ⟶ Z) [IsIso e]
    (h : IsIso (F.map (biprod.inr : Q ⟶ P ⊞ Q) ≫ F.map d)) :
    IsIso (biprod.lift (F.map biprod.fst ≫ e) (F.map d)) := by
  have : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  have : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  have : IsIso ((F.mapBiprod P Q).inv ≫
      biprod.lift (F.map biprod.fst ≫ e) (F.map d)) := by
    have heq : (F.mapBiprod P Q).inv ≫
        biprod.lift (F.map biprod.fst ≫ e) (F.map d) =
        Biprod.ofComponents e (F.map biprod.inl ≫ F.map d) 0
          (F.map biprod.inr ≫ F.map d) := by
      ext <;> simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
        Biprod.inl_ofComponents, Biprod.inr_ofComponents, Preadditive.add_comp,
        biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd,
        Category.comp_id, comp_zero, zero_comp,
        add_zero, zero_add, Functor.mapBiprod_inv, biprod.inl_desc_assoc,
        biprod.inr_desc_assoc, ← F.map_comp_assoc, Functor.map_zero]
      all_goals first
      | exact (F.map_id P ▸ Category.id_comp e)
      | exact (F.map_comp _ _).symm
    rw [heq]
    exact isIso_upper_triangular _ _ _
  exact IsIso.of_isIso_comp_left (F.mapBiprod P Q).inv _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_lift_from_second
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {P Q Z : C} {B : D}
    (e : F.obj Q ⟶ B) (d : P ⊞ Q ⟶ Z) [IsIso e]
    (h : IsIso (F.map (biprod.inl : P ⟶ P ⊞ Q) ≫ F.map d)) :
    IsIso (biprod.lift (F.map biprod.snd ≫ e) (F.map d)) := by
  have h' : IsIso (F.map (biprod.inr : P ⟶ Q ⊞ P) ≫
      F.map ((biprod.braiding Q P).hom ≫ d)) := by
    have hb : (biprod.inr : P ⟶ Q ⊞ P) ≫ (biprod.braiding Q P).hom =
        biprod.inl := by ext <;> simp [biprod.braiding]
    rw [F.map_comp, ← Category.assoc, ← F.map_comp, hb]
    exact h
  have ht := isIso_lift_from_first F e ((biprod.braiding Q P).hom ≫ d) h'
  have heq : biprod.lift (F.map biprod.fst ≫ e)
      (F.map ((biprod.braiding Q P).hom ≫ d)) =
      F.map (biprod.braiding Q P).hom ≫
        biprod.lift (F.map biprod.snd ≫ e) (F.map d) := by
    ext
    · simp only [Category.assoc, biprod.lift_fst, ← F.map_comp_assoc,
        biprod.braiding_hom, biprod.lift_snd]
    · simp only [Category.assoc, biprod.lift_snd, F.map_comp]
  rw [heq] at ht
  exact IsIso.of_isIso_comp_left (F.map (biprod.braiding Q P).hom) _

/-- The difference construction depends only on additive adjunctions and invertible cross mates.
Keeping the biproduct calculation abstract avoids unfolding the derived restriction functors. -/
private theorem difference_diagram_of_adjunctions
    {C C₁ C₂ C₁₂ : Type*}
    [Category C] [Category C₁] [Category C₂] [Category C₁₂]
    [Preadditive C] [Preadditive C₁] [Preadditive C₂] [Preadditive C₁₂]
    [HasBinaryBiproducts C] [HasBinaryBiproducts C₁] [HasBinaryBiproducts C₂]
    {rU : C ⥤ C₁} {rV : C ⥤ C₂} {rW : C ⥤ C₁₂}
    {sU : C₁ ⥤ C₁₂} {sV : C₂ ⥤ C₁₂}
    [rU.Additive] [rV.Additive] [rW.Additive] [sU.Additive] [sV.Additive]
    {jU : C₁ ⥤ C} {jV : C₂ ⥤ C} {jW : C₁₂ ⥤ C}
    (adjU : rU ⊣ jU) (adjV : rV ⊣ jV) (adjW : rW ⊣ jW)
    [IsIso adjU.counit] [IsIso adjV.counit]
    (eU : rU ⋙ sU ≅ rW) (eV : rV ⋙ sV ≅ rW)
    (A : C₁) (B : C₂) (c : sU.obj A ≅ sV.obj B)
    (hf : IsIso (rV.map ((adjW.homEquiv (jU.obj A) (sU.obj A))
      (eU.inv.app _ ≫ sU.map (adjU.counit.app A)))))
    (hg : IsIso (rU.map ((adjW.homEquiv (jV.obj B) (sV.obj B))
      (eV.inv.app _ ≫ sV.map (adjV.counit.app B))))) :
    let E := jU.obj A ⊞ jV.obj B;
    let D := jW.obj (sV.obj B);
    ∃ (d : E ⟶ D) (pU : rU.obj E ⟶ A) (pV : rV.obj E ⟶ B)
      (k : rW.obj D ⟶ sV.obj B),
      IsIso (biprod.lift pU (rU.map d)) ∧
      IsIso (biprod.lift pV (rV.map d)) ∧
      eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV = rW.map d ≫ k := by
  let E := jU.obj A ⊞ jV.obj B
  let εU : rU.obj (jU.obj A) ⟶ A := adjU.counit.app A
  let εV : rV.obj (jV.obj B) ⟶ B := adjV.counit.app B
  let pU : rU.obj E ⟶ A := rU.map biprod.fst ≫ εU
  let pV : rV.obj E ⟶ B := rV.map biprod.snd ≫ εV
  let t : rW.obj E ⟶ sV.obj B :=
    eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV
  let d := (adjW.homEquiv E (sV.obj B)) t
  let f := (adjW.homEquiv (jU.obj A) (sU.obj A))
    (eU.inv.app _ ≫ sU.map εU)
  let g := (adjW.homEquiv (jV.obj B) (sV.obj B))
    (eV.inv.app _ ≫ sV.map εV)
  change IsIso (rV.map f) at hf
  change IsIso (rU.map g) at hg
  have hU : rW.map (biprod.inl : jU.obj A ⟶ E) ≫ t =
      eU.inv.app _ ≫ sU.map εU ≫ c.hom := by
    dsimp only [t, pU, pV]
    rw [Preadditive.comp_sub]
    rw [eU.inv.naturality_assoc, eV.inv.naturality_assoc]
    change eU.inv.app _ ≫ sU.map (rU.map biprod.inl) ≫
        sU.map (rU.map biprod.fst ≫ εU) ≫ c.hom -
      eV.inv.app _ ≫ sV.map (rV.map biprod.inl) ≫
        sV.map (rV.map biprod.snd ≫ εV) = _
    simp only [← sU.map_comp_assoc, ← sV.map_comp, ← rU.map_comp_assoc,
      ← rV.map_comp_assoc, biprod.inl_fst, biprod.inl_snd,
      Functor.map_zero, zero_comp, comp_zero, sub_zero]
    rw [rU.map_id, Category.id_comp]
  have hV : rW.map (biprod.inr : jV.obj B ⟶ E) ≫ t =
      -(eV.inv.app _ ≫ sV.map εV) := by
    dsimp only [t, pU, pV]
    rw [Preadditive.comp_sub]
    rw [eU.inv.naturality_assoc, eV.inv.naturality_assoc]
    change eU.inv.app _ ≫ sU.map (rU.map biprod.inr) ≫
        sU.map (rU.map biprod.fst ≫ εU) ≫ c.hom -
      eV.inv.app _ ≫ sV.map (rV.map biprod.inr) ≫
        sV.map (rV.map biprod.snd ≫ εV) = _
    simp only [← sU.map_comp_assoc, ← sV.map_comp, ← rU.map_comp_assoc,
      ← rV.map_comp_assoc, biprod.inr_fst, biprod.inr_snd,
      Functor.map_zero, zero_comp, comp_zero, zero_sub]
    rw [rV.map_id, Category.id_comp]
  have hdU : (biprod.inl : jU.obj A ⟶ E) ≫ d = f ≫ jW.map c.hom := by
    rw [← adjW.homEquiv_naturality_left, hU]
    simpa only [Category.assoc, f] using
      adjW.homEquiv_naturality_right (eU.inv.app _ ≫ sU.map εU) c.hom
  have : jW.Additive := adjW.right_adjoint_additive
  have hdV : (biprod.inr : jV.obj B ⟶ E) ≫ d = -g := by
    rw [← adjW.homEquiv_naturality_left, hV]
    simp only [Adjunction.homEquiv_apply, Functor.map_neg, Preadditive.comp_neg, g]
  refine ⟨d, pU, pV, adjW.counit.app (sV.obj B), ?_, ?_, ?_⟩
  · apply isIso_lift_from_first rU εU d
    rw [← rU.map_comp, hdV, rU.map_neg]
    exact ⟨⟨-inv (rU.map g), by simp, by simp⟩⟩
  · apply isIso_lift_from_second rV εV d
    rw [← rV.map_comp, hdU, rV.map_comp]
    infer_instance
  · exact ((adjW.homEquiv E (sV.obj B)).symm_apply_apply t).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
/-- The difference arrow has split normal form on each of the two opens.
The middle and last objects are the explicit direct-image sum and overlap image.
This constructs their maps, not a glued object.
Source: Stacks Project, Cohomology, Tag 08DG, construction of the difference arrow;
Tag 08FE for restriction of direct images
(blueprint: lem-sc-derived-open-difference-diagram).

Proof: write W = U ∩ V and use the exact restriction functors rU, rV, rW and
sU, sV displayed below. Their canonical composition comparisons are eU and eV.
The underived open adjunction is `(Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
(Scheme.Modules.overFunctorEquiv O).symm`; derive it with
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`. Call these adjunctions
adjU, adjV and adjW. Take E = RjU_* A ⊕ RjV_* B and D = RjW_* (sV B).
The adjunction counits define
pU : rU E → A and pV : rV E → B by projection onto the corresponding summand.
The adjoint of c on the U summand and the negative of the adjoint of the identity
on the V summand define d : E → D. Explicitly, adjW.homEquiv sends
(eU⁻¹ on RjU A, then sU of adjU.counit on A, then c) to the U component;
it sends (eV⁻¹ on RjV B, then sV of adjV.counit on B) to the V component.
Take biprod.desc of the first and the negative of the second. The projections are
rU(biprod.fst) followed by adjU.counit and rV(biprod.snd) followed by adjV.counit.
The restriction counit k is adjW.counit on sV B, a map rW D → sV B.
Naturality and the triangle identities of the three derived open adjunctions give
(eU⁻¹ followed by sU pU followed by c) minus (eV⁻¹ followed by sV pV) = rW d
followed by k. Here the equivalence unit in eU and eV is precisely the comparison
between restriction on the over-category and restriction on the open subscheme.
By Tag 08FE, on U the V summand of E and D both identify with the same derived
pushforward from W to U; d on this summand is minus its identity. The U summand
restricts to A, with pU its identity and pU zero on the other summand. Thus the
matrix (pU, rU d) is invertible: its diagonal is (1, -1), and subtracting the
lower-left entry gives its explicit inverse. On V the analogous matrix has
invertible diagonal given by the identity on B and the direct image of c after
interchanging summands, hence is invertible too.
These sectionwise adjunction and matrix calculations remain valid for empty opens
or empty W, when the corresponding category is zero. No covering hypothesis is
needed for these local calculations, though it is retained for the caller. -/
theorem derived_open_difference_diagram
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let E := (schemeDerivedDirectImage U.ι).obj A ⊞ (schemeDerivedDirectImage V.ι).obj B;
    let D := (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B);
    ∃ (d : E ⟶ D)
      (pU : rU.obj E ⟶ A) (pV : rV.obj E ⟶ B)
      (k : rW.obj D ⟶ sV.obj B),
      IsIso (biprod.lift pU (rU.map d)) ∧
      IsIso (biprod.lift pV (rV.map d)) ∧
      eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV = rW.map d ≫ k := by
  have _cover := hcover
  classical
  dsimp only
  let adj (O : X.Opens)
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))] :
      (schemeOpenRestriction X O).mapDerivedCategory ⊣ schemeDerivedDirectImage O.ι := by
    let a : schemeOpenRestriction X O ⊣
        RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom :=
      (Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
        (Scheme.Modules.overFunctorEquiv O).symm
    exact a.mapDerivedCategoryRightDerivedAdjunction
  have hc (O : X.Opens)
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))] :
      IsIso (adj O).counit := by
    let a : schemeOpenRestriction X O ⊣
        RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom :=
      (Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
        (Scheme.Modules.overFunctorEquiv O).symm
    have : IsIso a.counit := by
      dsimp [a, Adjunction.ofNatIsoLeft]
      infer_instance
    have : (RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom).Full :=
      a.fullyFaithfulROfIsIsoCounit.full
    have : (RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom).Faithful :=
      a.fullyFaithfulROfIsIsoCounit.faithful
    have : (RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom).PreservesKInjectiveComplexes :=
      a.preservesKInjectiveComplexes
    exact Adjunction.counit_isIso_of_R_fully_faithful (adj O)
  have := hc U
  have := hc V
  exact difference_diagram_of_adjunctions (adj U) (adj V) (adj (U ⊓ V))
    (schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U))
    (schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V)) A B c
    (derived_open_intersection_mate_isIso X V U (U ⊓ V) (inf_comm U V)
      (homOfLE inf_le_left) (adj U) (adj (U ⊓ V)) A)
    (derived_open_intersection_mate_isIso X U V (U ⊓ V) rfl
      (homOfLE inf_le_right) (adj V) (adj (U ⊓ V)) B)

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import all WeilConjectures.AlgebraicGeometry.RingedLocalizationModels
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Idempotence of the actual Cech completion unit

Source: Stacks Project, algebraization.tex, Tag 099B.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory Limits MonoidalCategory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

omit [HasDerivedCategory (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] in
private theorem total_map (K₁ K₂ L₁ L₂ : ringedSiteComplex O)
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    letI := SheafOfModules.monoidalCategory O
    (KFlatRHom.total O).map (X := (K₁, K₂)) (Y := (L₁, L₂)) (f, g) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ) := by
  let := SheafOfModules.monoidalCategory O
  change HomologicalComplex.mapBifunctorMap f (𝟙 K₂) (curriedTensor _) (.up ℤ) ≫
    HomologicalComplex.mapBifunctorMap (𝟙 L₁) g (curriedTensor _) (.up ℤ) = _
  simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]

omit [HasDerivedCategory (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] in
private theorem ringComplex_kflat :
    CochainComplex.IsKFlatTensor (ringedSiteRingComplex O) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (ne_of_gt hn)
  · intro n
    let := SheafOfModules.monoidalCategory O
    by_cases hn : n = 0
    · subst n
      have h := ObjectProperty.prop_unit
        (ObjectProperty.flat (A := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
      exact ((ObjectProperty.flat).prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm h).tensorRight
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)).tensorRight

omit [HasDerivedCategory (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] in
private theorem localizationFactor_kflat
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsKFlatTensor (ringedLocalizationTwoTerm O s) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨1, fun n hn ↦ ?_⟩
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, ite_eq_right (show n ≠ 0 by omega),
      ite_eq_right (show n ≠ 1 by omega)]
    exact isZero_zero _
  · intro n
    change SheafOfModules.IsFlat (ringedLocalizationTwoTermX O s n)
    by_cases hn : n = 0
    · subst n
      rw [ringedLocalizationTwoTermX_zero]
      let := SheafOfModules.monoidalCategory O
      exact (ObjectProperty.prop_unit (ObjectProperty.flat)).tensorRight
    · by_cases hn' : n = 1
      · subst n
        rw [ringedLocalizationTwoTermX_one]
        exact localization_isFlat O s
      · simp only [ringedLocalizationTwoTermX, ite_eq_right hn, ite_eq_right hn']
        let := SheafOfModules.monoidalCategory O
        exact (ObjectProperty.flat_of_isZero (isZero_zero _)).tensorRight

omit [HasDerivedCategory (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] in
private theorem cech_kflat :
    CochainComplex.IsKFlatTensor (ringedExtendedCech O r b).1 := by
  induction r with
  | zero => exact ringComplex_kflat O
  | succ r ih =>
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := (SheafOfModules.tensorClosed O).1.some
    let := (SheafOfModules.tensorClosed O).2.1.some
    intro M hM i
    exact (ih (fun j ↦ b j.succ) _ (localizationFactor_kflat O (b 0) M hM) i).of_iso
      (HomologicalComplex.associator M (ringedLocalizationTwoTerm O (b 0))
        (ringedExtendedCech O r (fun j ↦ b j.succ)).1)

private theorem derivedHomUnit_isIso (E : ringedSiteDerived O) :
    IsIso (ringedDerivedHomUnit O E) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app
      (DerivedCategory.Q.objPreimage E)) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
  let e := DerivedCategory.Q.objObjPreimageIso E
  dsimp only [ringedDerivedHomUnit]
  repeat' apply IsIso.comp_isIso'
  all_goals try infer_instance
  change IsIso ((derivedInternalHom J O).mapIso ((Iso.refl _).prod e)).hom
  infer_instance

private theorem augmented_kflat_unit_idempotence
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : CochainComplex.IsKFlatTensor K)
    (hleft : QuasiIso ((KFlatRHom.total O).map (X := (K, K))
      (Y := (K, ringedSiteRingComplex O)) (𝟙 K, ε)))
    (hright : QuasiIso ((KFlatRHom.total O).map (X := (K, K))
      (Y := (ringedSiteRingComplex O, K)) (ε, 𝟙 K)))
    (E : ringedSiteDerived O) :
    IsIso ((ringedCechCompletionFunctor O K).map (ringedCechCompletionUnit O K ε E)) ∧
    IsIso (ringedCechCompletionUnit O K ε ((ringedCechCompletionFunctor O K).obj E)) := by
  let P : (KFlatRHom.flat O).FullSubcategory := ⟨K, hK⟩
  let U : (KFlatRHom.flat O).FullSubcategory :=
    ⟨ringedSiteRingComplex O, ringComplex_kflat O⟩
  let a : P ⟶ U := ObjectProperty.homMk ε
  let H := derivedInternalHom J O
  let Q := DerivedCategory.Q (C := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let L := ringedCechCompletionFunctor O K
  let pre (X : ringedSiteDerived O) :
      H.obj (op (Q.obj (ringedSiteRingComplex O)), X) ⟶ L.obj X :=
    H.map (X := (op (Q.obj (ringedSiteRingComplex O)), X))
      (Y := (op (Q.obj K), X)) ((Q.map ε).op, 𝟙 X)
  have hd (X : ringedSiteDerived O) : IsIso (ringedDerivedHomUnit O X) :=
    derivedHomUnit_isIso O X
  have hl : IsIso (L.map (pre E)) := by
    let X := (op P, (op U, E))
    let Y := (op P, (op P, E))
    let f : X ⟶ Y := (𝟙 _, (a.op, 𝟙 E))
    have hn := (KFlatRHom.curryIso O).hom.naturality f
    have ht : IsIso ((KFlatRHom.right O).map f) := by
      have : IsIso (Q.map ((KFlatRHom.total O).map (X := (K, K))
      (Y := (K, ringedSiteRingComplex O)) (𝟙 K, ε))) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hleft
      have : IsIso (Prod.mkHom
          (Q.map ((KFlatRHom.total O).map (X := (K, K))
            (Y := (K, ringedSiteRingComplex O)) (𝟙 K, ε))).op (𝟙 E)) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      change IsIso (H.map
        (X := (op (Q.obj ((KFlatRHom.total O).obj (K, ringedSiteRingComplex O))), E))
        (Y := (op (Q.obj ((KFlatRHom.total O).obj (K, K))), E))
        ((Q.map ((KFlatRHom.total O).map (X := (K, K))
          (Y := (K, ringedSiteRingComplex O)) (𝟙 K, ε))).op, 𝟙 E))
      infer_instance
    have : IsIso ((KFlatRHom.left O).map f) := by
      rw [← isIso_comp_right_iff ((KFlatRHom.left O).map f)
        ((KFlatRHom.curryIso O).hom.app Y), hn]
      infer_instance
    change IsIso (H.map
      (X := (op (Q.obj K), H.obj (op (Q.obj (ringedSiteRingComplex O)), E)))
      (Y := (op (Q.obj K), H.obj (op (Q.obj K), E)))
      ((Q.map (𝟙 K)).op, pre E)) at this
    simpa only [L, ringedCechCompletionFunctor, Functor.curry_obj_obj_map,
      Functor.map_id, op_id, ← prod_id'] using this
  have hr : IsIso (pre (L.obj E)) := by
    let X := (op U, (op P, E))
    let Y := (op P, (op P, E))
    let f : X ⟶ Y := (a.op, (𝟙 _, 𝟙 E))
    have hn := (KFlatRHom.curryIso O).hom.naturality f
    have ht : IsIso ((KFlatRHom.right O).map f) := by
      have : IsIso (Q.map ((KFlatRHom.total O).map (X := (K, K))
      (Y := (ringedSiteRingComplex O, K)) (ε, 𝟙 K))) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hright
      have : IsIso (Prod.mkHom
          (Q.map ((KFlatRHom.total O).map (X := (K, K))
            (Y := (ringedSiteRingComplex O, K)) (ε, 𝟙 K))).op (𝟙 E)) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      change IsIso (H.map
        (X := (op (Q.obj ((KFlatRHom.total O).obj (ringedSiteRingComplex O, K))), E))
        (Y := (op (Q.obj ((KFlatRHom.total O).obj (K, K))), E))
        ((Q.map ((KFlatRHom.total O).map (X := (K, K))
          (Y := (ringedSiteRingComplex O, K)) (ε, 𝟙 K))).op, 𝟙 E))
      infer_instance
    have : IsIso ((KFlatRHom.left O).map f) := by
      rw [← isIso_comp_right_iff ((KFlatRHom.left O).map f)
        ((KFlatRHom.curryIso O).hom.app Y), hn]
      infer_instance
    change IsIso (H.map
      (X := (op (Q.obj (ringedSiteRingComplex O)), L.obj E))
      (Y := (op (Q.obj K), L.obj E))
      ((Q.map ε).op, H.map (X := (op (Q.obj K), E))
        (Y := (op (Q.obj K), E)) ((Q.map (𝟙 K)).op, 𝟙 E))) at this
    simpa only [pre, L, ringedCechCompletionFunctor, Functor.curry_obj_obj_obj,
      Functor.map_id, op_id, ← prod_id'] using this
  have : IsIso (ringedDerivedHomUnit O E) := hd E
  have : IsIso (ringedDerivedHomUnit O (L.obj E)) := hd (L.obj E)
  constructor
  · change IsIso (L.map (ringedDerivedHomUnit O E ≫ pre E))
    rw [Functor.map_comp]
    exact IsIso.comp_isIso
  · change IsIso (ringedDerivedHomUnit O (L.obj E) ≫ pre (L.obj E))
    exact IsIso.comp_isIso

omit [HasDerivedCategory (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] in
private theorem cech_tensor_projections :
    QuasiIso ((KFlatRHom.total O).map
      (X := ((ringedExtendedCech O r b).1, (ringedExtendedCech O r b).1))
      (Y := ((ringedExtendedCech O r b).1, ringedSiteRingComplex O))
      (𝟙 _, (ringedExtendedCech O r b).2)) ∧
    QuasiIso ((KFlatRHom.total O).map
      (X := ((ringedExtendedCech O r b).1, (ringedExtendedCech O r b).1))
      (Y := (ringedSiteRingComplex O, (ringedExtendedCech O r b).1))
      ((ringedExtendedCech O r b).2, 𝟙 _)) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let K := (ringedExtendedCech O r b).1
  let ε := (ringedExtendedCech O r b).2
  have hl : QuasiIso (K ◁ ε) := by
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    exact (ringed_cech_tensor_augmentation_cone_acyclic O r b).of_iso
      (CochainComplex.mapBifunctorMappingCone₂Iso K ε
        (MonoidalCategory.curriedTensor A))
  have hr : QuasiIso (ε ▷ K) := by
    have h := BraidedCategory.braiding_naturality_right K ε
    have hc : QuasiIso ((K ◁ ε) ≫ (CategoryTheory.BraidedCategory.braiding K
        (ringedSiteRingComplex O)).hom) := inferInstance
    rw [h] at hc
    exact (quasiIso_iff_comp_left _ _).1 hc
  rw [total_map, total_map]
  exact ⟨hl, hr⟩

/-- Applying Cech completion to its unit and evaluating the unit on a completed
object both give isomorphisms. These are statements about the two actual maps,
not about an unspecified isomorphism between double and single completion.

Source: Stacks Project, algebraization.tex, Tag 099B, proof of lemma-derived-completion.
(auxiliary; not a blueprint node).

Proof: write K in degree q as the finite sum over q-element subsets I of the
localizations S_I = O[1/(product of b_i for i in I)], with S_empty = O. These sheaves
are flat, and K is bounded, so K is K-flat. For a nonempty I, choose j in I. In
K tensor S_I the j-th localization factor has invertible differential: b_j is already
invertible in S_I. Contract it by that inverse differential. On a tensor summand,
put the sign (-1) to the sum of the degrees preceding j; the other differential terms
cancel in d h + h d, while the j-th term gives the identity.

Cancel the identity ring-term pair in the cone of the augmentation K -> O. The
remaining positive localization complex has a finite filtration by Cech degree, with
graded terms finite sums of shifted S_I for nonempty I. After tensoring with K these
graded terms are contractible by the preceding formula, so the tensor is acyclic.
The tensor/mapping-cone comparison shows that id_K tensor epsilon followed by the
right unit comparison is a quasi-isomorphism. Symmetry gives the other projection,
epsilon tensor id_K followed by the left unit comparison.

For a K-injective representative I of E, Hom(K,I) is K-injective since K is K-flat.
Compute the actual unit on these representatives using evaluation at one and the
fixed functorial-replacement comparison defining derived internal Hom. Tensor-Hom
currying identifies L(eta_E) with Hom of id_K tensor epsilon, and eta_(L E) with
Hom of epsilon tensor id_K, after the respective ring-unit identifications. The
K-injective comparison maps intertwine these actual units; their compatibility follows
from evaluation at one and naturality of precomposition. Both projections are
quasi-isomorphisms, and Hom into I inverts them, proving both assertions. This uses
neither enough points nor exactness of infinite products. For the empty list the
positive filtration is empty and the projections are unit isomorphisms. An all-zero
list gives identity completion; an invertible generator gives contractible K and zero
completion. The same formulas include the zero ring and the empty site. -/
theorem ringed_cech_completion_unit_idempotence (E : ringedSiteDerived O) :
    IsIso ((ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).map
      (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2 E)) ∧
    IsIso (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
      (ringedExtendedCech O r b).2
      ((ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj E)) := by
  obtain ⟨hl, hr⟩ := cech_tensor_projections O r b
  exact augmented_kflat_unit_idempotence O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2 (cech_kflat O r b) hl hr E

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso
import Mathlib.Algebra.Homology.Factorizations.CM5a
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # The cohomology formula for a fixed augmented lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
-/

@[expose] public section
universe uBC u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Extend by zero, apply Mathlib's injective replacement with lower bound zero, and
use the full extension functor to recover a natural-indexed quasi-isomorphism.
Source: Stacks Project, Derived Categories, Tag 013K; Mathlib's
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`. -/
private theorem augmentedLift_injective_resolution
    {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
    (A : CochainComplex C ℕ) :
    ∃ (B : CochainComplex C ℕ) (i : A ⟶ B),
      (∀ n : ℕ, Injective (B.X n)) ∧ QuasiIso i := by
  let e := ComplexShape.embeddingUpNat
  obtain ⟨L, i, hi, hL, hL0⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (A.extend e) 0
  have : QuasiIso i := hi
  have : L.IsStrictlySupported e := by
    constructor
    intro n hn
    apply CochainComplex.isZero_of_isStrictlyGE L 0 n (by
      by_contra h
      have hn0 : 0 ≤ n := by omega
      exact hn n.toNat (by simpa [e] using Int.toNat_of_nonneg hn0))
  let E := e.extendFunctor C
  let B := L.truncGE' e
  let j : A ⟶ B := E.preimage (i ≫ HomologicalComplex.πTruncGE L e)
  have hj : QuasiIso (HomologicalComplex.extendMap j e) := by
    change QuasiIso (E.map j)
    dsimp [j]
    rw [E.map_preimage]
    infer_instance
  refine ⟨B, j, ?_, (HomologicalComplex.quasiIso_extendMap_iff j e).1 hj⟩
  intro n
  have : Injective ((L.restriction e).X n) := hL (e.f n)
  have : IsIso ((L.restrictionToTruncGE' e).f n) := by infer_instance
  exact Injective.of_iso (asIso ((L.restrictionToTruncGE' e).f n)) inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the integer-indexed sections theorem through extension by zero.
The natural comparison `mapExtendFunctorNatIso` identifies application of sections
before and after extension, and `quasiIso_extendMap_iff` reflects the result.
Source: Stacks Project, Cohomology of Sheaves, Tags 01FB and 01EZ. -/
private theorem augmentedLift_sections_quasiIso
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : CochainComplex X.Modules ℕ) (K : CochainComplex Y.Modules ℕ)
    (hA : ∀ n : ℕ, Injective (A.X n))
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ⟶ K)
    (hl : QuasiIso l) :
    QuasiIso (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map l) := by
  let e := ComplexShape.embeddingUpNat
  let : ∀ n : ℕ, Injective (A.X n) := hA
  let : ∀ n : ℕ, Injective (K.X n) := hK
  have : QuasiIso l := hl
  let l' := (A.mapExtendIso e (pushforward h)).hom ≫ HomologicalComplex.extendMap l e
  have hl' : QuasiIso l' := by dsimp [l']; infer_instance
  obtain ⟨_, hΓ⟩ := quasiIso_globalSections_pushforward_injectives h
    (A.extend e) (K.extend e) (fun n ↦ inferInstance) (fun n ↦ inferInstance)
    (fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)
    (fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn) l' hl'
  let Γ := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  have : Γ.Additive := inferInstanceAs
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}).Additive
  have : Γ.PreservesZeroMorphisms := inferInstance
  have hΓ' : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map l') := hΓ
  have : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap l e)) := by
    have : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (A.mapExtendIso e (pushforward h)).hom ≫
          (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap l e)) := by
      rw [← Functor.map_comp]
      exact hΓ'
    exact quasiIso_of_comp_left
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (A.mapExtendIso e (pushforward h)).hom) _
  let P := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A
  have hext : QuasiIso (HomologicalComplex.extendMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map l) e) := by
    apply quasiIso_of_arrow_mk_iso
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap l e))
    exact Arrow.isoMk (P.mapExtendIso e Γ) (K.mapExtendIso e Γ)
      ((e.mapExtendFunctorNatIso Γ).hom.naturality l).symm
  exact (HomologicalComplex.quasiIso_extendMap_iff _ e).1 hext

/-- A fixed augmented lift computes the cohomology map without changing resolutions.
Source: Stacks Project, Cohomology, Tags 01FB and 01EZ.
(blueprint: lem-weil-pbc-module-cohomology-augmented-lift).

Proof: Extend h_*I by zero and resolve it by a quasi-isomorphism lambda into a
bounded below injective complex; truncate back to natural indices. Take beta
= k followed by lambda. The augmentation of k supplies the compatibility
field of ModuleCohomologyFMapData, with the given resolutions I and J and the
canonical section comparison a. Sections of lambda are a quasi-isomorphism
because I is termwise injective (Tag 01EZ); hence the invertibility field holds.
In the formula for the data's cohomology map expand beta, apply functoriality of
homology, and cancel the homology map of sections of lambda with its inverse.
The result is the displayed formula. Independence of resolution choices
identifies the data's map with moduleCohomologyFMap. -/
theorem moduleCohomologyFMap_of_augmentedLift {X Y : Scheme.{uBC}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (pushforward h).obj F)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (k : J.cocomplex ⟶
      ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hk : J.ι.f 0 ≫ k.f 0 = φ ≫ (pushforward h).map (I.ι.f 0))
    (a : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex ≅
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (Scheme.Modules.presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op)
    (p : ℕ) :
    letI := RingedSpace.globalSectionsFunctor_additive Y.toRingedSpace
    letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p
    let rG := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
      (J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) p) ≪≫
      (((RingedSpace.globalSectionsComplex J).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{uBC})).symm
    let rF := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p) ≪≫
      (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{uBC})).symm
    rG.hom ≫ H.map (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).map k) ≫
        (H.mapIso a).inv ≫ rF.inv = moduleCohomologyFMap h φ p := by
  let := RingedSpace.globalSectionsFunctor_additive Y.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let Γ := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{uBC}
  let ΓC := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
  obtain ⟨K, l, hK, hl⟩ := augmentedLift_injective_resolution
    (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  have hΓ : QuasiIso (ΓC.map l) :=
    augmentedLift_sections_quasiIso h I.cocomplex K (fun n ↦ inferInstance) hK l hl
  let D : ModuleCohomologyFMapData h G F φ := {
    I := I
    J := J
    K := K
    injective := hK
    lambda := l
    quasiIso := hl
    β := k ≫ l
    compatible := by
      change J.ι.f 0 ≫ k.f 0 ≫ l.f 0 = _
      rw [← Category.assoc, hk, Category.assoc]
    a := a
    sections := ha
    invertible := by
      intro q
      have : QuasiIso (ΓC.map l) := hΓ
      have : IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC}
          (ComplexShape.up ℕ) q).map (ΓC.map l)) := by
        change IsIso (HomologicalComplex.homologyMap _ q)
        infer_instance
      rw [Functor.map_comp]
      infer_instance }
  have hi := moduleCohomologyFMap_independent h φ D
    (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)) p
  change D.map p = moduleCohomologyFMap h φ p at hi
  rw [← hi]
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p
  have : QuasiIso (ΓC.map l) := hΓ
  have : IsIso (H.map (ΓC.map l)) := by
    change IsIso (HomologicalComplex.homologyMap _ p)
    infer_instance
  have hinv : inv a.hom = a.inv := IsIso.inv_eq_of_hom_inv_id a.hom_inv_id
  simp only [ModuleCohomologyFMapData.map, D, Functor.map_comp,
    IsIso.inv_comp, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
    IsIso.hom_inv_id_assoc, ← Functor.map_inv, hinv]


end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.RingHomExtensionDefs

/-! # Interfaces for augmented ring complexes and their ordered Čech models

Source: Stacks Project, algebraization.tex, Tag 099D, clauses (a)-(d).
The predicates below specify data and equations; they select no witnesses.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators TensorProduct ChangeOfRings

namespace AlgebraicGeometry
noncomputable section

/-- The ring, as a module sheaf on the one-object site. -/
abbrev ringComplexUnit (A : CommRingCat.{u}) : RingSiteModules A :=
  SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf.{u} A))

/-- The target of the augmentation of an extended Čech complex. -/
abbrev ringComplexSingle (A : CommRingCat.{u}) : CochainComplex (RingSiteModules A) ℤ :=
  (HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).obj (ringComplexUnit A)

/-- Degree-zero coordinate of an augmentation to the ring in degree zero. -/
abbrev ringComplexAugmentationValue {A : CommRingCat.{u}}
    {K : CochainComplex (RingSiteModules A) ℤ} (ε : K ⟶ ringComplexSingle A)
    (x : (K.X 0).val.obj (op ⟨PUnit.unit⟩)) : A :=
  (ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (ringComplexUnit A)).hom).val.app (op ⟨PUnit.unit⟩) x

/-- A family indexed by a ring and a finitely generated ideal. -/
abbrev RingComplexFamily := ∀ A : CommRingCat.{u}, {I : Ideal A // I.FG} →
  CochainComplex (RingSiteModules A) ℤ

/-- Augmentations for a ring-complex family. -/
abbrev RingComplexAugmentations (K : RingComplexFamily.{u}) :=
  ∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}), K A I ⟶ ringComplexSingle A

/-- Degreewise semilinear maps for extension of the ideal. -/
abbrev RingComplexMaps (K : RingComplexFamily.{u}) :=
  ∀ (A B : CommRingCat.{u}) (φ : A →+* B)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG}),
    I.val.map φ = J.val → ∀ n : ℤ,
      ((K A I).X n).val.obj (op ⟨PUnit.unit⟩) →ₛₗ[φ]
        ((K B J).X n).val.obj (op ⟨PUnit.unit⟩)

/-- The differential, augmentation, identity, and composition equations of Tag 099D. -/
def RingComplexFunctorial (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) : Prop :=
  (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (h : I.val.map φ = J.val) (n k : ℤ)
    (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
    m A B φ I J h k (((K A I).d n k).val.app (op ⟨PUnit.unit⟩) x) =
      ((K B J).d n k).val.app (op ⟨PUnit.unit⟩) (m A B φ I J h n x)) ∧
  (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (h : I.val.map φ = J.val) (x : ((K A I).X 0).val.obj (op ⟨PUnit.unit⟩)),
    ringComplexAugmentationValue (ε B J) (m A B φ I J h 0 x) =
      φ (ringComplexAugmentationValue (ε A I) x)) ∧
  (∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG})
    (h : I.val.map (RingHom.id A) = I.val) (n : ℤ)
    (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
    m A A (RingHom.id A) I I h n x = x) ∧
  (∀ (A B D : CommRingCat.{u}) (φ : A →+* B) (ψ : B →+* D)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (L : {L : Ideal D // L.FG}) (h : I.val.map φ = J.val)
    (h' : J.val.map ψ = L.val) (h'' : I.val.map (ψ.comp φ) = L.val)
    (n : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
    m B D ψ J L h' n (m A B φ I J h n x) = m A D (ψ.comp φ) I L h'' n x)

/-- The ordered localization complex for every finite generating list, with its
augmentation-compatible comparison in the derived category. This predicate includes
all coordinates and differentials, including the empty generating list.
Source: Stacks Project, Tag 099D(d).
(auxiliary; not a blueprint node). -/
def RingComplexHasCechModel (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)] (I : Ideal A)
    (K : CochainComplex (RingSiteModules A) ℤ) (ε : K ⟶ ringComplexSingle A) : Prop :=
  ∀ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = I →
        ∃ (C : CochainComplex (RingSiteModules A) ℤ)
          (a : C ⟶ (HomologicalComplex.single (RingSiteModules A) (ComplexShape.up ℤ) 0).obj
            (@id (RingSiteModules A)
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))))
          (e₀ : (C.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
          (e : ∀ q : ℕ, (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
            ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
          (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
            Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
              Localization.Away (∏ i, f (t i))),
          (∀ n : ℤ, n < 0 → IsZero (C.X n)) ∧
          (∀ (x : (C.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
            e 0 ((C.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
              algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ x)) ∧
          (∀ (q : ℕ) (x : (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
            (t : Fin (q + 2) ↪o Fin r),
            e (q + 1) ((C.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
              (op ⟨PUnit.unit⟩) x) t =
              ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
                l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) ∧
          (∀ x : (C.X 0).val.obj (op ⟨PUnit.unit⟩),
            (a.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))).hom).val.app
                    (op ⟨PUnit.unit⟩) x = e₀ x) ∧
          ∃ α : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj K,
            α.hom ≫ DerivedCategory.Q.map ε = DerivedCategory.Q.map a

/-- Transport an augmented ordered localization model backwards across a quasi-isomorphism.
The augmentation equation is retained, rather than only the underlying derived object. -/
theorem ringComplexHasCechModel_of_quasiIso {A : CommRingCat.{u}}
    [HasDerivedCategory.{w} (RingSiteModules A)] {I : Ideal A}
    {K P : CochainComplex (RingSiteModules A) ℤ} (ε : K ⟶ ringComplexSingle A)
    (p : P ⟶ K) (hp : QuasiIso p) (hK : RingComplexHasCechModel A I K ε) :
    RingComplexHasCechModel A I P (p ≫ ε) := by
  intro r f hf
  obtain ⟨C, a, e₀, e, l, hneg, hd₀, hd, ha, α, hα⟩ := hK r f hf
  let : QuasiIso p := hp
  refine ⟨C, a, e₀, e, l, hneg, hd₀, hd, ha,
    α ≪≫ (asIso (DerivedCategory.Q.map p)).symm, ?_⟩
  simpa only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.map_comp,
    Category.assoc, IsIso.inv_hom_id_assoc] using hα

end

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology

/-! # The section-preserving base of strict ell-power coordinates

Source: Zheng Construction 4.1; the coefficient-tower construction in the
smooth-purity blueprint, and Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private def sliceCondition {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ RingCat.{r}) :
    ObjectProperty (PresheafOfModules.{r} P) :=
  fun M ↦ ∀ n : ℕ, Presheaf.IsSheaf J ((Prod.sectR n C).op ⋙ M.presheaf)

private def rebundle {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    (Q : Sheaf (verticalDiagramSiteTopology ℕ C J) RingCat.{r}) :
    (sliceCondition J Q.obj).FullSubcategory ≌ SheafOfModules.{r} Q where
  functor :=
    { obj := fun M ↦ ⟨M.obj, (verticalDiagramSite_isSheaf_iff ℕ C J _).2 M.property⟩
      map := fun f ↦ ⟨f.hom⟩ }
  inverse :=
    { obj := fun M ↦ ⟨M.val, (verticalDiagramSite_isSheaf_iff ℕ C J _).1 M.isSheaf⟩
      map := fun f ↦ ObjectProperty.homMk f.val }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def rebaseRebundle {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ RingCat.{r})
    (Q : Sheaf (verticalDiagramSiteTopology ℕ C J) RingCat.{r}) (h : P = Q.obj) :
    (sliceCondition J P).FullSubcategory ≌ SheafOfModules.{r} Q := by
  subst P
  exact rebundle J Q

private theorem rebaseRebundle_sections {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ RingCat.{r})
    (Q : Sheaf (verticalDiagramSiteTopology ℕ C J) RingCat.{r}) (h : P = Q.obj)
    (M : (sliceCondition J P).FullSubcategory) (U : (ℕ × C)ᵒᵖ) :
    HEq (((rebaseRebundle J P Q h).functor.obj M).val.obj U) (M.obj.obj U) := by
  subst P
  rfl

private theorem rebaseRebundle_restrictions {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ RingCat.{r})
    (Q : Sheaf (verticalDiagramSiteTopology ℕ C J) RingCat.{r}) (h : P = Q.obj)
    (M : (sliceCondition J P).FullSubcategory) {U V : (ℕ × C)ᵒᵖ} (a : U ⟶ V) :
    HEq (((rebaseRebundle J P Q h).functor.obj M).val.map a) (M.obj.map a) := by
  subst P
  rfl

private theorem rebaseRebundle_morphisms {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ RingCat.{r})
    (Q : Sheaf (verticalDiagramSiteTopology ℕ C J) RingCat.{r}) (h : P = Q.obj)
    {M N : (sliceCondition J P).FullSubcategory} (a : M ⟶ N) (U : (ℕ × C)ᵒᵖ) :
    HEq (((rebaseRebundle J P Q h).functor.map a).val.app U) (a.hom.app U) := by
  subst P
  rfl

private theorem rebaseRebundle_additive {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ RingCat.{r})
    (Q : Sheaf (verticalDiagramSiteTopology ℕ C J) RingCat.{r}) (h : P = Q.obj) :
    (rebaseRebundle J P Q h).functor.Additive := by
  subst P
  refine { map_add := ?_ }
  intro X Y f g
  rfl

private theorem opSequence_comp {C : Type c} [Category.{v} C]
    {C' : Type r} [Category C'] {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n)
    (G : C ⥤ C') :
    Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) =
      Functor.ofOpSequence f ⋙ G := by
  let a : Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) ⟶
      Functor.ofOpSequence f ⋙ G := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 (G.obj (X n))) ?_
    intro n
    simp only [Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map]
    exact (Category.comp_id (G.map (f n))).trans (Category.id_comp (G.map (f n))).symm
  let e : Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) ≅
      Functor.ofOpSequence f ⋙ G :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ a.naturality f)
  exact Functor.ext_of_iso e (fun _ ↦ rfl) (fun _ ↦ rfl)

private theorem opSequence_reconstruct {C : Type c} [Category.{v} C]
    (F : ℕᵒᵖ ⥤ C) :
    Functor.ofOpSequence (X := fun n ↦ F.obj (op n))
      (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op) = F := by
  let a : Functor.ofOpSequence (X := fun n ↦ F.obj (op n))
      (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op) ⟶ F := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 (F.obj (op n))) ?_
    intro n
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  let e : Functor.ofOpSequence (X := fun n ↦ F.obj (op n))
      (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op) ≅ F :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ a.naturality f)
  exact Functor.ext_of_iso e (fun _ ↦ rfl) (fun _ ↦ rfl)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem actualRing_eq (T : Scheme.{u}) :
    spCoefficientPresheaf l E T =
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (SemilinearSections.systemRing.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (B l E T) (tau l E T))).obj := by
  have hr : SemilinearSections.rings.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T) = spCoefficientCommRings l E T :=
    opSequence_reconstruct _
  have hs : spCoefficientRings l E T = spCoefficientCommRings l E T ⋙
      sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat) := by
    unfold spCoefficientRings spCoefficientReduction spCoefficientCommRings
    exact opSequence_comp _ _
  change spCoefficientPresheaf l E T =
    SemilinearSections.ringPresheaf.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T) ⋙ forget₂ CommRingCat RingCat
  unfold spCoefficientPresheaf SemilinearSections.ringPresheaf
  rw [hr, hs]
  rfl

private theorem ramification_factor :
    ∃ e : ℕ, 0 < e ∧ ∃ v : (Padic.coefficientExtensionIntegers l E)ˣ,
      (l : Padic.coefficientExtensionIntegers l E) =
        v * Padic.coefficientExtensionUniformizer l E ^ e := by
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  change ∃ e : ℕ, 0 < e ∧ ∃ v : Oˣ, (l : O) = v * π ^ e
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 (hm.symm.trans hgen.symm)
  have hl0 : (l : O) ≠ 0 := by
    intro heq
    have heq' : (l : E) = 0 := congrArg (fun x : O ↦ (x : E)) heq
    have hq : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    exact hq ((algebraMap ℚ_[l] E).injective (by
      simpa only [map_natCast, map_zero] using heq'))
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
  refine ⟨e, ?_, v, hv⟩
  have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    have hext := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change spectralNorm ℚ_[l] E (l : E) < 1
    simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
  have hnu : ¬ IsUnit (l : O) := by
    intro hu
    exact (ne_of_lt hval) ((h.2.2.1 (l : O)).mp hu)
  by_contra he
  have he0 : e = 0 := by omega
  apply hnu
  rw [hv, he0, pow_zero, mul_one]
  exact v.isUnit

/-- The actual ell-power tower has a section-preserving sequence-site base whose
calculus is the systems field of semilinear derived sections at every scheme.
Source: Zheng Construction 4.1; blueprint operations proof (2), coefficient
presentation step; Stacks 07A4.
(blueprint: lem-sp-strict-base-coordinates).

Proof: factor ell by the irreducible specified uniformizer in the integer DVR.
Its absolute value is less than one, so its exponent is positive. Taking powers
of the principal-ideal equality identifies the actual quotient ideals; finiteness
follows from the finite uniformizer quotients. The coefficient ring presheaves
are equal, since forming the inverse sequence commutes with forgetting
commutativity. The vertical sheaf condition is exactly the levelwise condition.
Rebundle the same module presheaves, with identity unit, counit and all maps.
Finally retain the systems field and Grothendieck structure of semilinear
derived sections. No new choice of tensor or of section carriers is made. -/
theorem strictBaseCoordinates :
    ∃ b : Base l E, ∀ T : Scheme.{u},
      ∃ s : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (B l E T) (tau l E T),
        s.systems = b.calculus T := by
  obtain ⟨e, he, v, hv⟩ := ramification_factor l E
  have hi (n : ℕ) : spEllIdeal l E ^ (n + 1) =
      Padic.coefficientExtensionIdeal l E (e * (n + 1)) := by
    unfold spEllIdeal Padic.coefficientExtensionIdeal
    rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow,
      ← pow_mul]
    rw [Ideal.span_singleton_pow]
  have hf (n : ℕ) : Finite (R l E n) := by
    unfold R
    rw [hi n]
    exact Padic.finite_coefficientExtensionRing l E _ (Nat.mul_pos he (Nat.succ_pos n))
  let s (T : Scheme.{u}) :=
    (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T)).some
  let q (T : Scheme.{u}) := SemilinearSections.ring.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (SemilinearSections.systemRing.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T))
  let a (T : Scheme.{u}) : spCoefficientTowers l E T ≌ S l E T :=
    rebaseRebundle (Scheme.ProEt.topology T) (spCoefficientPresheaf l E T)
      (q T) (actualRing_eq l E T)
  let b : Base l E := {
    ramification := e
    ramification_positive := he
    ramificationUnit := v
    ramification_eq := hv
    ideals := hi
    finite := hf
    realization := a
    realizationAdditive := fun T ↦ rebaseRebundle_additive
      (Scheme.ProEt.topology T) (spCoefficientPresheaf l E T) (q T) (actualRing_eq l E T)
    sections := fun T M n U ↦ rebaseRebundle_sections
      (Scheme.ProEt.topology T) (spCoefficientPresheaf l E T) (q T)
      (actualRing_eq l E T) M (op (n, U.unop))
    restrictions := fun T M _ _ f ↦ rebaseRebundle_restrictions
      (Scheme.ProEt.topology T) (spCoefficientPresheaf l E T) (q T)
      (actualRing_eq l E T) M f
    morphisms := fun T _ _ f U ↦ rebaseRebundle_morphisms
      (Scheme.ProEt.topology T) (spCoefficientPresheaf l E T) (q T)
      (actualRing_eq l E T) f U
    calculus := fun T ↦ (s T).systems
    tensorNormalization := fun T ↦ (s T).tensorNormalization
    kinjective := fun T ↦ by
      let := (s T).systems.grothendieck
      infer_instance }
  exact ⟨b, fun T ↦ ⟨s T, rfl⟩⟩

end AlgebraicGeometry.ProEtale.SpTowerShriek

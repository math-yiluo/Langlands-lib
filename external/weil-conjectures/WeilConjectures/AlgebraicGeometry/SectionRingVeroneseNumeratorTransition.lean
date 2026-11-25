/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionMap
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import all WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import all WeilConjectures.AlgebraicGeometry.FractionZeroTensorPower
import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation

/-! # Compatibility of Veronese numerators with tensor-power transitions

Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- Regrouping tensor powers preserves their concatenation.
Source: Stacks Project, Properties, Tag 0B5L, equation module-invert-s and
Lemma 01PW(2).

Proof: induct on n. At zero, tensorPowMulIso is the exponent-zero identification
and tensorPowAddIso is the left unitor, so naturality of the left unitor gives the
identity. At n+1, expand tensorPowMulIso and tensorPowAddIso. Naturality of the
associator moves the two regrouping maps through it. Apply the inductive identity
to the remaining n blocks, and then associativity of tensorPowAddIso for the three
exponents d, d*n, d*b. This associativity is itself proved by induction on its first
exponent, using the left unitor at zero and the monoidal pentagon at the successor.
All exponent transports agree by proof irrelevance and multiplication distributing
over addition. Neither symmetry nor an invertibility assumption is needed. Thus
this includes d=0, n=0 and b=0.
-/
private theorem tensorPowMulIso_add_inv
    {X : Scheme.{u}} (L : X.Modules) (d n b : ℕ) :
    ((L.tensorPowMulIso d n).inv ⊗ₘ (L.tensorPowMulIso d b).inv) ≫
        (L.tensorPowAddIso (d * n) (d * b)).inv ≫
        eqToHom (congrArg L.tensorPow (Nat.mul_add d n b).symm) =
      ((L.tensorPow d).tensorPowAddIso n b).inv ≫
        (L.tensorPowMulIso d (n + b)).inv := by
  induction n with
  | zero =>
    simp only [tensorPowMulIso, tensorPowAddIso, Iso.trans_inv, Iso.symm_inv,
      eqToIso.inv, Nat.mul_zero, eqToHom_refl, id_tensorHom, Category.assoc, tensorPow_zero]
    rw [← eqToHom_iso_inv_naturality (fun k ↦ L.tensorPowMulIso d k)
      (Nat.zero_add b).symm]
    simp only [eqToHom_trans]
    rw [leftUnitor_naturality_assoc]
  | succ n ih =>
    have ih' :
        ((L.tensorPowMulIso d n).inv ⊗ₘ (L.tensorPowMulIso d b).inv) ≫
          (L.tensorPowAddIso (d * n) (d * b)).inv =
        ((L.tensorPow d).tensorPowAddIso n b).inv ≫
          (L.tensorPowMulIso d (n + b)).inv ≫
          eqToHom (congrArg L.tensorPow (Nat.mul_add d n b)) := by
      rw [← Category.assoc, ← ih]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, tensorPow_succ, Category.assoc]
    rw [← eqToHom_iso_inv_naturality (fun k ↦ L.tensorPowMulIso d k)
      (Nat.succ_add n b).symm]
    simp only [tensorPowMulIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
      eqToIso.inv, tensorPow_succ]
    simp only [tensorHom_def', comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
    rw [← eqToHom_iso_inv_naturality_assoc
      (fun k ↦ L.tensorPowAddIso k (d * b)) (by ring : d + d * n = d * (n + 1))]
    simp only [id_whiskerRight, Category.id_comp]
    rw [reassoc_of% tensorPowAddIso_assoc_inv L d (d * n) (d * b),
      associator_naturality_middle_assoc,
      associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← tensorHom_def', ← whiskerLeft_comp_assoc, ih']
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom]
    rw [← eqToHom_iso_inv_naturality_assoc
      (fun k ↦ L.tensorPowAddIso d k) (Nat.mul_add d n b)]
    simp only [eqToHom_trans]

private theorem numerator_eq (X : Scheme.{u}) (L : X.Modules) (d n : ℕ)
    (t : Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (sectionRingVeroneseNumerator X L d n t).val =
      DirectSum.of (SectionRingComponent L) (d * n)
        ((L.tensorPowMulIso d n).inv.app ⊤
          ((λ_ ((L.tensorPow d).tensorPow n)).hom.app ⊤ t)) := by
  change DirectSum.of (SectionRingComponent L) (n • d)
    ((sectionRingVeroneseNumeratorIso X L d n).inv.app ⊤ t) = _
  simp only [sectionRingVeroneseNumeratorIso, Iso.trans_inv, Iso.symm_inv,
    eqToIso.inv, Hom.comp_app, ConcreteCategory.comp_apply]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (Nat.mul_comm n d)
  exact eqToHom_app_heq _ _

private theorem transition_unitor {X : Scheme.{u}} {M : X.Modules}
    (s : 𝟙_ X.Modules ⟶ M) (n b : ℕ)
    (t : Γ((𝟙_ X.Modules) ⊗ M.tensorPow n, ⊤)) :
    (λ_ (M.tensorPow (n + b))).hom.app ⊤
        ((mulTensorPowSection s (𝟙_ X.Modules) n b).app ⊤ t) =
      (M.tensorPowAddIso n b).inv.app ⊤
        (tmulSection ((λ_ (M.tensorPow n)).hom.app ⊤ t)
          (tensorPowSectionOne s b ⊤)) := by
  have ht : t = tmulSection (unitSectionsEquiv ⊤ 1)
      ((λ_ (M.tensorPow n)).hom.app ⊤ t) := by
    rw [← leftUnitor_inv_app, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
      Iso.hom_inv_id, Hom.id_app]
    rfl
  rw [ht, mulTensorPowSection_app, associator_hom_app_tmulSection,
    whiskerLeft_app_tmulSection, leftUnitor_hom_app_tmulSection,
    leftUnitor_hom_app_tmulSection, one_smul, one_smul]

-- Comparing the degree-one tensor regroupings needs additional definitional reductions.
/-- Transporting a tensor-power transition to the section ring multiplies the numerator
by the corresponding power of the homogeneous section.
Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
(blueprint: lem-sc-section-ring-veronese-numerator-transition)

Proof: cover X by opens on which L has a free generator e. Its tensor powers have generators
obtained by repeatedly tensoring e, with the zeroth generator the unit section. Induction on
the exponent in tensorPowAddIso and tensorPowMulIso shows that these isomorphisms send the
respective tensor products of these generators to the generator of the total tensor exponent;
the left unitor deletes the unit generator. Thus the inverse numerator isomorphism sends a
numerator with coefficient f to the same coefficient f in degree n*d. Write s locally as
c times the degree-d generator. The morphism homOfGlobalSection sends 1 to this section;
its b-th tensor power sends 1 to c^b times the degree-b*d generator. The definition of
mulTensorPowSection therefore sends the numerator with coefficient f to the numerator with
coefficient f*c^b. By the definition of graded multiplication, multiplying its ring numerator
by s^b has that same coefficient in degree (n+b)*d. Naturality of all the isomorphisms and
of tensor sections identifies these calculations with restrictions of the two global ring
numerators. The sheaf separatedness axiom glues their equality. The calculation includes
n=0, b=0, d=0, and zero coefficients, without dividing by c or assuming s nonzero.
-/
theorem sectionRingVeroneseNumerator_transition
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (n b : ℕ)
    (t : Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (sectionRingVeroneseNumerator X L d (n + b)
      ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
        (𝟙_ X.Modules) n b).app ⊤ t)).val =
      (sectionRingVeroneseNumerator X L d n t).val * s.val ^ b := by
  have hone (k : ℕ)
      (a : Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow k, ⊤)) :
      (sectionRingVeroneseNumerator X L d (k + 1)
        ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
          (𝟙_ X.Modules) k 1).app ⊤ a)).val =
        (sectionRingVeroneseNumerator X L d k a).val * s.val := by
    rw [numerator_eq, transition_unitor, numerator_eq]
    obtain ⟨v, hv⟩ := s.property
    have hs : s.val d = v := by
      rw [← hv, DirectSum.of_eq_same]
    rw [hs, ← hv]
    have hp : DirectSum.of (SectionRingComponent L) d v =
        DirectSum.of (SectionRingComponent L) (d * 1)
          ((L.tensorPowMulIso d 1).inv.app ⊤
            (tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) v) 1 ⊤)) := by
      simp only [tensorPowMulIso, Iso.trans_inv, MonoidalCategory.tensorIso_inv,
        Iso.refl_inv, tensorPowSectionOne_succ, Hom.comp_app,
        ConcreteCategory.comp_apply, eqToIso.inv, tensorPowSectionOne_zero]
      have ht : (homOfGlobalSection (L.tensorPow d) v).app ⊤
          (unitSectionsEquiv ⊤ 1) = v := by
        change (homOfGlobalSection (L.tensorPow d) v).app ⊤ (1 : Γ(X, ⊤)) = v
        rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
      simp only [Nat.mul_zero, eqToHom_refl, tensorHom_id, tensorPowAddIso_zero_inv,
        id_whiskerRight]
      dsimp only [tensorPow_zero]
      erw [Hom.id_app, ConcreteCategory.id_apply, ht,
        rightUnitor_hom_app_tmulSection, one_smul]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      apply Sigma.ext (Nat.mul_one d).symm
      exact (eqToHom_app_heq _ _).symm
    conv_rhs => rw [hp, DirectSum.of_mul_of]
    have h := congrArg
      (fun f ↦ f.app ⊤
        (tmulSection ((λ_ ((L.tensorPow d).tensorPow k)).hom.app ⊤ a)
          (tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) v) 1 ⊤)))
      (tensorPowMulIso_add_inv L d k 1)
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection] at h
    conv_lhs => rw [← h]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext (Nat.mul_add d k 1)
    exact eqToHom_app_heq _ _
  induction b with
  | zero =>
    rw [mulTensorPowSection_zero, Hom.id_app]
    simp
  | succ b ih =>
    have hc := mulTensorPowSection_comp
      (homOfGlobalSection (L.tensorPow d) (s.val d)) (𝟙_ X.Modules) n b 1
    simp only [eqToHom_refl, Category.comp_id] at hc
    rw [← hc, Hom.comp_app, ConcreteCategory.comp_apply]
    erw [hone, ih]
    rw [pow_succ, mul_assoc]

end AlgebraicGeometry.Scheme.Modules

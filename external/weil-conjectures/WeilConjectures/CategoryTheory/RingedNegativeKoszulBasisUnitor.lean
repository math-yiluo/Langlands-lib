/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ExteriorKoszulBasisDifferential
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel

/-! # Normalization of a negative pure tensor by the left unitor

Source: Stacks Project, More on Algebra, Tag 0664; Algebraization, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory

attribute [local irreducible] ringedKoszulScalar ringedNegativeKoszulFactor
  ringedNegativeKoszulBasis ringedNegativeKoszul

private theorem unit_basis_tensor
    {E : Type*} [Category E] [Preadditive E] [HasZeroObject E] [HasCountableCoproducts E]
    [MonoidalCategory E] [SymmetricCategory E] [MonoidalPreadditive E] [MonoidalClosed E]
    (N : CochainComplex E ℤ) (p q : ℤ) (hp : p = 0)
    (β : MonoidalCategory.tensorUnit E ⟶ N.X q) :
    β ≫ (HomologicalComplex.leftUnitor N).inv.f q =
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
        (MonoidalCategory.tensorUnit E) p hp).inv ≫
      (MonoidalCategory.rightUnitor ((HomologicalComplex.tensorUnit E (.up ℤ)).X p)).inv ≫
      MonoidalCategory.tensorHom (𝟙 _) β ≫
      CochainComplex.ιMapBifunctor (HomologicalComplex.tensorUnit E (.up ℤ)) N
        (MonoidalCategory.curriedTensor E) p q q (by omega) := by
  subst p
  have hl : (HomologicalComplex.leftUnitor N).inv.f q =
      (MonoidalCategory.leftUnitor (N.X q)).inv ≫
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (MonoidalCategory.tensorUnit E)).inv ▷ N.X q) ≫
        CochainComplex.ιMapBifunctor (HomologicalComplex.tensorUnit E (.up ℤ)) N
          (MonoidalCategory.curriedTensor E) 0 q q (zero_add q) :=
    HomologicalComplex.leftUnitor'_inv N q
  symm
  rw [hl]
  simp only [MonoidalCategory.id_tensorHom]
  rw [MonoidalCategory.rightUnitor_inv_naturality_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.leftUnitor_inv_naturality_assoc,
    MonoidalCategory.unitors_inv_equal]
  rfl

/-- The left unitor takes a canonical supported negative tensor to its specified
pure-tensor summand for the coefficient complex O[0].

Source: Stacks Project, More on Algebra, Tag 0664, tensoring finite Koszul factors;
Algebraization, Tag 0A0E, lemma-derived-completion-koszul, pure tensor normalization.
(auxiliary; not a blueprint node).

Proof: in a monoidal category apply leftUnitor'_inv to a map beta from the unit.
Naturality of the right unitor, the interchange law, and naturality of the left
unitor move beta through the two unit maps. The inverse left and right unitors
of the unit agree. This proves the displayed pure-tensor identity in coefficient
degree zero. For a supported subset, q=-card I and q+card I=0. Substitute this
relation and apply that identity to the specified negative basis vector. The
right-hand side is exactly the definition of ringedNegativeKoszulSummand with
coefficient complex O[0], including its equality transport. The calculation uses
no scalar property and includes the empty subset and empty tensor. -/
theorem ringedNegativeKoszulBasis_leftUnitor
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin r → A) (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :
    letI := SheafOfModules.isGrothendieckAbelian
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let M := SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
    let N := ringedNegativeKoszul O r
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) n
    ringedNegativeKoszulBasis O r
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) n I.1 q ≫
        (HomologicalComplex.leftUnitor N).inv.f q =
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M (q + I.1.card)
        (by have _hI := I.2; omega)).inv ≫
          ringedNegativeKoszulSummand O ρ a n (ringedSiteRingComplex O) q I.1 := by
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let M := SheafOfModules.unit
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
  let N := ringedNegativeKoszul O r
    (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) n
  rcases I with ⟨I, hq⟩
  change q = -(I.card : ℤ) at hq
  subst q
  have hc : -(I.card : ℤ) + I.card = 0 := by omega
  exact unit_basis_tensor N (-(I.card : ℤ) + I.card) (-(I.card : ℤ)) hc
    (ringedNegativeKoszulBasis O r
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) n I (-(I.card : ℤ)))

end CategoryTheory

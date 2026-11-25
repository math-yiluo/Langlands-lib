/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulBasisCoproduct

/-!
# Assembly of degreewise basis coproducts through the total tensor

This isolates the total-complex tensor universal property from the recursive basis
calculation.  It is the second step of the finite free calculation in Stacks Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- If every degree of the negative Koszul complex is presented by its supported pure
basis, then the total tensor with an arbitrary coefficient complex has the corresponding
subset cofan.  This is only the assembly step: it does not prove the recursive basis
presentation.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
Proof: apply the coproduct universal property of the total tensor degreewise, then apply
tensor preservation to each basis cofan and reindex pairs `(p,n)` with `p+n=q` by the
subset cardinality.  The inverse right unitor identifies each resulting leg with
`ringedNegativeKoszulSummand`; the uniqueness part of the iterated coproducts gives the
cofan universal property.  No differential or boundedness assertion is involved.
(auxiliary; not a blueprint node).
-/
theorem isColimit_ringedNegativeKoszulTensor_of_basis
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
    (h : ∀ n : ℤ, Nonempty (IsColimit (Cofan.mk
      ((ringedNegativeKoszul O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m).X n)
      (fun I : {I : Finset (Fin (r + 1)) // n = -(I.card : ℤ)} ↦
        ringedNegativeKoszulBasis O (r + 1)
          (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I.1 n)))) :
    Nonempty (IsColimit (Cofan.mk
      (((ringedNegativeKoszulTensor O ρ a m).obj K).X q)
      (ringedNegativeKoszulSummand O ρ a m K q))) := by
  classical
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let Q := ringedNegativeKoszul O (r + 1)
    (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m
  let B (n : ℤ) (I : {I : Finset (Fin (r + 1)) // n = -(I.card : ℤ)}) :=
    ringedNegativeKoszulBasis O (r + 1)
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I.1 n
  let hc (p n : ℤ) :=
    Cofan.isColimitMapCoconeEquiv (MonoidalCategory.tensorLeft (K.X p)) _
      (Cofan.mk (Q.X n) (B n))
      (isColimitOfPreserves (MonoidalCategory.tensorLeft (K.X p)) (h n).some)
  let d (s : Cofan (fun I : Finset (Fin (r + 1)) ↦ K.X (q + I.card)))
      (p n : ℤ) (hpq : p + n = q) :=
    (hc p n).desc (Cofan.mk s.pt (fun I ↦
      (MonoidalCategory.rightUnitor (K.X p)).hom ≫
        (K.XIsoOfEq (show p = q + (I.1.card : ℤ) by
          have := I.2
          omega)).hom ≫ s.inj I.1))
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦
    HomologicalComplex.mapBifunctorDesc (K₁ := K) (K₂ := Q)
      (F := MonoidalCategory.curriedTensor _) (c := ComplexShape.up ℤ)
      (fun p n hpq ↦ d s p n hpq)) ?_ ?_⟩
  · intro s I
    change (MonoidalCategory.rightUnitor _).inv ≫
      MonoidalCategory.tensorHom (𝟙 _) (B (-(I.card : ℤ)) ⟨I, rfl⟩) ≫
        HomologicalComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
          (ComplexShape.up ℤ) _ _ q _ ≫ _ = _
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    have hf := (hc (q + I.card) (-(I.card : ℤ))).fac
      (Cofan.mk s.pt (fun L ↦
        (MonoidalCategory.rightUnitor (K.X (q + I.card))).hom ≫
          (K.XIsoOfEq (show q + (I.card : ℤ) = q + (L.1.card : ℤ) by
            have := L.2
            omega)).hom ≫ s.inj L.1)) ⟨⟨I, rfl⟩⟩
    simpa [d, MonoidalCategory.tensorLeft, Category.assoc] using
      congrArg ((MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫ ·) hf
  · intro s f hf
    apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := K) (K₂ := Q)
      (F := MonoidalCategory.curriedTensor _) (c := ComplexShape.up ℤ)
    intro p n hpq
    change p + n = q at hpq
    apply (hc p n).hom_ext
    rintro ⟨I, hI⟩
    have hp : p = q + (I.card : ℤ) := by omega
    subst p
    subst n
    have hfac := (hc (q + I.card) (-(I.card : ℤ))).fac
      (Cofan.mk s.pt (fun L ↦
        (MonoidalCategory.rightUnitor (K.X (q + I.card))).hom ≫
          (K.XIsoOfEq (show q + (I.card : ℤ) = q + (L.1.card : ℤ) by
            have := L.2
            omega)).hom ≫ s.inj L.1)) ⟨⟨I, rfl⟩⟩
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    have hi := hf I
    change (MonoidalCategory.rightUnitor _).inv ≫
      MonoidalCategory.tensorHom (𝟙 _) (B (-(I.card : ℤ)) ⟨I, rfl⟩) ≫
        HomologicalComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
          (ComplexShape.up ℤ) _ _ q _ ≫ f = s.inj I at hi
    simpa only [d, MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor_obj_map,
      MonoidalCategory.curriedTensor_obj_obj, Category.assoc,
      Cofan.mk_ι_app, cofan_mk_inj, Discrete.functor_obj,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, MonoidalCategory.id_tensorHom, Iso.hom_inv_id_assoc] using
      (congrArg ((MonoidalCategory.rightUnitor (K.X (q + I.card))).hom ≫ ·) hi).trans
        (by simpa [d, MonoidalCategory.tensorLeft, Category.assoc] using hfac.symm)

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergRows

/-! # Homology of the complex assembled from alternating exact rows

Source: Stacks Project, Derived Categories, Lemma 015I, proof conclusion
(blueprint: lem-sp-cartan-eilenberg-rows-identifications).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

attribute [local instance] strongEpi_of_epi

private noncomputable def rowHomologyData
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : CochainComplex C ℤ} (R : CartanEilenbergRows S) (p : ℤ) :
    (R.complex.sc' (p - 1) p (p + 1)).LeftHomologyData := by
  have : Mono (R.u p) := (R.exact₁ p).mono_f
  have : Mono (R.w (p + 1)) := (R.exact₂ (p + 1)).mono_f
  have : Mono (R.u (p + 1)) := (R.exact₁ (p + 1)).mono_f
  have huv : R.u p ≫ (R.complex.sc' (p - 1) p (p + 1)).g = 0 := by
    change R.u p ≫ R.complex.d p (p + 1) = 0
    simp [reassoc_of% (R.uv p)]
  let hi : IsLimit (KernelFork.ofι (R.u p) huv) :=
    KernelFork.IsLimit.ofι _ _
      (fun k hk ↦ (R.exact₁ p).fIsKernel.lift (KernelFork.ofι k (by
        apply (cancel_mono (R.w (p + 1) ≫ R.u (p + 1))).1
        simpa [Category.assoc] using hk)))
      (fun k hk ↦ (R.exact₁ p).fIsKernel.fac _ WalkingParallelPair.zero)
      (fun k hk b hb ↦ by
        apply (cancel_mono (R.u p)).1
        apply hb.trans
        symm
        exact (R.exact₁ p).fIsKernel.fac _ WalkingParallelPair.zero)
  let r : R.A (p - 1) ⟶ R.D p :=
    R.v (p - 1) ≫ eqToHom (congrArg R.D (show p - 1 + 1 = p by omega))
  have : Epi (R.v (p - 1)) := (R.exact₁ (p - 1)).epi_g
  have : Epi r := by dsimp [r]; infer_instance
  have hr : r ≫ R.w p ≫ R.u p = (R.complex.sc' (p - 1) p (p + 1)).f := by
    change _ = R.complex.d (p - 1) p
    simp [CartanEilenbergRows.complex, r, show p - 1 + 1 = p by omega]
  have hlift : hi.lift (KernelFork.ofι _ (R.complex.sc' (p - 1) p (p + 1)).zero) = r ≫ R.w p := by
    apply (cancel_mono (R.u p)).1
    calc
      _ = (R.complex.sc' (p - 1) p (p + 1)).f :=
        hi.fac _ WalkingParallelPair.zero
      _ = _ := by simpa only [Category.assoc] using hr.symm
  have hwπ : hi.lift (KernelFork.ofι _ (R.complex.sc' (p - 1) p (p + 1)).zero) ≫ R.x p = 0 := by
    rw [hlift, Category.assoc, R.wx p, comp_zero]
  let hπ : IsColimit (CokernelCofork.ofπ (R.x p) hwπ) :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun k hk ↦ (R.exact₂ p).gIsCokernel.desc (CokernelCofork.ofπ k (by
        apply (cancel_epi r).1
        rw [← Category.assoc, ← hlift]
        simpa only [comp_zero] using hk)))
      (fun k hk ↦ (R.exact₂ p).gIsCokernel.fac _ WalkingParallelPair.one)
      (fun k hk b hb ↦ by
        have : Epi (R.x p) := (R.exact₂ p).epi_g
        apply (cancel_epi (R.x p)).1
        apply hb.trans
        symm
        exact (R.exact₂ p).gIsCokernel.fac _ WalkingParallelPair.one)
  exact
    { K := R.Z p
      H := R.H p
      i := R.u p
      π := R.x p
      wi := huv
      hi := hi
      wπ := hwπ
      hπ := hπ }

/-- The row objects identify the cycles, boundaries and homology of the assembled
complex, compatibly with its augmentation. No injectivity or resolution hypothesis
is used: this is a statement about short exact diagrams in any abelian category.

Source: Stacks Project, Derived Categories, Lemma 015I, proof conclusion
(blueprint: lem-sp-cartan-eilenberg-rows-identifications).

Proof:
1. The composite D^(p+1) -> Z^(p+1) -> A^(p+1) is monic. Since
   Z^p -> A^p -> D^(p+1) is short exact, Z^p is a kernel of the horizontal
   differential. Kernel uniqueness gives an isomorphism from the cycles to Z^p,
   whose composite with u^p is the canonical cycle inclusion.
2. A^(p-1) -> D^p is epic. Its composite with the monomorphism
   D^p -> Z^p -> A^p is the horizontal differential. The epi-mono image
   factorization gives an isomorphism from its image to D^p, whose composite
   with w^p u^p is the image inclusion.
3. Transport the boundary-to-cycle map along the preceding isomorphisms.
   It becomes w^p. The second short exact row makes H^p its cokernel, so
   cokernel uniqueness gives the homology isomorphism, intertwining the
   canonical homology projection with x^p.
4. Naturality of cycle and image inclusions, together with commZ and commD,
   shows that their induced augmentations followed by these isomorphisms equal
   jZ and jD (cancel the monic inclusions). Naturality of the homology projection
   and commH gives the last equality (cancel its epimorphic source projection).
   These arguments also apply to zero columns and to degree zero. -/
theorem cartanEilenberg_rows_identifications
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : CochainComplex C ℤ} (R : CartanEilenbergRows S) :
    ∃ (z : ∀ p : ℤ, R.complex.cycles p ≅ R.Z p)
      (d : ∀ p : ℤ, image (R.complex.d (p - 1) p) ≅ R.D p)
      (h : ∀ p : ℤ, R.complex.homology p ≅ R.H p),
      (∀ p : ℤ, HomologicalComplex.cyclesMap R.augmentation p ≫ (z p).hom = R.jZ p) ∧
      (∀ p : ℤ, image.map (Arrow.homMk' (R.augmentation.f (p - 1))
        (R.augmentation.f p) (R.augmentation.comm (p - 1) p)) ≫ (d p).hom = R.jD p) ∧
      (∀ p : ℤ, HomologicalComplex.homologyMap R.augmentation p ≫ (h p).hom = R.jH p) :=
  by
    have hp (p : ℤ) : (ComplexShape.up ℤ).prev p = p - 1 :=
      ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (p - 1) p by
        change p - 1 + 1 = p
        omega)
    have hn (p : ℤ) : (ComplexShape.up ℤ).next p = p + 1 :=
      ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel p (p + 1) by rfl)
    let z (p : ℤ) : R.complex.cycles p ≅ R.Z p :=
      R.complex.cyclesIsoSc' (p - 1) p (p + 1) (hp p) (hn p) ≪≫
        (rowHomologyData R p).cyclesIso
    let h (p : ℤ) : R.complex.homology p ≅ R.H p :=
      R.complex.homologyIsoSc' (p - 1) p (p + 1) (hp p) (hn p) ≪≫
        (rowHomologyData R p).homologyIso
    have hzi (p : ℤ) : (z p).hom ≫ R.u p = R.complex.iCycles p := by
      change _ ≫ (rowHomologyData R p).i = _
      simp only [z, Iso.trans_hom, Category.assoc,
        ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
        HomologicalComplex.cyclesIsoSc'_hom_iCycles]
    have hπ (p : ℤ) : R.complex.homologyπ p ≫ (h p).hom = (z p).hom ≫ R.x p := by
      change _ = _ ≫ (rowHomologyData R p).π
      dsimp only [h, z, Iso.trans_hom]
      rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom, Category.assoc,
        ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, Category.assoc]
    have hdexist (p : ℤ) :
        ∃ d : image (R.complex.d (p - 1) p) ≅ R.D p,
          d.hom ≫ R.w p ≫ R.u p = image.ι (R.complex.d (p - 1) p) := by
      let r : R.A (p - 1) ⟶ R.D p :=
        R.v (p - 1) ≫ eqToHom (congrArg R.D (show p - 1 + 1 = p by omega))
      have : Epi (R.v (p - 1)) := (R.exact₁ (p - 1)).epi_g
      have : Epi r := by dsimp [r]; infer_instance
      have : Mono (R.w p) := (R.exact₂ p).mono_f
      have : Mono (R.u p) := (R.exact₁ p).mono_f
      have hr : r ≫ (R.w p ≫ R.u p) = R.complex.d (p - 1) p := by
        simp [r, CartanEilenbergRows.complex, show p - 1 + 1 = p by omega]
      exact ⟨(image.isoStrongEpiMono r (R.w p ≫ R.u p) hr).symm,
        image.isoStrongEpiMono_inv_comp_mono r (R.w p ≫ R.u p) hr⟩
    choose d hdi using hdexist
    have hz (p : ℤ) :
        HomologicalComplex.cyclesMap R.augmentation p ≫ (z p).hom = R.jZ p := by
      have : Mono (R.u p) := (R.exact₁ p).mono_f
      apply (cancel_mono (R.u p)).1
      rw [Category.assoc, hzi, HomologicalComplex.cyclesMap_i]
      exact R.commZ p
    refine ⟨z, d, h, hz, ?_, ?_⟩
    · intro p
      have : Mono (R.w p) := (R.exact₂ p).mono_f
      have : Mono (R.u p) := (R.exact₁ p).mono_f
      apply (cancel_mono (R.w p ≫ R.u p)).1
      rw [Category.assoc, hdi]
      calc
        _ = image.ι (S.d (p - 1) p) ≫ R.augmentation.f p := image.map_ι _
        _ = _ := R.commD p
    · intro p
      apply (cancel_epi (S.homologyπ p)).1
      calc
        S.homologyπ p ≫ (HomologicalComplex.homologyMap R.augmentation p ≫ (h p).hom) =
            HomologicalComplex.cyclesMap R.augmentation p ≫
              (R.complex.homologyπ p ≫ (h p).hom) := by
          rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
        _ = HomologicalComplex.cyclesMap R.augmentation p ≫ ((z p).hom ≫ R.x p) :=
          congrArg (fun f ↦ HomologicalComplex.cyclesMap R.augmentation p ≫ f) (hπ p)
        _ = R.jZ p ≫ R.x p := by rw [← Category.assoc, hz]
        _ = S.homologyπ p ≫ R.jH p := (R.commH p).symm

end CategoryTheory

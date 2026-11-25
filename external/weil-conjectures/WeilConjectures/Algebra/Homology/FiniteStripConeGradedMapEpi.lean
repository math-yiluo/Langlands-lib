/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMap

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem image_le_of_factors {X Y : C} {S : Subobject Y} (g : X ⟶ Y)
    (h : S.Factors g) : imageSubobject g ≤ S :=
  imageSubobject_le g (S.factorThru g h) (Subobject.factorThru_arrow _ _ _)

private theorem epi_of_joint_images {X Y Z W Q : C} (e : W ⟶ Y) [Mono e]
    (g : X ⟶ W) (t : Z ⟶ W) (q : W ⟶ Q) [Epi q]
    (hcover : imageSubobject (g ≫ e) ⊔ imageSubobject (t ≫ e) = imageSubobject e)
    (ht : t ≫ q = 0) : Epi (g ≫ q) := by
  apply Preadditive.epi_of_cancel_zero
  intro R z hz
  have hg : g ≫ (q ≫ z) = 0 := by simpa only [Category.assoc] using hz
  have ht' : t ≫ (q ≫ z) = 0 := by rw [← Category.assoc, ht, zero_comp]
  have hle : Subobject.mk e ≤ Subobject.mk (kernel.ι (q ≫ z) ≫ e) := by
    rw [← imageSubobject_mono e, ← hcover]
    apply sup_le
    · exact imageSubobject_le_mk _ _ (kernel.lift _ g hg) (by simp)
    · exact imageSubobject_le_mk _ _ (kernel.lift _ t ht') (by simp)
  let l := Subobject.ofMkLEMk e (kernel.ι (q ≫ z) ≫ e) hle
  have hl : l ≫ kernel.ι (q ≫ z) = 𝟙 W := by
    apply (cancel_mono e).1
    simpa only [Category.assoc, Category.id_comp] using Subobject.ofMkLEMk_comp hle
  apply zero_of_epi_comp q
  calc
    q ≫ z = (l ≫ kernel.ι (q ≫ z)) ≫ (q ≫ z) := by rw [hl, Category.id_comp]
    _ = 0 := by simp

/-- The row and the next tail jointly generate the current tail.
Source: Stacks Project, Homology, Tag 0133, diagonal quotient argument.
(blueprint: lem-sc-finite-strip-cone-graded-map-split-epi)
Proof: each current-tail generator either has vertical index exactly p and is
in the row image, or has larger vertical index and belongs to the next tail.
The source generator is in the row when n+1=p, and in the next tail otherwise.
The reverse inclusion follows from the row factorization and monotonicity. -/
private theorem row_joint_images
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    imageSubobject (finiteStripRowInclusion K A b f p n) ⊔ F.complexStep (p + 1) n =
      F.complexStep p n := by
  apply le_antisymm
  · apply sup_le
    · exact image_le_of_factors _
        (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p n)
    · rw [hsteps, hsteps]
      apply sup_le_sup
      · split_ifs <;> first | exact le_rfl | exact bot_le | omega
      · apply Finset.sup_mono_fun
        intro i hi
        split_ifs <;> first | exact le_rfl | exact bot_le | omega
  · rw [hsteps]
    apply sup_le
    · split_ifs with hp
      · by_cases heq : n + 1 = p
        · subst p
          have h := imageSubobject_comp_le
            (biprod.inl ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod (f (n + 1))
              (n - (n + 1)) (n - (n + 1) + 1) rfl).inv)
            (finiteStripRowInclusion K A b f (n + 1) n)
          simp only [finiteStripRowInclusion, Category.assoc, Iso.inv_hom_id_assoc,
            biprod.inl_desc] at h
          have hsrc : imageSubobject (finiteStripSourceInclusion K A b (n + 1) n) =
              imageSubobject ((CochainComplex.mappingCone.inl b).v (n + 1) n
                (by omega)) := by
            simp [finiteStripSourceInclusion, imageSubobject_iso_comp]
          exact (hsrc ▸ h).trans le_sup_left
        · apply le_trans _ le_sup_right
          rw [hsteps, ite_eq_left (by omega)]
          exact le_sup_left
      · exact bot_le
    · apply Finset.sup_le
      intro i hi
      split_ifs with hp
      · by_cases heq : p = n - i
        · have hi' : i = n - p := by omega
          subst i
          have hj : n - (n - p) = p := by omega
          rw [hj]
          have h := imageSubobject_comp_le
            (biprod.inr ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p)
              (n - p) (n - p + 1) rfl).inv)
            (finiteStripRowInclusion K A b f p n)
          simp only [finiteStripRowInclusion, Category.assoc, Iso.inv_hom_id_assoc,
            biprod.inr_desc] at h
          exact h.trans le_sup_left
        · apply le_trans _ le_sup_right
          rw [hsteps]
          apply le_trans _ le_sup_right
          apply le_trans _ (Finset.le_sup (f := fun j ↦
            if p + 1 ≤ n - j then imageSubobject
              (K.ιTotalOrZero (ComplexShape.up ℤ) j (n - j) n ≫
                (CochainComplex.mappingCone.inr b).f n) else ⊥) hi)
          rw [ite_eq_left (by omega)]
      · exact bot_le

private theorem filtrationLift_arrow
    (M : CochainComplex C ℤ) (F : DecreasingFiltration M) (p n : ℤ)
    {V : C} (t : V ⟶ M.X n) (ht : (F.complexStep p n).Factors t) :
    let := finiteStripStep_image_isIso M F p n
    (F.complexStep p n).factorThru t ht ≫
      inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
      (F.step p).arrow.f n = t := by
  let := finiteStripStep_image_isIso M F p n
  dsimp only [DecreasingFiltration.complexStep] at ht ⊢
  calc
    _ = (imageSubobject ((F.step p).arrow.f n)).factorThru t ht ≫
        inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
        factorThruImageSubobject ((F.step p).arrow.f n) ≫
        (imageSubobject ((F.step p).arrow.f n)).arrow := by
      rw [imageSubobject_arrow_comp]
    _ = t := by rw [IsIso.inv_hom_id_assoc, Subobject.factorThru_arrow]


/-- The canonical finite-strip graded map is epic.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), diagonal quotient argument;
explicit cone refinement of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-epi)

Proof: write the ambient cone in degree n as the biproduct of A.X (n+1)
and the total diagonal coproduct. The given hsteps identifies the current tail
with the sum of its supported generators. Suppose two arrows out of its graded
quotient agree after the displayed map. Precompose their difference with the
quotient projection, which is epic. On target generators with vertical index p,
the difference vanishes by the assumed equality after the row inclusion. Target
generators with vertical index strictly greater than p lie in the next tail and
are killed by the quotient; these are all remaining target generators. The source
generator survives only when n+1=p and is then the source summand of the row cone;
when n+1>p it lies in the next tail. The source single object is zero in all other
degrees. Thus the difference vanishes on every generator of the current tail,
so the two arrows agree. Unsupported horizontal summands are zero by hsupport.
This proves epimorphy also for r=0 and when n-p lies outside the strip. -/
theorem finiteStripGradedMap_epi
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) : Epi (finiteStripGradedMap K r hsupport A b f F hsteps p n) := by
  let := finiteStripStep_image_isIso (CochainComplex.mappingCone b) F p n
  let g := (F.complexStep p n).factorThru (finiteStripRowInclusion K A b f p n)
    (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p n) ≫
      inv (factorThruImageSubobject ((F.step p).arrow.f n))
  let t := (Subobject.ofLE (F.step (p + 1)) (F.step p)
    (F.antitone_step (by omega))).f n
  let q := (F.complexQuotientπ p (p + 1) (by omega)).f n
  have hg : g ≫ (F.step p).arrow.f n = finiteStripRowInclusion K A b f p n := by
    simpa only [g, Category.assoc] using filtrationLift_arrow
      (CochainComplex.mappingCone b) F p n _
      (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p n)
  have ht : t ≫ (F.step p).arrow.f n = (F.step (p + 1)).arrow.f n := by
    simpa only [t, ← HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom (Subobject.ofLE_arrow
        (F.antitone_step (show p ≤ p + 1 by omega))) n
  have hcover : imageSubobject (g ≫ (F.step p).arrow.f n) ⊔
      imageSubobject (t ≫ (F.step p).arrow.f n) =
        imageSubobject ((F.step p).arrow.f n) := by
    rw [hg, ht]
    exact row_joint_images K r hsupport A b f F hsteps p n
  have htq : t ≫ q = 0 := by
    exact HomologicalComplex.congr_hom (cokernel.condition
      (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega)))) n
  have : Epi q := by
    change Epi ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      (cokernel.π (Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega)))))
    infer_instance
  simpa only [g, q, finiteStripGradedMap, Category.assoc] using
    epi_of_joint_images ((F.step p).arrow.f n) g t q hcover htq


end HomologicalComplex₂

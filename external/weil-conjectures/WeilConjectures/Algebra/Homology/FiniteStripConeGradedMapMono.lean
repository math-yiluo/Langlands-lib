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

/-- Projection from the total object onto its `(n-p,p)` component. -/
private noncomputable def finiteStripTotalProjection
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (p n : ℤ) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X (n - p)).X p :=
  K.totalDesc (fun i j _ ↦
    if h : i = n - p ∧ j = p then eqToHom (by rw [h.1, h.2]) else 0)

/-- The source projection is supported exactly when `n+1=p`. -/
private noncomputable def finiteStripSourceProjection (A : CochainComplex C ℤ) (p n : ℤ) :
    A.X (n + 1) ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p)).X
        (n - p + 1) :=
  if h : n + 1 = p then
    (A.XIsoOfEq h).hom ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (A.X p)
        (n - p + 1) (by omega)).inv
  else 0

/-- The concrete diagonal projection from the ambient cone to the row cone. -/
private noncomputable def finiteStripRowProjection
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (p n : ℤ) :
    (CochainComplex.mappingCone b).X n ⟶ (CochainComplex.mappingCone (f p)).X (n - p) :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod b n (n + 1) rfl).hom ≫
    biprod.map (finiteStripSourceProjection A p n) (finiteStripTotalProjection K p n) ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p) (n - p) (n - p + 1) rfl).inv

private theorem finiteStripTotalProjection_ι
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (p n i j : ℤ) (h : i + j = n) :
    K.ιTotalOrZero (ComplexShape.up ℤ) i j n ≫ finiteStripTotalProjection K p n =
      if h' : i = n - p ∧ j = p then eqToHom (by rw [h'.1, h'.2]) else 0 := by
  rw [K.ιTotalOrZero_eq _ i j n (by simpa using h)]
  exact K.ι_totalDesc _ i j _

set_option backward.isDefEq.respectTransparency false in
/-- The row inclusion and the explicit diagonal projection are a retraction pair. -/
private theorem finiteStripRowInclusion_projection
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (p n : ℤ) :
    finiteStripRowInclusion K A b f p n ≫ finiteStripRowProjection K A b f p n = 𝟙 _ := by
  dsimp only [CochainComplex.mappingCone, ComplexShape.up]
  apply (cancel_epi
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p) (n - p) (n - p + 1) rfl).inv).1
  apply (cancel_mono
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p) (n - p) (n - p + 1) rfl).hom).1
  simp only [finiteStripRowInclusion, finiteStripRowProjection, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc]
    unfold finiteStripSourceInclusion
    split_ifs with h
    · simp only [Category.assoc]
      change _ ≫ _ ≫ HomologicalComplex.homotopyCofiber.inlX b (n + 1) n rfl ≫
        _ ≫ _ = _
      simp only [HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc,
        biprod.inl_map]
      unfold finiteStripSourceProjection
      rw [dite_eq_left h]
      simp only [Category.assoc, HomologicalComplex.XIsoOfEq, eqToIso.hom,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.hom_inv_id_assoc]
      have hr : (biprod.inl :
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p)).X
            (n - p + 1) ⟶ _ ⊞ (K.flip.X p).X (n - p)) =
          biprod.inl ≫
            (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p)
              (n - p) (n - p + 1) rfl).inv ≫
            𝟙 ((HomologicalComplex.homotopyCofiber (f p)).X (n - p)) ≫
            (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p)
              (n - p) (n - p + 1) rfl).hom := by
        let e := HomologicalComplex.homotopyCofiber.XIsoBiprod (f p)
          (n - p) (n - p + 1) rfl
        calc
          _ = biprod.inl ≫ 𝟙 _ := (Category.comp_id _).symm
          _ = biprod.inl ≫ (e.inv ≫ e.hom) :=
            congrArg (fun t ↦ biprod.inl ≫ t) e.inv_hom_id.symm
          _ = biprod.inl ≫ e.inv ≫ (𝟙 _ ≫ e.hom) :=
            congrArg (fun t ↦ biprod.inl ≫ e.inv ≫ t) (Category.id_comp e.hom).symm
      exact hr
    · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (A.X p) (n - p + 1) (by omega)
      exact hz.eq_of_src _ _
  · simp only [biprod.inr_desc_assoc]
    simp only [Category.assoc]
    change K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ≫
      HomologicalComplex.homotopyCofiber.inrX b n ≫ _ ≫ _ = _
    simp only [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc,
      biprod.inr_map]
    rw [← Category.assoc, finiteStripTotalProjection_ι K p n (n - p) p (by omega)]
    simp
    rfl


set_option backward.isDefEq.respectTransparency false in
/-- Descend the explicit projection through the next-tail quotient. -/
private theorem finiteStripGradedMap_hasLeftInverse
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
    ∃ g : (F.gradedPiece p).X n ⟶ (CochainComplex.mappingCone (f p)).X (n - p),
      finiteStripGradedMap K r hsupport A b f F hsteps p n ≫ g = 𝟙 _ := by
  let P := finiteStripRowProjection K A b f p n
  have hk : F.complexStep (p + 1) n ≤ kernelSubobject P := by
    rw [hsteps]
    apply sup_le
    · split_ifs with h
      · apply le_kernelSubobject
        apply imageSubobject_arrow_comp_eq_zero
        have hn : n + 1 ≠ p := by omega
        dsimp only [P, finiteStripRowProjection]
        change HomologicalComplex.homotopyCofiber.inlX b (n + 1) n rfl ≫ _ ≫ _ = 0
        simp only [HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc,
          biprod.inl_map_assoc]
        rw [finiteStripSourceProjection, dite_eq_right hn]
        simp
      · exact bot_le
    · apply Finset.sup_le
      intro i hi
      split_ifs with h
      · apply le_kernelSubobject
        apply imageSubobject_arrow_comp_eq_zero
        have hn : ¬ (i = n - p ∧ n - i = p) := by omega
        dsimp only [P, finiteStripRowProjection]
        simp only [Category.assoc]
        change K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
          HomologicalComplex.homotopyCofiber.inrX b n ≫ _ ≫ _ = 0
        simp only [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc,
          biprod.inr_map_assoc]
        rw [← Category.assoc, ← Category.assoc,
          finiteStripTotalProjection_ι K p n i (n - i) (by omega), dite_eq_right hn]
        simp
      · exact bot_le
  have hzero : (F.step (p + 1)).arrow.f n ≫ P = 0 := by
    calc
      _ = factorThruImageSubobject ((F.step (p + 1)).arrow.f n) ≫
          (F.complexStep (p + 1) n).arrow ≫ P := by
        simp only [DecreasingFiltration.complexStep, imageSubobject_arrow_comp_assoc]
      _ = 0 := by
        rw [← Subobject.ofLE_arrow hk, Category.assoc, kernelSubobject_arrow_comp,
          comp_zero, comp_zero]
  let incl := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have hw : incl.f n ≫ ((F.step p).arrow.f n ≫ P) = 0 := by
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
    exact hzero
  let hc := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n) incl
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hc ((F.step p).arrow.f n ≫ P) hw
  refine ⟨g, ?_⟩
  change (F.complexQuotientπ p (p + 1) (by omega)).f n ≫ g =
    (F.step p).arrow.f n ≫ P at hg
  let := finiteStripStep_image_isIso (CochainComplex.mappingCone b) F p n
  dsimp only [finiteStripGradedMap]
  rw [Category.assoc, Category.assoc, hg]
  have hl : inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
      (F.step p).arrow.f n = (F.complexStep p n).arrow := by
    dsimp only [DecreasingFiltration.complexStep]
    calc
      _ = inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
          factorThruImageSubobject ((F.step p).arrow.f n) ≫
          (imageSubobject ((F.step p).arrow.f n)).arrow := by
        rw [imageSubobject_arrow_comp]
      _ = _ := by rw [IsIso.inv_hom_id_assoc]
  rw [← Category.assoc _ ((F.step p).arrow.f n), hl,
    ← Category.assoc, Subobject.factorThru_arrow]
  exact finiteStripRowInclusion_projection K A b f p n

/-- The canonical finite-strip graded map is monic.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), diagonal quotient argument;
explicit cone refinement of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-mono)

Proof: project the ambient cone in degree n onto its target diagonal summand
K.X (n-p).X p, using the total coproduct projection, and onto its source summand
A.X (n+1) only when n+1=p. Identify the latter with the degree n-p+1 object
of single(A.X p,0); in other degrees that single object is zero. Combine these
projections using the degreewise biproduct decomposition of Cone(f p). Restrict
to the current tail. Each target generator of the next tail has vertical index
at least p+1 and is killed by this projection. Its source generator is present
only when p+1<=n+1, which excludes n+1=p, so it too is killed. Hence the restricted
projection descends through the evaluated cokernel defining the graded quotient.
Its composite with finiteStripGradedMap is the identity: check the two row cone
summands using the biproduct projection-inclusion identities and the total
coproduct identities. If n-p is outside [0,r), that target object is zero by
hsupport; the identity there is zero. The source identity is checked at n+1=p,
and otherwise its object is zero. Thus this descended arrow is a left inverse,
which implies monomorphy. This includes r=0, where only the source can survive. -/
theorem finiteStripGradedMap_mono
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
    (p n : ℤ) : Mono (finiteStripGradedMap K r hsupport A b f F hsteps p n) := by
  obtain ⟨g, hg⟩ := finiteStripGradedMap_hasLeftInverse K r hsupport A b f F hsteps p n
  constructor
  intro Z u v huv
  calc
    u = u ≫ 𝟙 _ := by simp
    _ = u ≫ (finiteStripGradedMap K r hsupport A b f F hsteps p n ≫ g) := by rw [hg]
    _ = (u ≫ finiteStripGradedMap K r hsupport A b f F hsteps p n) ≫ g := by simp
    _ = (v ≫ finiteStripGradedMap K r hsupport A b f F hsteps p n) ≫ g := by rw [huv]
    _ = v ≫ (finiteStripGradedMap K r hsupport A b f F hsteps p n ≫ g) := by simp
    _ = v ≫ 𝟙 _ := by rw [hg]
    _ = v := by simp


end HomologicalComplex₂

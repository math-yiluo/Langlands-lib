/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient
import WeilConjectures.Algebra.Homology.TwoTermCoimageQuasiIso

/-!
# Successive canonical upper truncations

Source: Stacks Project, Homology, Section 12.15 (Tag 0118), and Derived Categories,
Remark 13.12.4 (Tag 08J5) (blueprint: theorem-pbc-injective-acyclicity).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex


private lemma truncLEXIsoCycles_comp_iCycles {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    (K.truncLEXIsoCycles q).hom ≫ K.iCycles q = (K.ιTruncLE q).f q := by
  have h : (K.op.πTruncGE (ComplexShape.embeddingUpIntLE q).op).f q =
      K.op.pOpcycles q ≫
        (K.op.truncGEXIsoOpcycles (ComplexShape.embeddingUpIntLE q).op
          (i := 0) (by change q - 0 = q; omega) (by simp [ComplexShape.Embedding.op_boundaryGE_iff,
            ComplexShape.boundaryLE_embeddingUpIntLE_iff])).inv := by
    rw [HomologicalComplex.πTruncGE,
      ComplexShape.Embedding.liftExtend_f (ComplexShape.embeddingUpIntLE q).op
        _ _ (i := 0) (by change q - 0 = q; omega),
      HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
        K.op (ComplexShape.embeddingUpIntLE q).op (i := 0)
        (by change q - 0 = q; omega) (by simp [ComplexShape.Embedding.op_boundaryGE_iff,
          ComplexShape.boundaryLE_embeddingUpIntLE_iff])]
    simp [HomologicalComplex.truncGEXIsoOpcycles, Category.assoc]
  simp only [truncLEXIsoCycles, HomologicalComplex.truncLEXIsoCycles,
    ιTruncLE, HomologicalComplex.ιTruncLE, HomologicalComplex.unopFunctor_map_f,
    Quiver.Hom.unop_op, h, Iso.trans_hom, Iso.symm_hom, Iso.unop_inv, CategoryTheory.unop_comp,
    Category.assoc]
  have hh := congrArg Quiver.Hom.unop
    ((K.sc q).op_pOpcycles_opcyclesOpIso_hom)
  change (K.opcyclesOpIso q).hom.unop ≫ (K.op.pOpcycles q).unop = K.iCycles q at hh
  rw [← hh]
  simp only [← CategoryTheory.unop_comp, Category.assoc, Iso.hom_inv_id_assoc]

private lemma truncLE_d_homologyπ {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q r : ℤ) :
    (K.truncLE q).d r q ≫ (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q = 0 := by
  have h : (K.truncLE q).d r q ≫ (K.truncLEXIsoCycles q).hom =
      (K.ιTruncLE q).f r ≫ K.toCycles r q := by
    rw [← cancel_mono (K.iCycles q)]
    simp only [Category.assoc, truncLEXIsoCycles_comp_iCycles, HomologicalComplex.toCycles_i]
    exact ((K.ιTruncLE q).comm r q).symm
  rw [← Category.assoc, h, Category.assoc]
  simp

private noncomputable def stepInclusion {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    K.truncLE (q - 1) ⟶ K.truncLE q := by
  have : (K.truncLE (q - 1)).IsStrictlyLE q :=
    isStrictlyLE_of_le _ (q - 1) q (by omega)
  exact inv ((K.truncLE (q - 1)).ιTruncLE q) ≫ truncLEMap (K.ιTruncLE (q - 1)) q

private lemma stepInclusion_comp {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    stepInclusion K q ≫ K.ιTruncLE q = K.ιTruncLE (q - 1) := by
  have : (K.truncLE (q - 1)).IsStrictlyLE q :=
    isStrictlyLE_of_le _ (q - 1) q (by omega)
  simp [stepInclusion, Category.assoc]

private noncomputable def stepProjection {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    K.truncLE q ⟶ (singleFunctor C q).obj (K.homology q) :=
  HomologicalComplex.mkHomToSingle
    ((K.truncLEXIsoCycles q).hom ≫ K.homologyπ q) (fun r _ ↦ truncLE_d_homologyπ K q r)

private lemma stepProjection_self {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    (stepProjection K q).f q ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
      (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q := by
  simp [stepProjection, Category.assoc]

private lemma stepProjection_other {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q r : ℤ) (hr : r ≠ q) :
    (stepProjection K q).f r = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ hr).eq_of_tgt _ _

private lemma truncLEXIsoCycles_naturality {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ) :
    (truncLEMap f q).f q ≫ (L.truncLEXIsoCycles q).hom =
      (K.truncLEXIsoCycles q).hom ≫ HomologicalComplex.cyclesMap f q := by
  rw [← cancel_mono (L.iCycles q)]
  simp only [Category.assoc, truncLEXIsoCycles_comp_iCycles, HomologicalComplex.cyclesMap_i]
  simpa only [HomologicalComplex.comp_f, ← Category.assoc, truncLEXIsoCycles_comp_iCycles] using
    congrArg (fun g ↦ g.f q) (ιTruncLE_naturality f q)

set_option backward.isDefEq.respectTransparency false in

private lemma stepProjection_naturality {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ) :
    truncLEMap f q ≫ stepProjection L q =
      stepProjection K q ≫ (singleFunctor C q).map (HomologicalComplex.homologyMap f q) := by
  apply HomologicalComplex.hom_ext
  intro r
  by_cases hr : r = q
  · subst r
    rw [← cancel_mono
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (L.homology q)).hom]
    simp only [HomologicalComplex.comp_f, Category.assoc, stepProjection_self]
    change _ = (stepProjection K q).f q ≫
      ((HomologicalComplex.single C (ComplexShape.up ℤ) q).map
        (HomologicalComplex.homologyMap f q)).f q ≫ _
    rw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, truncLEXIsoCycles_naturality, Category.assoc,
      ← HomologicalComplex.homologyπ_naturality]
    simp only [← Category.assoc, stepProjection_self]
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ hr).eq_of_tgt

private lemma stepInclusion_projection {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    stepInclusion K q ≫ stepProjection K q = 0 := by
  apply HomologicalComplex.hom_ext
  intro r
  by_cases hr : r = q
  · subst r
    exact ((K.truncLE (q - 1)).isZero_of_isStrictlyLE (q - 1) q (by omega)).eq_of_src _ _
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hr).eq_of_tgt _ _

private instance stepInclusion_mono {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    Mono (stepInclusion K q) := by
  have : Mono (stepInclusion K q ≫ K.ιTruncLE q) := by
    rw [stepInclusion_comp]
    dsimp [ιTruncLE]
    infer_instance
  exact mono_of_mono (stepInclusion K q) (K.ιTruncLE q)

private lemma stepInclusion_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ) :
    (ShortComplex.mk (stepInclusion K q) (cokernel.π (stepInclusion K q))
      (cokernel.condition (stepInclusion K q))).ShortExact := by
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

private lemma stepInclusion_naturality {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ) :
    truncLEMap f (q - 1) ≫ stepInclusion L q = stepInclusion K q ≫ truncLEMap f q := by
  have : Mono (L.ιTruncLE q) := by dsimp [ιTruncLE]; infer_instance
  apply (cancel_mono (L.ιTruncLE q)).1
  simp only [Category.assoc, stepInclusion_comp, ιTruncLE_naturality]
  rw [← Category.assoc, stepInclusion_comp]

/-- Successive canonical upper truncations and their cohomology quotient.
Source: Stacks, Homology Tag 0118 and Derived Categories Remark 08J5
(blueprint: theorem-pbc-injective-acyclicity).

Proof, following the node's seven steps:
1. Define the inclusion by the identity below `q - 1`, the cycles inclusion at
`q - 1`, and zero above. Its composite into `K` is the earlier truncation inclusion.
2. Form the two-term quotient: the cokernel of the kernel inclusion at `q - 1`
and cycles at `q`. The differential induced by `d` is mono by
`lem-weil-pbc-coimage-mono`, and its image is the boundaries.
3. The quotient map is the cokernel projection at `q - 1`, identity on cycles at
`q`, and zero elsewhere. It commutes with the differential and kills the inclusion.
4. These sequences are short exact in each degree, hence short exact as complexes
by `lem-weil-pbc-cochain-complexes-degreewise-exact`; their quotient is `cokernel i`.
5. Projection from cycles to homology defines the map to the single complex. It
kills boundaries, factors through the quotient, and the factor is unique since
its projection is epi.
6. The quotient has zero homology at `q - 1` because its differential is mono.
At `q` its homology is cycles modulo boundaries, and the induced map is the identity
under this identification. In other degrees both homologies vanish. Thus the
factor is a quasi-isomorphism.
7. A chain map preserves cycles and boundaries. It restricts to both truncations
and descends to the quotient, commuting with the cohomology projection; uniqueness
of descent gives naturality.
-/
theorem exists_upperTruncationStepSES {C : Type u} [Category.{v} C] [Abelian C] :
    ∃ (i : ∀ (K : CochainComplex C ℤ) (q : ℤ),
          K.truncLE (q - 1) ⟶ K.truncLE q)
      (j : ∀ (K : CochainComplex C ℤ) (q : ℤ),
          K.truncLE q ⟶ (singleFunctor C q).obj (K.homology q))
      (barj : ∀ (K : CochainComplex C ℤ) (q : ℤ),
          cokernel (i K q) ⟶ (singleFunctor C q).obj (K.homology q)),
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        i K q ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)) ∧
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        (ShortComplex.mk (i K q) (cokernel.π (i K q))
          (cokernel.condition (i K q))).ShortExact) ∧
      (∀ (K : CochainComplex C ℤ) (q r : ℤ),
        r ≠ q - 1 → r ≠ q → IsZero ((cokernel (i K q)).X r)) ∧
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        ∃ (e₀ : (cokernel (i K q)).X (q - 1) ≅
              cokernel (kernel.ι (K.d (q - 1) q)))
          (e₁ : (cokernel (i K q)).X q ≅ K.cycles q),
          (cokernel.π (i K q)).f (q - 1) ≫ e₀.hom =
            (K.ιTruncLE q).f (q - 1) ≫ cokernel.π (kernel.ι (K.d (q - 1) q)) ∧
          (cokernel.π (i K q)).f q ≫ e₁.hom = (K.truncLEXIsoCycles q).hom ∧
          cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
              (cokernel (i K q)).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q =
            K.d (q - 1) q ∧
          Mono ((cokernel (i K q)).d (q - 1) q) ∧
          e₁.inv ≫ (barj K q).f q ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
            K.homologyπ q) ∧
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        (j K q).f q ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q ∧
        (∀ r : ℤ, r ≠ q → (j K q).f r = 0) ∧
        j K q = cokernel.π (i K q) ≫ barj K q ∧
        (∀ b : cokernel (i K q) ⟶ (singleFunctor C q).obj (K.homology q),
          cokernel.π (i K q) ≫ b = j K q → b = barj K q) ∧
        IsZero ((cokernel (i K q)).homology (q - 1)) ∧ QuasiIso (barj K q)) ∧
      (∀ {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ),
        truncLEMap f (q - 1) ≫ i L q = i K q ≫ truncLEMap f q ∧
        ∃ (g : cokernel (i K q) ⟶ cokernel (i L q)),
          truncLEMap f q ≫ cokernel.π (i L q) = cokernel.π (i K q) ≫ g ∧
          barj K q ≫ (singleFunctor C q).map (HomologicalComplex.homologyMap f q) =
            g ≫ barj L q) := by
  let b (K : CochainComplex C ℤ) (q : ℤ) :
      cokernel (stepInclusion K q) ⟶ (singleFunctor C q).obj (K.homology q) :=
    cokernel.desc (stepInclusion K q) (stepProjection K q) (stepInclusion_projection K q)
  have hb (K : CochainComplex C ℤ) (q : ℤ) :
      cokernel.π (stepInclusion K q) ≫ b K q = stepProjection K q := cokernel.π_desc _ _ _
  have coords (K : CochainComplex C ℤ) (q : ℤ) :=
    upperTruncationStep_quotientCoordinates K q (stepInclusion K q) (stepInclusion_comp K q)
  have bq (K : CochainComplex C ℤ) (q : ℤ)
      (e₁ : (cokernel (stepInclusion K q)).X q ≅ K.cycles q)
      (he₁ : (cokernel.π (stepInclusion K q)).f q ≫ e₁.hom = (K.truncLEXIsoCycles q).hom) :
      e₁.inv ≫ (b K q).f q ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
        K.homologyπ q := by
    rw [← cancel_epi ((cokernel.π (stepInclusion K q)).f q ≫ e₁.hom)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← HomologicalComplex.comp_f_assoc, hb, stepProjection_self]
    simp only [← Category.assoc, he₁]
  refine ⟨stepInclusion, stepProjection, b, stepInclusion_comp,
    stepInclusion_shortExact, ?_, ?_, ?_, ?_⟩
  · intro K q r h₀ h₁
    exact (coords K q).1 r h₀ h₁
  · intro K q
    obtain ⟨e₀, e₁, h₀, h₁, hd, hm⟩ := (coords K q).2
    exact ⟨e₀, e₁, h₀, h₁, hd, hm, bq K q e₁ h₁⟩
  · intro K q
    obtain ⟨e₀, e₁, h₀, h₁, hd, hm⟩ := (coords K q).2
    refine ⟨stepProjection_self K q, stepProjection_other K q, (hb K q).symm, ?_, ?_, ?_⟩
    · intro b' h'
      exact (cancel_epi (cokernel.π (stepInclusion K q))).1 (h'.trans (hb K q).symm)
    · apply HomologicalComplex.ExactAt.isZero_homology
      rw [HomologicalComplex.exactAt_iff' _ (q - 2) (q - 1) q (by simp; omega)
        (by simp)]
      exact (ShortComplex.exact_iff_mono _
        (((coords K q).1 (q - 2) (by omega) (by omega)).eq_of_src _ _)).2 hm
    · exact twoTermCoimage_quasiIso K (cokernel (stepInclusion K q)) q
        (coords K q).1 e₀ e₁ hd hm (b K q) (bq K q e₁ h₁)
  · intro K L f q
    refine ⟨stepInclusion_naturality f q, ?_⟩
    let g : cokernel (stepInclusion K q) ⟶ cokernel (stepInclusion L q) :=
      cokernel.map (stepInclusion K q) (stepInclusion L q)
        (truncLEMap f (q - 1)) (truncLEMap f q) (stepInclusion_naturality f q).symm
    have hg : cokernel.π (stepInclusion K q) ≫ g =
        truncLEMap f q ≫ cokernel.π (stepInclusion L q) := by simp [g]
    refine ⟨g, hg.symm, ?_⟩
    apply (cancel_epi (cokernel.π (stepInclusion K q))).1
    simp only [← Category.assoc, hb, hg]
    rw [Category.assoc, hb, stepProjection_naturality]

end CochainComplex

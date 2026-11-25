/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Kernel of a successive lower truncation transition

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations).
(blueprint: lem-pc-lower-truncation-transition-kernel)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private lemma pi_f_above {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasZeroObject C]
    (K : CochainComplex C ℤ) [∀ i, K.HasHomology i] (m r : ℤ) (hr : m < r) :
    (K.πTruncGE m).f r = (K.truncGEXIso m r hr).inv := by
  dsimp only [πTruncGE, HomologicalComplex.πTruncGE, truncGEXIso,
    HomologicalComplex.truncGEXIso, Iso.trans_inv]
  have h : (ComplexShape.embeddingUpIntGE m).f (r - m).natAbs = r := by
    change m + ((r - m).natAbs : ℤ) = r
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ (ComplexShape.embeddingUpIntGE m).BoundaryGE (r - m).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ h,
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ _ h hb]
  simp

private lemma pi_f_self {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasZeroObject C]
    (K : CochainComplex C ℤ) [∀ i, K.HasHomology i] (m : ℤ) :
    (K.πTruncGE m).f m = K.pOpcycles m ≫ (K.truncGEXIsoOpcycles m).inv := by
  dsimp only [πTruncGE, HomologicalComplex.πTruncGE, truncGEXIsoOpcycles,
    HomologicalComplex.truncGEXIsoOpcycles, Iso.trans_inv]
  have h : (ComplexShape.embeddingUpIntGE m).f 0 = m := by simp
  have hb : (ComplexShape.embeddingUpIntGE m).BoundaryGE 0 := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ h,
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ _ h hb]
  simp

/-- Source: Stacks Project, Tag 0118 (homology-section-truncations).

Evaluate the kernel fork in each degree; evaluation preserves kernels. The projection
identity determines the transition since each projection component is epi. At `m`
the target is zero, hence the kernel inclusion is an isomorphism and its source
identifies with opcycles. At `m+1` transport the kernel fork along the invertible
first projection: the transition is the opcycles quotient, whose kernel is the
image of the preceding differential. Below `m` the source is zero; above `m+1`
the transition is invertible, so its kernel is zero. These identifications give
the two inclusion formulas. Apply the chain map identity of the kernel inclusion
and the truncation differential formula to obtain the differential formula.
The argument does not require boundedness; for a zero differential the image
object is zero and the same kernel computation still applies.
-/
private theorem lowerTruncationKernelTerms
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ)
    (q : K.truncGE m ⟶ K.truncGE (m + 1))
    (hq : K.πTruncGE m ≫ q = K.πTruncGE (m + 1)) :
    ∃ (e₀ : (kernel q).X m ≅ K.opcycles m)
      (e₁ : (kernel q).X (m + 1) ≅ Abelian.image (K.d m (m + 1))),
      (e₀.inv ≫ (kernel.ι q).f m = (K.truncGEXIsoOpcycles m).inv) ∧
      (e₁.inv ≫ (kernel.ι q).f (m + 1) ≫ (K.truncGEXIso m (m + 1)).hom =
        Abelian.image.ι (K.d m (m + 1))) ∧
      (e₀.inv ≫ (kernel q).d m (m + 1) ≫ e₁.hom ≫
        Abelian.image.ι (K.d m (m + 1)) = K.fromOpcycles m (m + 1)) ∧
      (∀ (r : ℤ), r ≠ m → r ≠ m + 1 → IsZero ((kernel q).X r)) := by
  let B := kernel q
  let ι := kernel.ι q
  have hker (r : ℤ) : IsLimit (KernelFork.ofι (ι.f r)
      (show ι.f r ≫ q.f r = 0 by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun t => t.f r) (kernel.condition q))) :=
    isLimitForkMapOfIsLimit' (HomologicalComplex.eval C (ComplexShape.up ℤ) r)
      (kernel.condition q) (kernelIsKernel q)
  have hqm : q.f m = 0 :=
    ((K.truncGE (m + 1)).isZero_of_isStrictlyGE (m + 1) m).eq_of_tgt _ _
  have hιm : IsIso (ι.f m) := KernelFork.IsLimit.isIso_ι _ (hker m) hqm
  let e₀ : B.X m ≅ K.opcycles m := asIso (ι.f m) ≪≫ K.truncGEXIsoOpcycles m
  have he₀ : e₀.inv ≫ ι.f m = (K.truncGEXIsoOpcycles m).inv := by
    simp [e₀]
  have hqf (r : ℤ) : (K.πTruncGE m).f r ≫ q.f r =
      (K.πTruncGE (m + 1)).f r := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun t => t.f r) hq
  have hqnext : q.f (m + 1) ≫ (K.truncGEXIsoOpcycles (m + 1)).hom =
      (K.truncGEXIso m (m + 1)).hom ≫ K.pOpcycles (m + 1) := by
    apply (cancel_epi (K.truncGEXIso m (m + 1)).inv).mp
    have h := hqf (m + 1)
    rw [pi_f_above K m (m + 1) (by omega), pi_f_self] at h
    rw [← Category.assoc, h]
    simp
  have hnext : IsLimit (KernelFork.ofι
      (ι.f (m + 1) ≫ (K.truncGEXIso m (m + 1)).hom)
      (show _ ≫ K.pOpcycles (m + 1) = 0 by
        rw [Category.assoc, ← hqnext, ← Category.assoc]
        have h : ι.f (m + 1) ≫ q.f (m + 1) = 0 := by
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
            congrArg (fun t => t.f (m + 1)) (kernel.condition q)
        rw [h, zero_comp])) := by
    apply KernelFork.isLimitOfIsLimitOfIff (hker (m + 1))
      (K.pOpcycles (m + 1)) (K.truncGEXIso m (m + 1))
    intro W a
    rw [← cancel_mono (K.truncGEXIsoOpcycles (m + 1)).hom]
    simp only [Category.assoc, hqnext, zero_comp]
  let ec := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (K.d m (m + 1)))
    (K.opcyclesIsCokernel m (m + 1) (by simp))
  have hec : cokernel.π (K.d m (m + 1)) ≫ ec.hom = K.pOpcycles (m + 1) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (K.d m (m + 1)))
      (K.opcyclesIsCokernel m (m + 1) (by simp)) WalkingParallelPair.one
  have him : IsLimit (KernelFork.ofι (Abelian.image.ι (K.d m (m + 1)))
      (show _ ≫ K.pOpcycles (m + 1) = 0 by rw [← hec]; simp)) := by
    apply KernelFork.isLimitOfIsLimitOfIff'
      (kernelIsKernel (cokernel.π (K.d m (m + 1)))) (K.pOpcycles (m + 1))
    intro W a
    rw [← cancel_mono ec.hom]
    simp only [Category.assoc, hec, zero_comp]
  let e₁ : B.X (m + 1) ≅ Abelian.image (K.d m (m + 1)) :=
    IsLimit.conePointUniqueUpToIso hnext him
  have he₁ : e₁.inv ≫ ι.f (m + 1) ≫ (K.truncGEXIso m (m + 1)).hom =
      Abelian.image.ι (K.d m (m + 1)) :=
    IsLimit.conePointUniqueUpToIso_inv_comp hnext him WalkingParallelPair.zero
  have hd : e₀.inv ≫ B.d m (m + 1) ≫ e₁.hom ≫
      Abelian.image.ι (K.d m (m + 1)) = K.fromOpcycles m (m + 1) := by
    have he₁' : e₁.hom ≫ Abelian.image.ι (K.d m (m + 1)) =
        ι.f (m + 1) ≫ (K.truncGEXIso m (m + 1)).hom := by
      rw [← he₁]
      simp
    rw [← cancel_epi (K.pOpcycles m)]
    simp only [he₁']
    rw [← ι.comm_assoc]
    rw [← Category.assoc e₀.inv (ι.f m), he₀]
    rw [← Category.assoc (K.pOpcycles m), ← pi_f_self,
      (K.πTruncGE m).comm_assoc]
    simp [pi_f_above K m (m + 1) (by omega)]
  refine ⟨e₀, e₁, he₀, he₁, hd, ?_⟩
  intro r hr hr'
  by_cases hlt : r < m
  · have hzero : IsZero ((K.truncGE m).X r) :=
      (K.truncGE m).isZero_of_isStrictlyGE m r hlt
    have : Mono (q.f r) := ⟨fun a b h => hzero.eq_of_tgt _ _⟩
    exact KernelFork.IsLimit.isZero_of_mono (hker r)
  · have habove : m + 1 < r := by omega
    have heq : q.f r = (K.truncGEXIso m r (by omega)).hom ≫
        (K.truncGEXIso (m + 1) r habove).inv := by
      apply (cancel_epi (K.truncGEXIso m r (by omega)).inv).mp
      have h := hqf r
      rw [pi_f_above K m r (by omega), pi_f_above K (m + 1) r habove] at h
      simp only [← Category.assoc, Iso.inv_hom_id]
      simpa using h
    have : IsIso (q.f r) := by rw [heq]; infer_instance
    exact KernelFork.IsLimit.isZero_of_mono (hker r)

private theorem quasiIso_single_of_kernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (B : CochainComplex C ℤ) (m : ℤ) {A : C} (f : A ⟶ B.X m)
    (hf : ∀ r, (ComplexShape.up ℤ).Rel m r → f ≫ B.d m r = 0)
    (hlim : IsLimit (KernelFork.ofι f (hf (m + 1) (by simp))))
    [Epi (B.d m (m + 1))]
    (hz : ∀ r, r ≠ m → r ≠ m + 1 → IsZero (B.X r)) :
    QuasiIso (HomologicalComplex.mkHomFromSingle f hf) := by
  rw [quasiIso_iff]
  intro r
  by_cases hr : r = m
  · subst r
    rw [quasiIsoAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp)]
    let S := ((singleFunctor C m).obj A).sc' (m - 1) m (m + 1)
    let T := B.sc' (m - 1) m (m + 1)
    let ψ : S ⟶ T := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
      (m - 1) m (m + 1)).map (HomologicalComplex.mkHomFromSingle f hf)
    have hfT : T.f = 0 := (hz (m - 1) (by omega) (by omega)).eq_of_src _ _
    let H₁ := ShortComplex.LeftHomologyData.ofZeros S (by simp [S]) (by simp [S])
    let H₂ := ShortComplex.LeftHomologyData.ofIsLimitKernelFork T hfT _ hlim
    let γ : ShortComplex.LeftHomologyMapData ψ H₁ H₂ :=
      { φK := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m A).hom
        φH := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m A).hom
        commi := by
          change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m A).hom ≫ f =
            𝟙 _ ≫ (HomologicalComplex.mkHomFromSingle f hf).f m
          simp
        commπ := by
          change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
          simp }
    exact γ.quasiIso_iff.mpr (by dsimp [γ]; infer_instance)
  · rw [quasiIsoAt_iff_exactAt _ r
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ m A r hr))]
    by_cases hr' : r = m + 1
    · subst r
      rw [B.exactAt_iff' (i := m) (j := m + 1) (k := m + 2) (by simp) (by simp; omega)]
      apply (ShortComplex.exact_iff_epi _
        ((hz (m + 2) (by omega) (by omega)).eq_of_tgt _ _)).mpr
      exact inferInstanceAs (Epi (B.d m (m + 1)))
    · exact HomologicalComplex.ExactAt.of_isZero (hz r hr hr')

/-- Source: Stacks Tag 0118 (homology-section-truncations).
(blueprint: lem-pc-lower-truncation-transition-kernel)

Since the projections are epimorphisms, the factorization determines `q` uniquely.
In degree `m` its target is zero, and its kernel is the source, identified with
opcycles. In degree `m+1`, cancel the invertible degree component of the first
projection: `q` is the opcycles quotient, whose kernel is the image of `d m (m+1)`.
In higher degrees both projections are invertible, so the kernel is zero; below
`m` the source is zero. The chain map identity identifies the remaining kernel
differential with the epimorphism from opcycles onto the image of the differential.
The inclusion of homology into opcycles therefore defines the map `φ`, using the
kernel universal property and the constructor for maps from a single complex.
This component and the kernel inclusion determine `φ` uniquely. Its degree `m`
homology map is the identity of cycles modulo boundaries; degree `m+1` homology
vanishes because the kernel differential is epi; all other degrees are zero.
Thus `φ` is a quasi-isomorphism. These arguments apply also to the zero complex,
zero differentials, and acyclic complexes; no boundedness assumption is needed.
-/
theorem exists_lowerTruncationTransitionKernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ)
    (q : K.truncGE m ⟶ K.truncGE (m + 1))
    (hq : K.πTruncGE m ≫ q = K.πTruncGE (m + 1)) :
    ∃ (φ : ((singleFunctor C m).obj (K.homology m)) ⟶ kernel q),
      (∃ (e₀ : (kernel q).X m ≅ K.opcycles m)
            (e₁ : (kernel q).X (m + 1) ≅
              Abelian.image (K.d m (m + 1))),
            e₀.inv ≫ (kernel.ι q).f m =
              (K.truncGEXIsoOpcycles m).inv ∧
            e₁.inv ≫ (kernel.ι q).f (m + 1) ≫
              (K.truncGEXIso m (m + 1)).hom =
                Abelian.image.ι (K.d m (m + 1)) ∧
            e₀.inv ≫ (kernel q).d m (m + 1) ≫ e₁.hom ≫
              Abelian.image.ι (K.d m (m + 1)) =
                K.fromOpcycles m (m + 1) ∧
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
                (K.homology m)).inv ≫ φ.f m ≫ e₀.hom =
                  K.homologyι m) ∧
      (∀ (r : ℤ), r ≠ m → r ≠ m + 1 → IsZero ((kernel q).X r)) ∧
      QuasiIso φ := by
  obtain ⟨e₀, e₁, he₀, he₁, hd, hz⟩ := lowerTruncationKernelTerms K m q hq
  let f := K.homologyι m ≫ e₀.inv
  have hf : ∀ r, (ComplexShape.up ℤ).Rel m r → f ≫ (kernel q).d m r = 0 := by
    intro r hr
    have : r = m + 1 := by simpa using hr.symm
    subst r
    apply (cancel_mono (e₁.hom ≫ Abelian.image.ι (K.d m (m + 1)))).mp
    simp [f, Category.assoc, hd]
  let φ := HomologicalComplex.mkHomFromSingle f hf
  have hlim : IsLimit (KernelFork.ofι f (hf (m + 1) (by simp))) := by
    apply KernelFork.isLimitOfIsLimitOfIff (K.homologyIsKernel m (m + 1) (by simp))
      ((kernel q).d m (m + 1)) e₀.symm
    intro W a
    rw [← cancel_mono (e₁.hom ≫ Abelian.image.ι (K.d m (m + 1)))]
    simp only [Category.assoc, Iso.symm_hom, hd, zero_comp]
  have hepi : Epi ((kernel q).d m (m + 1)) := by
    have hfac : K.pOpcycles m ≫ e₀.inv ≫ (kernel q).d m (m + 1) ≫ e₁.hom =
        Abelian.factorThruImage (K.d m (m + 1)) := by
      apply (cancel_mono (Abelian.image.ι (K.d m (m + 1)))).mp
      simp [Category.assoc, hd]
    have : Epi (K.pOpcycles m ≫ e₀.inv ≫ (kernel q).d m (m + 1) ≫ e₁.hom) := by
      rw [hfac]
      infer_instance
    have : Epi (e₀.inv ≫ (kernel q).d m (m + 1) ≫ e₁.hom) :=
      epi_of_epi (K.pOpcycles m) _
    have : Epi ((kernel q).d m (m + 1) ≫ e₁.hom) := epi_of_epi e₀.inv _
    exact (epi_comp_iff_of_isIso _ e₁.hom).mp inferInstance
  refine ⟨φ, ⟨e₀, e₁, he₀, he₁, hd, ?_⟩, hz, ?_⟩
  · simp [φ, f, Category.assoc]
  · exact quasiIso_single_of_kernel (kernel q) m f hf hlim hz

end CochainComplex

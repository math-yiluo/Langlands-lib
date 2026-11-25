/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Restriction of the complementary smart truncation comparison -/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma restriction_preservesCokernels :
    PreservesColimitsOfShape WalkingParallelPair
      (ComplexShape.embeddingUpNat.restrictionFunctor C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape WalkingParallelPair
    (HomologicalComplex.eval C (ComplexShape.up ℤ) (n : ℤ))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma restriction_quasiIso {K M : CochainComplex C ℤ} (f : K ⟶ M)
    (hK : IsZero (K.X (-1))) (hM : IsZero (M.X (-1))) [QuasiIso f] :
    QuasiIso (HomologicalComplex.restrictionMap f ComplexShape.embeddingUpNat) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    let αK : (K.restriction ComplexShape.embeddingUpNat).sc' 0 0 1 ⟶ K.sc' (-1) 0 1 :=
      { τ₁ := 0
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [HomologicalComplex.sc', hK.eq_of_src (K.d (-1) 0) 0]
        comm₂₃ := by
          simp [HomologicalComplex.sc', ComplexShape.embeddingUpNat,
            ComplexShape.Embedding.mk'] }
    let αM : (M.restriction ComplexShape.embeddingUpNat).sc' 0 0 1 ⟶ M.sc' (-1) 0 1 :=
      { τ₁ := 0
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [HomologicalComplex.sc', hM.eq_of_src (M.d (-1) 0) 0]
        comm₂₃ := by
          simp [HomologicalComplex.sc', ComplexShape.embeddingUpNat,
            ComplexShape.Embedding.mk'] }
    have : Epi αK.τ₁ := hK.isInitial.epi_to _
    have : Epi αM.τ₁ := hM.isInitial.epi_to _
    have : ShortComplex.QuasiIso αK := ShortComplex.quasiIso_of_epi_of_isIso_of_mono αK
    have : ShortComplex.QuasiIso αM := ShortComplex.quasiIso_of_epi_of_isIso_of_mono αM
    let β := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ) (-1) 0 1).map f
    have : ShortComplex.QuasiIso β :=
      (quasiIsoAt_iff' f (-1) 0 1 (by simp) (by simp)).1 inferInstance
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [← ShortComplex.quasiIso_iff_comp_right _ αM]
    have heq :
        (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map
          (HomologicalComplex.restrictionMap f ComplexShape.embeddingUpNat) ≫ αM = αK ≫ β := by
      ext <;> simp [αK, αM, β, ComplexShape.embeddingUpNat, ComplexShape.Embedding.mk']
    rw [heq]
    infer_instance
  | succ n =>
    rw [quasiIsoAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    have h := (quasiIsoAt_iff' f (n : ℤ) (n + 1) (n + 2)
      (by simp) (by simp; omega)).1 (inferInstance : QuasiIsoAt f (n + 1))
    simpa [HomologicalComplex.shortComplexFunctor', HomologicalComplex.sc',
      HomologicalComplex.restriction, HomologicalComplex.restrictionMap, Nat.cast_add,
      Nat.cast_one, ComplexShape.embeddingUpNat, ComplexShape.Embedding.mk'] using h

/-- The comparison from any cokernel of a restricted smart cutoff inclusion
to the restricted complementary truncation is a quasi-isomorphism.
Source: Mathlib Algebra/Homology/Embedding/AreComplementary.lean,
`shortComplexTruncLEX₃ToTruncGE` and its `QuasiIso` instance.
(blueprint: lem-sp-restricted-complementary-truncation-comparison).

Proof: put E = L.extend embeddingUpNat. Restriction to natural vertical indices
preserves cokernels, since colimits of complexes are computed degreewise. Thus the
cokernel universal property identifies Q with
(cokernel (E.ιTruncLE (a-1))).restriction embeddingUpNat, via an isomorphism
compatible with the cokernel projections. The equation hg
identifies g, under this isomorphism, with the restriction of
E.shortComplexTruncLEX₃ToTruncGE (a-1) a. The embeddings are complementary since
(a-1)+1=a, so Mathlib makes this integer-indexed map a quasi-isomorphism.
For a>0, E is zero in negative degrees, its cutoff is also zero there, and hence
its cokernel is zero there; the lower truncation is zero below a. Thus source and
target have zero degree -1, and restriction preserves their homology even at zero:
there the incoming image is zero in both integer and natural complexes. At positive
indices the three terms and differentials computing homology are unchanged.
For a<=0, the cutoff below a is zero, and truncation from below at a changes only
zero terms (including the boundary cokernel of a zero incoming map). The comparison
is an isomorphism. This includes a=0, a=1, and a column concentrated in degree zero.
Transfer the restricted quasi-isomorphism across the source isomorphism. -/
theorem restrictedComplementaryTruncationComparison_quasiIso
    (L : CochainComplex C ℕ) (a : ℤ) (Q : CochainComplex C ℕ)
    (π : (L.extend ComplexShape.embeddingUpNat).restriction
      ComplexShape.embeddingUpNat ⟶ Q)
    (hzero : HomologicalComplex.restrictionMap
      (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (a - 1))
        ComplexShape.embeddingUpNat ≫ π = 0)
    (hπ : IsColimit (CokernelCofork.ofπ π hzero))
    (g : Q ⟶ (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a).restriction
      ComplexShape.embeddingUpNat)
    (hg : π ≫ g = HomologicalComplex.restrictionMap
      (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a)
        ComplexShape.embeddingUpNat) :
    QuasiIso g := by
  let E := L.extend ComplexShape.embeddingUpNat
  let S := CochainComplex.shortComplexTruncLE E (a - 1)
  let F := ComplexShape.embeddingUpNat.restrictionFunctor C
  have : PreservesColimitsOfShape WalkingParallelPair F := restriction_preservesCokernels
  have hρ := isColimitCoforkMapOfIsColimit' F
    (cokernel.condition (CochainComplex.ιTruncLE E (a - 1)))
    (cokernelIsCokernel (CochainComplex.ιTruncLE E (a - 1)))
  let e := hπ.coconePointUniqueUpToIso hρ
  have he : π ≫ e.hom = HomologicalComplex.restrictionMap S.g
      ComplexShape.embeddingUpNat :=
    hπ.comp_coconePointUniqueUpToIso_hom hρ WalkingParallelPair.one
  let f := CochainComplex.shortComplexTruncLEX₃ToTruncGE E (a - 1) a (by omega)
  have hS : IsZero (S.X₃.X (-1)) :=
    IsZero.of_epi (S.g.f (-1)) (CochainComplex.isZero_of_isStrictlyGE E 0 (-1) (by omega))
  have hT : IsZero ((CochainComplex.truncGE E a).X (-1)) :=
    HomologicalComplex.isZero_X_of_isStrictlySupported _ ComplexShape.embeddingUpNat (-1)
      (by simp [ComplexShape.embeddingUpNat, ComplexShape.Embedding.mk'])
  have : QuasiIso (HomologicalComplex.restrictionMap f ComplexShape.embeddingUpNat) :=
    restriction_quasiIso f hS hT
  have hg' : g = e.hom ≫ HomologicalComplex.restrictionMap f
      ComplexShape.embeddingUpNat := by
    apply Cofork.IsColimit.hom_ext hπ
    change π ≫ g = π ≫ _
    rw [hg, ← Category.assoc, he, ← HomologicalComplex.restrictionMap_comp]
    exact congrArg (fun φ ↦ HomologicalComplex.restrictionMap φ
      ComplexShape.embeddingUpNat) (CochainComplex.g_shortComplexTruncLEX₃ToTruncGE E (a - 1) a
        (by omega)).symm
  rw [hg']
  infer_instance

end CochainComplex

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Coordinates of the quotient of successive upper truncations

Source: Stacks Project, Tags 0118, 0114, and 08J5.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private lemma truncLE_inclusion_coordinates {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    ((K.truncLEXIsoCycles n).hom ≫ K.iCycles n = (K.ιTruncLE n).f n) ∧
      ∀ (r : ℤ) (hr : r < n), (K.ιTruncLE n).f r = (K.truncLEXIso n r hr).hom := by
  constructor
  · have h : (K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f n =
        K.op.pOpcycles n ≫
          (K.op.truncGEXIsoOpcycles (ComplexShape.embeddingUpIntLE n).op
            (i := 0) (by change n - 0 = n; omega) (by
              simp [ComplexShape.Embedding.op_boundaryGE_iff,
                ComplexShape.boundaryLE_embeddingUpIntLE_iff])).inv := by
      rw [HomologicalComplex.πTruncGE,
        ComplexShape.Embedding.liftExtend_f (ComplexShape.embeddingUpIntLE n).op
          _ _ (i := 0) (by change n - 0 = n; omega),
        HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
          K.op (ComplexShape.embeddingUpIntLE n).op (i := 0)
          (by change n - 0 = n; omega) (by
            simp [ComplexShape.Embedding.op_boundaryGE_iff,
              ComplexShape.boundaryLE_embeddingUpIntLE_iff])]
      simp [HomologicalComplex.truncGEXIsoOpcycles, Category.assoc]
    simp only [truncLEXIsoCycles, HomologicalComplex.truncLEXIsoCycles,
      ιTruncLE, HomologicalComplex.ιTruncLE, HomologicalComplex.unopFunctor_map_f,
      Quiver.Hom.unop_op, h, Iso.trans_hom, Iso.symm_hom, Iso.unop_inv,
      CategoryTheory.unop_comp, Category.assoc]
    have hh := congrArg Quiver.Hom.unop
      ((K.sc n).op_pOpcycles_opcyclesOpIso_hom)
    change (K.opcyclesOpIso n).hom.unop ≫ (K.op.pOpcycles n).unop = K.iCycles n at hh
    rw [← hh]
    simp only [← CategoryTheory.unop_comp, Category.assoc, Iso.hom_inv_id_assoc]
  · intro r hr
    have h : (K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f r =
        (K.op.truncGEXIso (ComplexShape.embeddingUpIntLE n).op
          (i := (n - r).natAbs) (by
            change n - (n - r).natAbs = r
            rw [Int.natAbs_of_nonneg (by omega)]
            omega) (by
            simp only [ComplexShape.Embedding.op_boundaryGE_iff,
              ComplexShape.boundaryLE_embeddingUpIntLE_iff]
            omega)).inv := by
      rw [HomologicalComplex.πTruncGE,
        ComplexShape.Embedding.liftExtend_f (ComplexShape.embeddingUpIntLE n).op
          _ _ (i := (n - r).natAbs) (by
            change n - (n - r).natAbs = r
            rw [Int.natAbs_of_nonneg (by omega)]
            omega),
        HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv
          K.op (ComplexShape.embeddingUpIntLE n).op (i := (n - r).natAbs)
          (by
            change n - (n - r).natAbs = r
            rw [Int.natAbs_of_nonneg (by omega)]
            omega) (by
            simp only [ComplexShape.Embedding.op_boundaryGE_iff,
              ComplexShape.boundaryLE_embeddingUpIntLE_iff]
            omega)]
      simp [HomologicalComplex.truncGEXIso, Category.assoc]
    simpa only [truncLEXIso, HomologicalComplex.truncLEXIso, ιTruncLE,
      HomologicalComplex.ιTruncLE, HomologicalComplex.unopFunctor_map_f,
      Quiver.Hom.unop_op, Iso.symm_hom, Iso.unop_inv] using
      congrArg Quiver.Hom.unop h

/-- The cokernel of the inclusion of successive canonical upper truncations is
supported in degrees `q - 1` and `q`, with its induced differential a monomorphism.
Source: Stacks Project, [Tag 0118](https://stacks.math.columbia.edu/tag/0118),
[Tag 0114](https://stacks.math.columbia.edu/tag/0114), and
[Remark 08J5](https://stacks.math.columbia.edu/tag/08J5)
(blueprint: lem-weil-pbc-upper-step-quotient-coordinates).

Proof: the compatibility with the inclusions into `K` determines `i` uniquely,
since the latter inclusion is mono. Below `q - 1`, identify both truncations
with `K`; then `i` is the identity. At `q - 1`, it is the kernel inclusion
`kernel.ι (K.d (q - 1) q)` after the canonical cycles identification. At `q`,
its source is zero and its target is `K.cycles q`. Above `q` both objects are
zero. Evaluation preserves cokernels in the abelian category of complexes.
The degreewise cokernel universal properties therefore give zero objects away
from the two named degrees and the isomorphisms `e₀` and `e₁`, with exactly the
stated identities for the cokernel projection. The differential identity follows
from the chain-map identity for that projection; cancel its epimorphic component
in degree `q - 1`. The composite of the resulting differential with the cycles
inclusion is the coimage factor of `K.d (q - 1) q`, which is mono in an abelian
category (the coimage-to-image map is an isomorphism). Consequently the
quotient differential itself is mono. This also covers zero differentials and
the zero complex: the coimage is then zero.
-/
theorem upperTruncationStep_quotientCoordinates
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ)
    (i : K.truncLE (q - 1) ⟶ K.truncLE q)
    (hi : i ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)) :
    (∀ r : ℤ, r ≠ q - 1 → r ≠ q → IsZero ((cokernel i).X r)) ∧
    ∃ (e₀ : (cokernel i).X (q - 1) ≅ cokernel (kernel.ι (K.d (q - 1) q)))
      (e₁ : (cokernel i).X q ≅ K.cycles q),
      (cokernel.π i).f (q - 1) ≫ e₀.hom =
        (K.ιTruncLE q).f (q - 1) ≫ cokernel.π (kernel.ι (K.d (q - 1) q)) ∧
      (cokernel.π i).f q ≫ e₁.hom = (K.truncLEXIsoCycles q).hom ∧
      cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
          (cokernel i).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q = K.d (q - 1) q ∧
      Mono ((cokernel i).d (q - 1) q) := by
  classical
  have hif (r : ℤ) : i.f r ≫ (K.ιTruncLE q).f r =
      (K.ιTruncLE (q - 1)).f r := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun f ↦ f.f r) hi
  let E (r : ℤ) : (cokernel i).X r ≅ cokernel (i.f r) :=
    PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.up ℤ) r) i
  have hE (r : ℤ) : (cokernel.π i).f r ≫ (E r).hom = cokernel.π (i.f r) :=
    PreservesCokernel.π_iso_hom (HomologicalComplex.eval C (ComplexShape.up ℤ) r) i
  have hz : i.f q = 0 :=
    ((K.truncLE (q - 1)).isZero_of_isStrictlyLE (q - 1) q (by omega)).eq_of_src _ _
  let e₁ : (cokernel i).X q ≅ K.cycles q :=
    E q ≪≫ cokernelIsoOfEq hz ≪≫ cokernelZeroIsoTarget ≪≫ K.truncLEXIsoCycles q
  have he₁ : (cokernel.π i).f q ≫ e₁.hom = (K.truncLEXIsoCycles q).hom := by
    dsimp [e₁]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hE]
    simp
  let a :=
    (K.cyclesIsKernel (q - 1) q (by simp)).conePointUniqueUpToIso
      (kernelIsKernel (K.d (q - 1) q))
  have ha : a.hom ≫ kernel.ι (K.d (q - 1) q) = K.iCycles (q - 1) := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (K.cyclesIsKernel (q - 1) q (by simp))
      (kernelIsKernel (K.d (q - 1) q)) WalkingParallelPair.zero
  let b : (K.truncLE (q - 1)).X (q - 1) ≅ kernel (K.d (q - 1) q) :=
    K.truncLEXIsoCycles (q - 1) ≪≫ a
  let c : (K.truncLE q).X (q - 1) ≅ K.X (q - 1) :=
    K.truncLEXIso q (q - 1) (by omega)
  have hw : i.f (q - 1) ≫ c.hom = b.hom ≫ kernel.ι (K.d (q - 1) q) := by
    dsimp [b, c]
    rw [Category.assoc, ha, (truncLE_inclusion_coordinates K (q - 1)).1,
      ← (truncLE_inclusion_coordinates K q).2 (q - 1) (by omega)]
    exact hif (q - 1)
  let e₀ : (cokernel i).X (q - 1) ≅ cokernel (kernel.ι (K.d (q - 1) q)) :=
    E (q - 1) ≪≫ cokernel.mapIso _ _ b c hw
  have he₀ : (cokernel.π i).f (q - 1) ≫ e₀.hom =
      (K.ιTruncLE q).f (q - 1) ≫ cokernel.π (kernel.ι (K.d (q - 1) q)) := by
    dsimp [e₀]
    rw [← Category.assoc, hE]
    simp only [cokernel.mapIso_hom, cokernel.π_desc]
    rw [(truncLE_inclusion_coordinates K q).2 (q - 1) (by omega)]
  have hd : cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
      (cokernel i).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q = K.d (q - 1) q := by
    have hc : IsIso ((K.ιTruncLE q).f (q - 1)) := by
      rw [(truncLE_inclusion_coordinates K q).2 (q - 1) (by omega)]
      infer_instance
    rw [← cancel_epi ((K.ιTruncLE q).f (q - 1))]
    rw [← Category.assoc, ← he₀]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [(cokernel.π i).comm_assoc (q - 1) q]
    rw [← Category.assoc ((cokernel.π i).f q), he₁,
      (truncLE_inclusion_coordinates K q).1]
    exact ((K.ιTruncLE q).comm (q - 1) q).symm
  have hm : Mono ((cokernel i).d (q - 1) q) := by
    have hf : e₀.inv ≫ (cokernel i).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q =
        Abelian.factorThruCoimage (K.d (q - 1) q) := by
      rw [← cancel_epi (cokernel.π (kernel.ι (K.d (q - 1) q)))]
      simpa only [Abelian.coimage.fac] using hd
    have : Mono (e₀.inv ≫ (cokernel i).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q) := by
      rw [hf]
      infer_instance
    have : Mono ((e₀.inv ≫ (cokernel i).d (q - 1) q) ≫
        (e₁.hom ≫ K.iCycles q)) := by simpa only [Category.assoc] using this
    have : Mono (e₀.inv ≫ (cokernel i).d (q - 1) q) :=
      mono_of_mono (e₀.inv ≫ (cokernel i).d (q - 1) q) (e₁.hom ≫ K.iCycles q)
    have : Mono (e₀.hom ≫ (e₀.inv ≫ (cokernel i).d (q - 1) q)) := inferInstance
    simpa using this
  refine ⟨?_, e₀, e₁, he₀, he₁, hd, hm⟩
  intro r hr₀ hr₁
  apply IsZero.of_iso _ (E r)
  have hir : Epi (i.f r) := by
    by_cases hr : r < q - 1
    · have h₀ : IsIso ((K.ιTruncLE (q - 1)).f r) := by
        rw [(truncLE_inclusion_coordinates K (q - 1)).2 r hr]
        infer_instance
      have h₁ : IsIso ((K.ιTruncLE q).f r) := by
        rw [(truncLE_inclusion_coordinates K q).2 r (by omega)]
        infer_instance
      apply (epi_comp_iff_of_isIso (i.f r) ((K.ιTruncLE q).f r)).mp
      rw [hif r]
      infer_instance
    · exact (K.truncLE q).isZero_of_isStrictlyLE q r (by omega) |>.epi _
  exact isZero_cokernel_of_epi (i.f r)

end CochainComplex

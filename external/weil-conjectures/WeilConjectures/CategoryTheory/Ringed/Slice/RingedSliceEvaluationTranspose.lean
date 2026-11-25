/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceNormalizedComparisons
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationCoherence
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceKoszulCoherence

/-! # Slice evaluation and transpose compatibility

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

set_option backward.isDefEq.respectTransparency false in
private theorem transpose_of_evaluation
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} {r : D ⥤ E}
    {S : CoefficientClosedStructure H} {SU : CoefficientClosedStructure HU}
    {K : Prop} (d : RingedSliceEvaluationComparisons H HU r S SU K)
    (L M : D)
    (he : (d.rho (H.obj (op L, M)) L).inv ≫ r.map (S.evaluation L M) =
      SU.tensor.map (X := (r.obj (H.obj (op L, M)), r.obj L))
        (Y := (HU.obj (op (r.obj L), r.obj M), r.obj L))
        ((d.eta L M).hom, 𝟙 _) ≫ SU.evaluation (r.obj L) (r.obj M))
    (V : D) (f : S.tensor.obj (V, L) ⟶ M) :
    SU.transpose _ _ _ ((d.rho V L).inv ≫ r.map f) =
      r.map (S.transpose V L M f) ≫ (d.eta L M).hom := by
  let := S.monoidal
  let := SU.monoidal
  let g := S.transpose V L M f
  have hg : S.tensor.map (g, 𝟙 L) ≫ S.evaluation L M = f := by
    have h := (S.transpose V L M).symm_apply_apply f
    change ((S.adjunction L).homEquiv V M).symm g = f at h
    rw [Adjunction.homEquiv_symm_apply] at h
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorRight,
      Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id] using h
  have hn : SU.tensor.map (r.map g, 𝟙 (r.obj L)) ≫
      (d.rho (H.obj (op L, M)) L).inv =
      (d.rho V L).inv ≫ r.map (S.tensor.map (g, 𝟙 L)) := by
    apply (cancel_mono (d.rho (H.obj (op L, M)) L).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      d.rho_naturality, Functor.map_id, Iso.inv_hom_id_assoc]
  apply (SU.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change (d.rho V L).inv ≫ r.map f =
    ((SU.adjunction (r.obj L)).homEquiv _ _).symm
      (r.map g ≫ (d.eta L M).hom)
  rw [Adjunction.homEquiv_symm_apply]
  change (d.rho V L).inv ≫ r.map f =
    (r.map g ≫ (d.eta L M).hom) ▷ r.obj L ≫ SU.evaluation _ _
  rw [← MonoidalCategory.tensorHom_id]
  change (d.rho V L).inv ≫ r.map f =
    SU.tensor.map (X := (r.obj V, r.obj L))
      (Y := (HU.obj (op (r.obj L), r.obj M), r.obj L))
      (r.map g ≫ (d.eta L M).hom, 𝟙 _) ≫ SU.evaluation _ _
  have ht : SU.tensor.map (X := (r.obj V, r.obj L))
      (Y := (HU.obj (op (r.obj L), r.obj M), r.obj L))
      (r.map g ≫ (d.eta L M).hom, 𝟙 (r.obj L)) =
      SU.tensor.map (X := (r.obj V, r.obj L))
        (Y := (r.obj (H.obj (op L, M)), r.obj L)) (r.map g, 𝟙 (r.obj L)) ≫
        SU.tensor.map (X := (r.obj (H.obj (op L, M)), r.obj L))
          (Y := (HU.obj (op (r.obj L), r.obj M), r.obj L))
          ((d.eta L M).hom, 𝟙 (r.obj L)) := by
    simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht, Category.assoc, ← he, ← Category.assoc, hn, Category.assoc,
    ← r.map_comp, hg]

/-- Slice restriction preserves evaluation, its adjunction transpose, and Koszul symmetry
for arbitrary unbounded objects, with the canonical representative normalizations above.
Source: Stacks 07A4, 08J9, 08JB and the blueprint delta-restriction proof
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose).

Proof:
1. Resolve L by a flat-term K-flat P and M by a K-injective I; resolve Hom(P,I) by
   a flat-term K-flat Q (lem-pc-kflat-resolution and prop-pur-kinjective-resolutions-exist).
   Restriction preserves these properties (lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   lem-pur-kinjective-restrict-localized), and exactness preserves the resolving quasi-isos.
2. Relocalization identifies local Hom families with the same maps and differential
   d(h)=d_I h-(-1)^n h d_P. Tensor restriction is identity on local pure tensors
   (lem-sfb-localized-site-tensor-restriction). It commutes with sheafification and sums
   (lem-cbc-sieve-slice-sheafification), hence totalization. The descent theorem
   lem-weil-pbc-site-derived-tensor-descent gives the natural derived comparisons.
3. By def-coef-ringed-tensor-hom-model evaluation on Q tensor P is x tensor p ↦ q(x)(p).
   Restricting gives the same formula, proving the evaluation equation on representatives
   and therefore in the derived category. No evaluation map is inverted.
4. Write f as evaluation after transpose(f) tensor identity. Naturality of rho and the
   preceding evaluation equation show that its restricted transpose is eta after the
   restriction of transpose(f). Apply the tensor-Hom bijection; this covers all derived f.
5. In degrees a,b both symmetry composites send x tensor y to (-1)^(ab) y tensor x.
   Equality on generators gives equality on total complexes and then after localization.
   These arguments use no boundedness, perfectness or invertibility of evaluation. -/
theorem ringedSlice_evaluation_transpose
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU) :
    Nonempty {d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U) // RingedSliceEvaluationNormalized.{c, v, u, w, w'} J A U S T SU TU d} ∧
    ∀ (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U))
      (_hd : RingedSliceEvaluationNormalized.{c, v, u, w, w'} J A U S T SU TU d)
      (V L M : DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
        CommRingCat.{max c v u} RingCat.{max c v u})).obj A))) (f : S.tensor.obj (V, L) ⟶ M),
      ((d.rho ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op L, M)) L).inv ≫
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
            (S.evaluation L M) =
      SU.tensor.map (X := ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
        ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op L, M)),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)) (Y :=
        ((derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj (op
        ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)) ((d.eta L M).hom, 𝟙 _) ≫
        SU.evaluation
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M)) ∧
      (SU.transpose _ _ _ ((d.rho V L).inv ≫
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map f) =
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
          (S.transpose V L M f) ≫ (d.eta L M).hom) ∧
      ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
          (d.sigma L M).hom ≫ (d.rho M L).hom =
      (d.rho L M).hom ≫
        (d.sigmaU
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M)).hom) := by
  refine ⟨ringedSlice_normalizedComparisons J A U S T SU TU, ?_⟩
  intro d hd V L M f
  have he := ringedSlice_evaluation_coherence J A U S T SU TU d hd.1 hd.2.1 L M
  refine ⟨he, transpose_of_evaluation d L M he V f, ?_⟩
  exact ringedSlice_koszul_coherence J A U S T SU TU d hd L M

end CategoryTheory

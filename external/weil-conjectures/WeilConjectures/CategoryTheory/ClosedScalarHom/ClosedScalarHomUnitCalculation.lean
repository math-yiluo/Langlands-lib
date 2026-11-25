/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison

/-! # The unit calculation for the five scalar-Hom bijections

Source: Stacks 07A6 and 08J9, specialized to a testing unit object.
-/

@[expose] public section
set_option autoImplicit false

universe a av b bv
open CategoryTheory Opposite WeilConjectures

namespace CategoryTheory.ClosedScalarHom

/-- The five-bijection comparison respects the unit-adjusted inverse closed transpose.
Only the displayed unit square is needed; no associativity or symmetry is assumed.
Source: Stacks 07A6 and 08J9, evaluation-transpose calculation at the unit.
(blueprint: lem-coef-closed-scalar-hom-unit-calculation).

Proof: postcompose the defining five-bijection formula with the inverse comparison.
The two comparison maps cancel, leaving the closed transpose of q. Apply the inverse
closed transpose and the inverse scalar transpose. Naturality of the inverse closed
transpose moves the unit map to the first tensor factor. The unit
square identifies that tensor map followed by the inverse target unitor with the
image of the inverse source unitor. Scalar-adjunction naturality finishes. -/
theorem unit_calculation
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor)
    {IA : A} {IB : B} (e : F.obj IA ⟶ IB) (K : A) (N : B)
    (lA : S.tensor.obj (IA, K) ≅ K)
    (lB : T.tensor.obj (IB, F.obj K) ≅ F.obj K)
    (hunit : μ.hom.app (IA, K) ≫ T.tensor.map (Prod.mkHom e (𝟙 _)) ≫ lB.hom =
      F.map lA.hom)
    (q : IA ⟶ H.obj (op K, U.obj N))
    (r : IB ⟶ I.obj (op (F.obj K), N))
    (hr : e ≫ r = (adj.homEquiv IA _).symm
      (q ≫ (iso S T adj μ).inv.app (op K, N))) :
    lB.inv ≫ (T.transpose IB (F.obj K) N).symm r =
      (adj.homEquiv K N).symm (lA.inv ≫ (S.transpose IA K (U.obj N)).symm q) := by
  have h := representing S T adj μ IA K N
    (q ≫ (iso S T adj μ).inv.app (op K, N))
  simp only [Category.assoc, Iso.inv_hom_id_app] at h
  dsimp only [bijection, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
    Iso.symm_inv, Iso.refl_hom] at h
  change (S.transpose IA K (U.obj N))
    (adj.homEquiv _ N (μ.hom.app (IA, K) ≫
      (T.transpose _ (F.obj K) N).symm
        ((adj.homEquiv IA _).symm (q ≫ (iso S T adj μ).inv.app (op K, N))) ≫ 𝟙 N)) =
      q ≫ 𝟙 (H.obj (op K, U.obj N)) at h
  simp only [Category.comp_id] at h
  have hh : μ.hom.app (IA, K) ≫ (T.transpose _ (F.obj K) N).symm
      ((adj.homEquiv IA _).symm (q ≫ (iso S T adj μ).inv.app (op K, N))) =
        (adj.homEquiv _ N).symm ((S.transpose IA K (U.obj N)).symm q) := by
    apply (adj.homEquiv _ N).injective
    apply (S.transpose IA K (U.obj N)).injective
    simpa only [Equiv.apply_symm_apply] using h
  have ht : (T.transpose _ (F.obj K) N).symm (e ≫ r) =
      T.tensor.map (Prod.mkHom e (𝟙 _)) ≫ (T.transpose IB (F.obj K) N).symm r := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      Prod.sectR, Functor.comp_obj] using
      (T.adjunction (F.obj K)).homEquiv_naturality_left_symm e r
  apply (cancel_epi (F.map lA.hom)).mp
  calc
    F.map lA.hom ≫ (lB.inv ≫ (T.transpose IB (F.obj K) N).symm r) =
        μ.hom.app (IA, K) ≫ (T.transpose _ (F.obj K) N).symm (e ≫ r) := by
      rw [← hunit]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [ht]
    _ = (adj.homEquiv _ N).symm ((S.transpose IA K (U.obj N)).symm q) := by
      rw [hr]
      exact hh
    _ = F.map lA.hom ≫
        (adj.homEquiv K N).symm (lA.inv ≫ (S.transpose IA K (U.obj N)).symm q) := by
      rw [← adj.homEquiv_naturality_left_symm]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoryTheory.ClosedScalarHom

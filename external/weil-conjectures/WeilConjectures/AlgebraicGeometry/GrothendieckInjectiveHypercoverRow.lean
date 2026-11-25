/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverResolution
import WeilConjectures.AlgebraicGeometry.HypercoverInjectiveModuleRow
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Injective hypercover rows with Grothendieck abelian coefficients -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicTopology
open CategoryTheory.IsGrothendieckAbelian

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

omit [CompactSpace X] [QuasiSeparatedSpace X] in
private theorem injective_sheafCompose (F : Sheaf X.smallEtaleTopology A) [Injective F] :
    Injective ((sheafCompose X.smallEtaleTopology
      (preadditiveCoyonedaObj (separator A))).obj F) := by
  let G := separator A
  let R := preadditiveCoyonedaObj G
  let L := tensorObj G
  have : PreservesFiniteLimits L :=
    GabrielPopescu.preservesFiniteLimits G (isSeparator_separator A)
  have : (Sheaf.composeAndSheafify X.smallEtaleTopology L).PreservesMonomorphisms := by
    unfold Sheaf.composeAndSheafify
    infer_instance
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Sheaf.adjunction X.smallEtaleTopology
        (tensorObjPreadditiveCoyonedaObjAdjunction G))
  exact Functor.injective_obj _ _

private theorem section_d_map (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) (n : ℕ) :
    (preadditiveCoyonedaObj (separator A)).map
      (((sectionComplexFunctor A U).obj F).d n (n + 1)) =
      ((sectionComplexFunctor (ModuleCat.{u + 1} (End (separator A))ᵐᵒᵖ) U).obj
          ((sheafCompose X.smallEtaleTopology
            (preadditiveCoyonedaObj (separator A))).obj F)).d n (n + 1) := by
  simp only [sectionComplexFunctor,
    Functor.comp_obj, whiskeringLeft_obj_obj, alternatingCofaceMapComplex,
    AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rfl

private theorem section_a0_map (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) :
    (preadditiveCoyonedaObj (separator A)).map
      ((sectionAugmentation A U F).f 0) =
      (sectionAugmentation (ModuleCat.{u + 1} (End (separator A))ᵐᵒᵖ) U
          ((sheafCompose X.smallEtaleTopology
            (preadditiveCoyonedaObj (separator A))).obj F)).f 0 := by
  simp only [sectionAugmentation,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  rfl

/-- Injective hypercover rows are acyclic with arbitrary Grothendieck abelian coefficients.
Source: Stacks Project, Hypercoverings, Tag 01GW, and Gabriel--Popescu.
(auxiliary; not a blueprint node).

Proof: embed the coefficient category by Hom from a separator into modules over
its opposite endomorphism ring. The exact tensor left adjoint induces a
monomorphism-preserving left adjoint on sheaves. Thus the induced module sheaf
of an injective sheaf is injective. Apply the module hypercover-row theorem.
The embedding is additive and faithful, and therefore reflects exact short
complexes and monomorphisms. Its action commutes with the finite alternating
sums defining every differential and with the augmentation. Reflect the exact
augmented row degree by degree. The degree-zero and positive-degree criteria
for quasi-isomorphisms conclude. -/
theorem injective_row_quasiIso (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) [Injective F] :
    QuasiIso (sectionAugmentation A U F) := by
  let R := preadditiveCoyonedaObj (separator A)
  have : R.Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj _).mp (isSeparator_separator A)
  let F' := (sheafCompose X.smallEtaleTopology R).obj F
  have : Injective F' := injective_sheafCompose A F
  let K := (sectionComplexFunctor A U).obj F
  let K' := (sectionComplexFunctor (ModuleCat.{u + 1} (End (separator A))ᵐᵒᵖ) U).obj F'
  let a := sectionAugmentation A U F
  let a' := sectionAugmentation (ModuleCat.{u + 1} (End (separator A))ᵐᵒᵖ) U F'
  have : QuasiIso a' :=
    AlgebraicGeometry.FiniteSplitEtaleHypercover.injective_module_row_quasiIso U _ F'
  have ha₀ : QuasiIsoAt a' 0 := inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros _
      (HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 0)
      (HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 1)
      (K'.shape 0 0 (by simp))] at ha₀
  have hz : (ShortComplex.mk (a.f 0) (K.d 0 1) (by
      simpa only [HomologicalComplex.single_obj_d, zero_comp] using (a.comm 0 1))).Exact := by
    apply R.reflects_exact_of_faithful
    change (ShortComplex.mk (R.map (a.f 0)) (R.map (K.d 0 1)) _).Exact
    have ha := ha₀.1
    change (ShortComplex.mk (a'.f 0) (K'.d 0 1) _).Exact at ha
    simpa only [show R.map (a.f 0) = a'.f 0 from section_a0_map A U F,
      show R.map (K.d 0 1) = K'.d 0 1 from section_d_map A U F 0] using ha
  have hi : Mono (a.f 0) := by
    have : Mono (R.map (a.f 0)) := by
      change Mono ((preadditiveCoyonedaObj (separator A)).map
        ((sectionAugmentation A U F).f 0))
      rw [section_a0_map]
      exact ha₀.2
    exact R.mono_of_mono_map inferInstance
  have hpos (n : ℕ) : K.ExactAt (n + 1) := by
    have hK' : K'.ExactAt (n + 1) :=
      (quasiIsoAt_iff_exactAt a' (n + 1)
        (HomologicalComplex.ExactAt.of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mp
            inferInstance
    rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp)]
    rw [HomologicalComplex.exactAt_iff' K' n (n + 1) (n + 2) (by simp) (by simp)] at hK'
    apply R.reflects_exact_of_faithful
    change (ShortComplex.mk (R.map (K.d n (n + 1)))
      (R.map (K.d (n + 1) (n + 2))) _).Exact
    change (ShortComplex.mk (K'.d n (n + 1)) (K'.d (n + 1) (n + 2)) _).Exact at hK'
    simpa only [show R.map (K.d n (n + 1)) = K'.d n (n + 1) from
      section_d_map A U F n,
      show R.map (K.d (n + 1) (n + 2)) = K'.d (n + 1) (n + 2) from
        section_d_map A U F (n + 1)] using hK'
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr ⟨hz, hi⟩
      · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 1
      · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 0
      · exact K.shape 0 0 (by simp)
  | succ n =>
      exact (quasiIsoAt_iff_exactAt a (n + 1)
        (HomologicalComplex.ExactAt.of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mpr (hpos n)

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

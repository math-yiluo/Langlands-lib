/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Independence of the corank of a local presentation

Source: the geometric evaluation step of the rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1.
-/

@[expose] public section

universe u v w v₁ w₁

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section FiniteFreeCoordinates

variable {E : Type v} [Field E]
variable {D : Type v₁} [Category.{w₁} D] [Preadditive D] [HasFiniteBiproducts D]
variable (A : D) (F : D ⥤ ModuleCat.{w} E) [F.Additive]
variable (e : F.obj A ≃ₗ[E] E)

/-- Coordinates obtained from the biproduct comparison and the regular-module coordinates. -/
@[irreducible] noncomputable def finiteFreeEvaluationCoords (k : ℕ) :
    F.obj (⨁ fun _ : Fin k ↦ A) ≃ₗ[E] (Fin k → E) :=
  ((F.mapBiproduct (fun _ : Fin k ↦ A)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin k ↦ F.obj A)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

private lemma finiteFreeEvaluationCoords_apply (k : ℕ) (j : Fin k)
    (x : F.obj (⨁ fun _ : Fin k ↦ A)) :
    finiteFreeEvaluationCoords A F e k x j = e ((F.map (biproduct.π (fun _ : Fin k ↦ A) j)) x) := by
  unfold finiteFreeEvaluationCoords
  change e (((ModuleCat.biproductIsoPi _).hom ≫
    ModuleCat.ofHom (LinearMap.proj j)).hom
      ((F.mapBiproduct (fun _ : Fin k ↦ A)).hom x)) = _
  congr 1
  have hp : (ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin k ↦ A))).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  have h := F.biproductComparison_π (fun _ : Fin k ↦ A) j
  rw [← hp] at h
  exact congrArg (fun t ↦ t x) h

private lemma finiteFreeEvaluationCoords_symm_single (k : ℕ) (j : Fin k) (x : E) :
    (finiteFreeEvaluationCoords A F e k).symm (Pi.single j x) =
      F.map (biproduct.ι (fun _ : Fin k ↦ A) j) (e.symm x) := by
  classical
  apply (finiteFreeEvaluationCoords A F e k).injective
  ext i
  rw [LinearEquiv.apply_symm_apply, finiteFreeEvaluationCoords_apply]
  change (Pi.single j x : Fin k → E) i = e ((F.map (biproduct.ι (fun _ : Fin k ↦ A) j) ≫
      F.map (biproduct.π (fun _ : Fin k ↦ A) i))
    (e.symm x))
  rw [← F.map_comp]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

lemma finiteFreeEvaluationCoords_matrix (m n : ℕ)
    (f : (⨁ fun _ : Fin m ↦ A) ⟶ ⨁ fun _ : Fin n ↦ A)
    (M : Matrix (Fin n) (Fin m) E)
    (h : ∀ i j, e (F.map (biproduct.ι _ j ≫ f ≫ biproduct.π _ i) (e.symm 1)) =
      M i j) :
    (finiteFreeEvaluationCoords A F e n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords A F e m).symm.toLinearMap = M.mulVecLin := by
  classical
  apply LinearMap.toMatrix'.injective
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change finiteFreeEvaluationCoords A F e n
    (F.map f ((finiteFreeEvaluationCoords A F e m).symm (Pi.single j 1))) i = _
  rw [finiteFreeEvaluationCoords_symm_single, finiteFreeEvaluationCoords_apply]
  simpa only [Functor.map_comp, ModuleCat.comp_apply, LinearMap.toMatrix'_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h i j

end FiniteFreeCoordinates

lemma finrank_cokernel_of_matrix
    {E : Type v} [Field E] {A B : ModuleCat.{w} E}
    {m n : ℕ} (a : A ≃ₗ[E] (Fin m → E)) (b : B ≃ₗ[E] (Fin n → E))
    (f : A ⟶ B) (M : Matrix (Fin n) (Fin m) E)
    (hf : b.toLinearMap ∘ₗ f.hom ∘ₗ a.symm.toLinearMap = M.mulVecLin) :
    Module.finrank E (cokernel f : ModuleCat.{w} E) = n - M.rank := by
  have : Module.Finite E B := Module.Finite.of_injective b.toLinearMap b.injective
  have hr : M.rank = Module.finrank E (LinearMap.range f.hom) := by
    change Module.finrank E (LinearMap.range M.mulVecLin) = _
    rw [← hf, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 a.symm.surjective, Submodule.map_top]
    exact b.finrank_map_eq _
  calc
    Module.finrank E (cokernel f : ModuleCat.{w} E) =
        Module.finrank E (B ⧸ LinearMap.range f.hom) :=
      (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.finrank_eq
    _ = Module.finrank E B - Module.finrank E (LinearMap.range f.hom) :=
      Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank _)
    _ = n - M.rank := by
      rw [b.finrank_eq, Module.finrank_pi, Fintype.card_fin, ← hr]

private lemma matrix_of_regular_endomorphisms
    (E : Type u) [NormedField E] (V : Scheme.{u})
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ condensedFieldContinuousCoefficientObj E V) [IsIso e]
    (F : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) R ⥤
      ModuleCat.{u + 1} E) [F.Additive]
    (b : F.obj (Mod.regular R) ≃ₗ[E] E) (v : V)
    (h : ∀ f : Mod.regular R ⟶ Mod.regular R,
      b (F.map f (b.symm 1)) =
        condensedFieldContinuousCoefficientMap E V (inv e ≫ f.hom ≫ e) v)
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    (finiteFreeEvaluationCoords (Mod.regular R) F b n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords (Mod.regular R) F b m).symm.toLinearMap =
        ((continuousFieldPresentationMatrix E V e f).map (fun s ↦ s v)).mulVecLin := by
  apply finiteFreeEvaluationCoords_matrix
  intro i j
  exact h (biproduct.ι (fun _ : Fin m ↦ Mod.regular R) j ≫
    f ≫ biproduct.π (fun _ : Fin n ↦ Mod.regular R) i)

/-- Two finite presentations of the same pulled-back module have equal coranks over
points with the same image. No noetherian hypothesis is needed here.
Source: the rank/descent argument, step 3, accompanying Hemo--Richarz--Scholbach,
Example 3.1; Bhatt--Scholze, Example 4.2.11
(auxiliary; not a blueprint node).
Proof: choose an algebraic closure of a common overfield of the two residue fields
at v and w over the residue field of their common image. The resulting geometric
point factors through both cover members. Pull back both cokernel presentations to
that geometric point. Inverse image is additive and preserves finite colimits, and
the monoidal coefficient comparison sends the regular module to the regular module.
Evaluation at the final object on the algebraically closed field is exact, because
pro-etale covers there split, and sends the coefficient ring to E. Compatibility of
the canonical continuous-function realization with inverse image identifies the two
maps with their evaluated matrices. Both cokernels therefore compute the same finite
dimensional E-vector space. Rank-nullity gives n minus matrix rank for both of its
dimensions. This includes zero rows, zero columns, and zero-dimensional cokernels.
An empty cover member contributes no points. -/
theorem condensedField_presentation_corank_eq
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (condensedFieldCoefficientRingObj E) X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (n m : C.I₀ → ℕ)
    (f : ∀ i, Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X)) (m i) ⟶
      Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
        (condensedRingObj (condensedFieldCoefficientRingObj E) X)) (n i))
    (e : ∀ i, (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
      (condensedRingObj (condensedFieldCoefficientRingObj E) X)).obj P) ≅ cokernel (f i))
    (i j : C.I₀) (v : C.X i) (w : C.X j) (h : C.f i v = C.f j w) :
    n i - ((continuousFieldPresentationMatrix E (C.X i)
      (condensedFieldPullbackRealization E (C.f i)) (f i)).map (fun a ↦ a v)).rank =
    n j - ((continuousFieldPresentationMatrix E (C.X j)
      (condensedFieldPullbackRealization E (C.f j)) (f j)).map (fun a ↦ a w)).rank := by
  obtain ⟨z, hzi, hzj⟩ := Scheme.Pullback.exists_preimage_pullback v w h
  let Z := pullback (C.f i) (C.f j)
  let Ω := AlgebraicClosure (Z.residueField z)
  let q : Spec (.of Ω) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω)) ≫
      Z.fromSpecResidueField z
  let a := q ≫ pullback.fst (C.f i) (C.f j)
  let d := q ≫ pullback.snd (C.f i) (C.f j)
  have had : a ≫ C.f i = d ≫ C.f j := by
    simp only [a, d, Category.assoc, pullback.condition]
  let t₀ : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hq : q t₀ = z := by
    exact Scheme.fromSpecResidueField_apply z
      ((Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω))) t₀)
  have ha : a t₀ = v := by
    change pullback.fst (C.f i) (C.f j) (q t₀) = v
    rw [hq]
    exact hzi
  have hd : d t₀ = w := by
    change pullback.snd (C.f i) (C.f j) (q t₀) = w
    rw [hq]
    exact hzj
  rw [← ha, ← hd]
  obtain ⟨F, G, hF, hG, hFc, hGc, ⟨α⟩, b, c, hb, hc⟩ :=
    exists_condensedField_compatible_evaluations E X (C.X i) (C.X j) Ω
      (C.f i) (C.f j) a d had t₀
  let := hF
  let := hG
  let := hFc
  let := hGc
  let Ri := (upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
    (condensedRingObj (condensedFieldCoefficientRingObj E) X)
  let Rj := (upperStar AddCommGrpCat.{u + 1} (C.f j)).obj
    (condensedRingObj (condensedFieldCoefficientRingObj E) X)
  let bi := finiteFreeEvaluationCoords (Mod.regular Ri) F b
  let bj := finiteFreeEvaluationCoords (Mod.regular Rj) G c
  have hbi := matrix_of_regular_endomorphisms E (C.X i)
    (condensedFieldPullbackRealization E (C.f i)) F b (a t₀) hb (f i)
  have hbj := matrix_of_regular_endomorphisms E (C.X j)
    (condensedFieldPullbackRealization E (C.f j)) G c (d t₀) hc (f j)
  let t : cokernel (F.map (f i)) ≅ cokernel (G.map (f j)) :=
    (PreservesCokernel.iso F (f i)).symm ≪≫
      F.mapIso (e i).symm ≪≫ α.app P ≪≫ G.mapIso (e j) ≪≫
        PreservesCokernel.iso G (f j)
  calc
    _ = Module.finrank E (cokernel (F.map (f i)) : ModuleCat.{u + 1} E) :=
      (finrank_cokernel_of_matrix (bi (m i)) (bi (n i)) (F.map (f i)) _
        hbi).symm
    _ = Module.finrank E (cokernel (G.map (f j)) : ModuleCat.{u + 1} E) :=
      t.toLinearEquiv.finrank_eq
    _ = _ := finrank_cokernel_of_matrix (bj (m j)) (bj (n j)) (G.map (f j)) _
      hbj

end AlgebraicGeometry.ProEtale

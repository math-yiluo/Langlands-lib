/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Zero-differential free graded modules as coproducts of single complexes

Source: Stacks Project, Differential Graded Algebra, Tag 09KN, proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {A : Type u} [CommRing A]

private noncomputable def freeBasisIn
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (B : ℤ → Type u)
    (e : ∀ n : ℤ, K.X n ≃ₗ[A] (B n →₀ A)) (hd : ∀ i j : ℤ, K.d i j = 0)
    (i : Σ n : ℤ, B n) :
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i.1).obj
      (ModuleCat.of A A) ⟶ K :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom ((e i.1).symm.toLinearMap.comp (Finsupp.lsingle i.2)))
    (by intro j _; rw [hd, comp_zero])

private noncomputable def freeBasisCofan
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (B : ℤ → Type u)
    (e : ∀ n : ℤ, K.X n ≃ₗ[A] (B n →₀ A)) (hd : ∀ i j : ℤ, K.d i j = 0) :
    Cofan (fun i : Σ n : ℤ, B n ↦
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i.1).obj
        (ModuleCat.of A A)) :=
  Cofan.mk K (freeBasisIn K B e hd)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeBasisEvalIsColimit
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (B : ℤ → Type u)
    (e : ∀ n : ℤ, K.X n ≃ₗ[A] (B n →₀ A)) (hd : ∀ i j : ℤ, K.d i j = 0)
    (n : ℤ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n).mapCocone
      (freeBasisCofan K B e hd)) where
  desc s := ModuleCat.ofHom (LinearMap.comp
    (Finsupp.linearCombination A (M := s.pt) (fun b : B n ↦
      s.ι.app ⟨⟨n, b⟩⟩
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv 1)))
    (e n).toLinearMap)
  fac s i := by
    rcases i with ⟨⟨k, b⟩⟩
    by_cases h : n = k
    · subst k
      change (freeBasisIn K B e hd ⟨n, b⟩).f n ≫ _ = _
      simp only [freeBasisIn, HomologicalComplex.mkHomFromSingle_f]
      apply (cancel_epi
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv).mp
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change Finsupp.linearCombination A _
        (e n ((e n).symm (Finsupp.single b a))) = _
      rw [LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]
      change a • (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
        (ModuleCat.of A A)).inv ≫ s.ι.app ⟨⟨n, b⟩⟩).hom 1) = _
      let t : ModuleCat.of A A ⟶ s.pt :=
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
          (ModuleCat.of A A)).inv ≫ s.ι.app ⟨⟨n, b⟩⟩
      change a • t.hom 1 = t.hom a
      have ht := t.hom.map_smul a (1 : A)
      change t.hom (a * 1) = a • t.hom 1 at ht
      rw [mul_one] at ht
      exact ht.symm
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k
        (ModuleCat.of A A) n h).eq_of_src _ _
  uniq s f h := by
    apply ModuleCat.hom_ext
    have he : f.hom.comp (e n).symm.toLinearMap =
        Finsupp.linearCombination A (fun b : B n ↦ s.ι.app ⟨⟨n, b⟩⟩
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
            (ModuleCat.of A A)).inv 1)) := by
      apply Finsupp.lhom_ext
      intro b a
      have hb := h ⟨⟨n, b⟩⟩
      change (freeBasisIn K B e hd ⟨n, b⟩).f n ≫ f = s.ι.app ⟨⟨n, b⟩⟩ at hb
      have hh := congrArg
        (fun g ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
          (ModuleCat.of A A)).inv ≫ g) hb
      simp only [freeBasisIn, HomologicalComplex.mkHomFromSingle_f,
        Category.assoc, Iso.inv_hom_id_assoc] at hh
      have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hh) a
      change f ((e n).symm (Finsupp.single b a)) = _ at hx
      change f ((e n).symm (Finsupp.single b a)) = _
      rw [hx, Finsupp.linearCombination_single]
      change (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
        (ModuleCat.of A A)).inv ≫ s.ι.app ⟨⟨n, b⟩⟩).hom a) =
          a • (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
            (ModuleCat.of A A)).inv ≫ s.ι.app ⟨⟨n, b⟩⟩).hom 1)
      simpa only [smul_eq_mul, mul_one] using
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
          (ModuleCat.of A A)).inv ≫ s.ι.app ⟨⟨n, b⟩⟩).hom.map_smul a 1)
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun he (e n x)
    change f ((e n).symm (e n x)) = _ at hx
    rw [LinearEquiv.symm_apply_apply] at hx
    exact hx

/-- A zero-differential complex with a specified free basis in each degree is the
coproduct of copies of the ring concentrated in the degrees of those basis vectors.

Source: Stacks Project, Differential Graded Algebra, Tag 09KN,
proof, the identification of the upper and lower graded free modules.

Proof. Index the summands by pairs `(n, b)` with `b : B n`. Map the copy of the
ring concentrated in degree `n` to `K` by sending `1` to `e n` inverse applied to
`Finsupp.single b 1`. This is a map of complexes since all differentials of `K`
are zero. In any fixed degree `m`, the summands with `n != m` are zero. The
remaining summands have the usual free-module coproduct universal property:
a linear map out of `B m →₀ A` is uniquely determined by its values on the basis
vectors. Transport that property along `e m`. Evaluation jointly detects
colimits of complexes, so these inclusions exhibit `K` as the coproduct of the
single complexes. Uniqueness of colimits gives the required isomorphism.
This includes empty basis types and the zero ring.
(blueprint: lem-pc-zero-differential-free-coproduct) -/
theorem nonempty_iso_coproduct_single_of_zero_d
    {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (B : ℤ → Type u) (e : ∀ n : ℤ, K.X n ≃ₗ[A] (B n →₀ A))
    (hd : ∀ i j : ℤ, K.d i j = 0) :
    Nonempty (K ≅ ∐ (fun i : Σ n : ℤ, B n ↦
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i.1).obj
        (ModuleCat.of A A))) := by
  classical
  let c := freeBasisCofan K B e hd
  let hc : IsColimit c := HomologicalComplex.isColimitOfEval _ c
    (freeBasisEvalIsColimit K B e hd)
  exact ⟨hc.coconePointUniqueUpToIso (coproductIsCoproduct _)⟩

end CochainComplex

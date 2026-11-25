/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.ProperBaseChange.FiniteMonicSplitting
import WeilConjectures.ProperBaseChange.MonicTensorPresentation.SplitMonicTensorSections
import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeAlgebraSpectrum

/-!
# Finite affine morphisms and finite covers by closed sections

Source: Stacks Project, Morphisms, Tag 03HW, Lemma `lemma-massage-finite`, clauses (1)–(5)
(blueprint: lem-weil-pbc-finite-affine-section-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite morphism to an affine scheme admits, after surjective finite locally free base
change, a closed immersion into an affine finite locally free scheme covered by finitely many
closed sections. Source: Stacks Project, Morphisms, Tag 03HW, clauses (1)–(5)
(blueprint: lem-weil-pbc-finite-affine-section-cover).

Proof:
1. Use the global-section rings `R` and `B` of the affine schemes. Finite module generators
   also generate the algebra and satisfy monic equations by finite-algebra integrality.
2. Successively split the equations over finite free extensions. For the zero base ring use
   the identity extension. The resulting algebra `S` is faithful, finite and free over `R`.
3. Lying over gives surjectivity of `Spec S → Spec R`. The finite-free spectrum lemma gives
   finite local freeness, which is preserved by composing with `X.isoSpec.inv`.
4. Over `S`, take the finite tensor product of the `AdjoinRoot` algebras of the equations.
   Its tensor power basis makes its spectrum finite locally free. Evaluation at the
   base-changed generators is surjective, giving a closed immersion of `Spec (S ⊗[R] B)`.
5. The tensor-product pushout and the affine comparison isomorphisms identify that spectrum
   with the actual pullback `Y ×_X Spec S`, compatibly with both projections.
6. Evaluation at tuples of roots gives surjective algebra maps back to `S`. Their spectra
   are closed sections. Modulo any prime, each split equation has a vanishing linear factor;
   the corresponding evaluation section contains the point. The finite family covers.
7. Surjectivity, finiteness, flatness and local finite presentation are stable under base
   change, giving the final assertion about the first pullback projection. Zero rings,
   empty generator families, constant equations and repeated roots require no exception. -/
theorem exists_finite_affine_section_cover {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsAffine X] :
    ∃ (X' : Scheme.{u}) (a : X' ⟶ X),
      IsAffine X' ∧ Surjective a ∧ a.IsFiniteLocallyFree ∧
      ∃ (W : Scheme.{u}) (p : W ⟶ X') (j : pullback f a ⟶ W),
        IsAffine W ∧ p.IsFiniteLocallyFree ∧ IsClosedImmersion j ∧
        j ≫ p = pullback.snd f a ∧
        (∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (i : ∀ k : Fin n, Z k ⟶ W),
          (∀ k : Fin n, IsClosedImmersion (i k) ∧ IsIso (i k ≫ p)) ∧
          ∀ w : W, ∃ (k : Fin n) (z : Z k), i k z = w) ∧
        Surjective (pullback.fst f a) ∧ (pullback.fst f a).IsFiniteLocallyFree := by
  classical
  have : IsAffine Y := isAffine_of_isAffineHom f
  let R : Type u := Γ(X, ⊤)
  let B : Type u := Γ(Y, ⊤)
  let : Algebra R B := f.appTop.hom.toAlgebra
  have : Module.Finite R B := f.finite_appTop
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := B)
  have hgen : Algebra.adjoin R (Set.range x) = ⊤ := by
    rw [← Algebra.toSubmodule_eq_top]
    apply top_unique
    rw [← hx]
    exact Algebra.span_le_adjoin R _
  choose P hP hxP using fun i ↦ (IsIntegral.of_finite (R := R) (x i))
  obtain ⟨S, _, _, _, _, _, hsp⟩ := exists_faithful_finite_free_splitting R n P hP
  let X' := Spec (.of S)
  let a₀ : X' ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have ha₀ : a₀.IsFiniteLocallyFree :=
    specMap_isFiniteLocallyFree_of_basis R S (Module.Free.chooseBasis R S)
  have : Surjective a₀ := ⟨Algebra.IsIntegral.comap_surjective R S⟩
  let a : X' ⟶ X := a₀ ≫ X.isoSpec.inv
  have ha : a.IsFiniteLocallyFree := ⟨⟩
  let B' := TensorProduct R S B
  let Q : Fin n → Polynomial S := fun i ↦ (P i).map (algebraMap R S)
  let y : Fin n → B' := fun i ↦ TensorProduct.tmul R 1 (x i)
  have hy : ∀ i, Polynomial.aeval (y i) (Q i) = 0 := by
    intro i
    change Polynomial.aeval (Algebra.TensorProduct.includeRight (x i))
      ((P i).map (algebraMap R S)) = 0
    rw [← Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R S B').symm,
      Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hxP i, map_zero]
  have hgen' : Algebra.adjoin S (Set.range y) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def, y] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := S) (Set.range x) hgen
  let C := MonicTensorPresentation.Tensor Q
  let ψ : C →ₐ[S] B' := MonicTensorPresentation.presentationMap Q y hy
  have hψ : Function.Surjective ψ :=
    MonicTensorPresentation.presentationMap_surjective Q y hy hgen'
  let W := Spec (.of C)
  let p : W ⟶ X' := Spec.map (CommRingCat.ofHom (algebraMap S C))
  have hp : p.IsFiniteLocallyFree :=
    specMap_isFiniteLocallyFree_of_basis S C
      (MonicTensorPresentation.basis Q (fun i ↦ (hP i).map _))
  let t₁ : Spec (.of B') ⟶ Y :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫ Y.isoSpec.inv
  let t₂ : Spec (.of B') ⟶ X' := Spec.map (CommRingCat.ofHom (algebraMap S B'))
  have H : IsPullback t₁ t₂ f a := by
    have H₀ := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R S B)).flip
    refine H₀.of_iso (Iso.refl _) Y.isoSpec.symm (Iso.refl _) X.isoSpec.symm
      (by simp [t₁])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) ?_ (by simp [a, a₀])
    exact Scheme.isoSpec_inv_naturality f
  let j : pullback f a ⟶ W := H.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hψ
  have hj : j ≫ p = pullback.snd f a := by
    dsimp [j, p]
    rw [Category.assoc, ← Spec.map_comp]
    convert H.isoPullback_inv_snd using 1
    congr 2
    ext r
    exact ψ.commutes r
  obtain ⟨m, e, he, hcover⟩ := MonicTensorPresentation.exists_cover S Q
    (fun i ↦ (hP i).map _) hsp
  let Z : Fin m → Scheme.{u} := fun _ ↦ X'
  let i : ∀ k : Fin m, Z k ⟶ W :=
    fun k ↦ Spec.map (CommRingCat.ofHom (e k).toRingHom)
  have hi (k : Fin m) : IsClosedImmersion (i k) ∧ IsIso (i k ≫ p) := by
    refine ⟨IsClosedImmersion.spec_of_surjective _ (he k), ?_⟩
    have hid : i k ≫ p = 𝟙 X' := by
      dsimp [i, p]
      rw [← Spec.map_comp]
      have heq : CommRingCat.ofHom (algebraMap S C) ≫
          CommRingCat.ofHom (e k).toRingHom = 𝟙 (CommRingCat.of S) := by
        ext r
        exact (e k).commutes r
      change Spec.map (CommRingCat.ofHom (algebraMap S C) ≫
        CommRingCat.ofHom (e k).toRingHom) = 𝟙 X'
      rw [heq, Spec.map_id]
    rw [hid]
    infer_instance
  have hc : ∀ w : W, ∃ (k : Fin m) (z : Z k), i k z = w := hcover
  have : Surjective a := inferInstance
  refine ⟨X', a, inferInstance, inferInstance, ha, W, p, j, inferInstance, hp,
    inferInstance, hj, ⟨m, Z, i, hi, hc⟩, inferInstance, ?_⟩
  exact ⟨⟩

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import Mathlib.RingTheory.TensorProduct.Quotient
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient

/-! The non-elementary flatness and tensor-reduction part of the finite constant
completion tower.
Source: Stacks Project, Tags 093M and 0912
(auxiliary; not a blueprint node).
The proof shows that taking sections of a constant sheaf is an exact functor of the
coefficient module, so it commutes with tensoring by finitely presented modules. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]

/--
Source: Stacks Project, Tags 093M and 0912 (auxiliary; not a blueprint node).
Proof: the scalar tower `htower` and the surjectivity of `A → A ⧸ I^(n+1)` force
`(Ideal.Quotient.mk _ a) • b = a • b`, so the given module structure is the canonical
one induced by the sheafification unit. Fix `R = A ⧸ I^(m+1)` and `U`, and let
`G(M)` be the sections over `U` of the sheafified constant presheaf with value the
`R`-module `M`; `G(R)` is `adicTerm … m U`. The functor `G` is additive and left exact
(constant presheaf and sheafification are exact, sections are left exact). It also
preserves surjections: a surjection of sets `p : M → N` has a set-theoretic section
`s`, and the constant sheaf of types (which commutes with forgetting the module
structure) sends `p ∘ s = id` to a splitting of `G(p)`. So `G` is exact, and the
natural map `M ⊗[R] G(R) → G(M)` is an isomorphism for finitely presented `M`
(compare both right exact functors on a presentation `R^a → R^b → M → 0`).
Flatness: for an ideal `𝔞` of the Noetherian ring `R`, `𝔞 ⊗[R] G(R) → G(R)` is
`G(𝔞) → G(R)`, injective by left exactness. Reduction: `G(R) ⊗[A] (A ⧸ I^(n+1))
= G(R) ⊗[R] (A ⧸ I^(min m n + 1)) ≅ G(A ⧸ I^(min m n + 1))`, which is
`adicTerm … (min m n) U`; on `b ⊗ mk a` this isomorphism is `a • adicTransition b`,
the transition being `G` of the quotient map. -/
theorem finiteSystem_flat_and_reduction (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)]
    (htower : ∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)) :
    (∀ (n : ℕ) (U : Cᵒᵖ),
      Module.Flat (A ⧸ I ^ (n + 1))
        (adicTerm J A (finiteSystemUnder J A I) n U)) ∧
    (∀ (m n : ℕ) (U : Cᵒᵖ),
      ∃ e : TensorProduct A (adicTerm J A (finiteSystemUnder J A I) m U)
          (A ⧸ I ^ (n + 1)) ≃ₗ[A] adicTerm J A (finiteSystemUnder J A I) (min m n) U,
        ∀ (b : adicTerm J A (finiteSystemUnder J A I) m U) (a : A),
          e (b ⊗ₜ[A] Ideal.Quotient.mk _ a) = a •
            adicTransition J A (finiteSystemUnder J A I) m (min m n)
              (Nat.min_le_left m n) U b) := by
  constructor
  · intro n U
    let R := A ⧸ I ^ (n + 1)
    let B := adicTerm J A (finiteSystemUnder J A I) n U
    have : IsScalarTower A R B := htower n U
    let η : R →+* B :=
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U).hom
    let α : A →+* B :=
      ((quotient J A I n).hom.app U).hom.comp
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U).hom
    let e : B ≃ₗ[R] (constant J R).obj.obj U :=
      { AddEquiv.refl B with
        map_smul' := by
          intro r b
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
          change (algebraMap A R a) • b = _
          rw [IsScalarTower.algebraMap_smul R]
          change _ = η (Ideal.Quotient.mk _ a) * b
          change α a * b = _
          congr 1
          exact (ConcreteCategory.congr_hom (congr_app
            (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) U) a).symm }
    have : Module.Flat R ((constant J R).obj.obj U) := ringSectionsFlat J R U
    exact Module.Flat.of_linearEquiv e
  · intro m n U
    let S := finiteSystemUnder J A I
    let B := (constant J A).obj.obj U
    let η : A →+* B :=
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U).hom
    let f (k : ℕ) : B →+* adicTerm J A S k U :=
      ((quotient J A I k).hom.app U).hom
    have hf (k : ℕ) : Function.Surjective (f k) :=
      (flat_and_quotients_quotient J A I k U.unop).1
    have hker (k : ℕ) : RingHom.ker (f k) = (I ^ (k + 1)).map η := by
      rw [(flat_and_quotients_quotient J A I k U.unop).2]
      change Ideal.span (Set.range (fun a : ↥(I ^ (k + 1)) ↦ η a)) =
        Ideal.span (η '' (↑(I ^ (k + 1)) : Set A))
      congr 1
      ext x
      simp
    have hscalar (k : ℕ) : (f k).comp η = algebraMap A (adicTerm J A S k U) := rfl
    have hcomp (k l : ℕ) (h : l ≤ k) :
        (adicTransition J A S k l h U).toRingHom.comp (f k) = f l := by
      have hcone := (quotientCone J A I).w (homOfLE h).op
      exact congrArg (fun g ↦ (g.hom.app U).hom) hcone
    let q := adicTransition J A S m (min m n) (Nat.min_le_left m n) U
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨x, rfl⟩ := hf (min m n) y
      exact ⟨f m x, RingHom.congr_fun (hcomp m (min m n) (Nat.min_le_left m n)) x⟩
    have hmap (k : ℕ) : (RingHom.ker (f k)).map (f m) =
        (I ^ (k + 1)).map (algebraMap A (adicTerm J A S m U)) := by
      rw [hker, Ideal.map_map, hscalar]
    have hqker : RingHom.ker q =
        (I ^ (n + 1)).map (algebraMap A (adicTerm J A S m U)) := by
      calc
        RingHom.ker q = ((RingHom.ker q).comap (f m)).map (f m) :=
          (Ideal.map_comap_of_surjective (f m) (hf m) _).symm
        _ = (RingHom.ker (f (min m n))).map (f m) := by
          change ((RingHom.ker q.toRingHom).comap (f m)).map (f m) = _
          rw [RingHom.comap_ker]
          change (RingHom.ker ((adicTransition J A S m (min m n)
            (Nat.min_le_left m n) U).toRingHom.comp (f m))).map (f m) = _
          rw [hcomp]
        _ = (I ^ (n + 1)).map (algebraMap A (adicTerm J A S m U)) := by
          by_cases h : n ≤ m
          · rw [Nat.min_eq_right h, hmap]
          · have hmn : m ≤ n := Nat.le_of_not_ge h
            rw [Nat.min_eq_left hmn, hmap]
            have hm : (I ^ (m + 1)).map (algebraMap A (adicTerm J A S m U)) = ⊥ := by
              rw [← hmap, Ideal.map_eq_bot_iff_le_ker]
            have hn : (I ^ (n + 1)).map (algebraMap A (adicTerm J A S m U)) = ⊥ :=
              eq_bot_iff.mpr ((Ideal.map_mono
                (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))).trans hm.le)
            rw [hm, hn]
    let e :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (adicTerm J A S m U) (I ^ (n + 1))).symm.restrictScalars A).trans
        ((Ideal.quotientEquivAlgOfEq A hqker.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective hq))
    refine ⟨e.toLinearEquiv, ?_⟩
    intro b a
    change q (a • b) = a • q b
    exact q.toLinearMap.map_smul a b
end CategoryTheory.ConstantCompletion

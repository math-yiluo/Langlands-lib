/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.AlgebraicGeometry.IntegralModelFiniteFreeProjector
import WeilConjectures.RingTheory.LiftIdempotentUpstairs
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Lifting finite free projectors over an étale neighbourhood

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, matrix construction.
(blueprint: lem-weil-pbc-etale-lift-finite-free-projector).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An idempotent endomorphism of a finite free quotient module lifts to an
idempotent endomorphism over an étale neighbourhood preserving the quotient.

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, from the choice
of the lifted matrix through the construction of the lifted projector.
(blueprint: lem-weil-pbc-etale-lift-finite-free-projector).

Proof: Apply `exists_integral_model_finite_free_projector` to obtain an
integral commutative `A`-algebra `B`, an algebra map `ψ : B →ₐ[A] Mat_n(A)`,
and an element `y` idempotent modulo `IB` whose matrix image reduces to `pbar`.
Apply Tag 07M4 to the class of `y`. It gives an étale `A → C` preserving `A/I`,
an idempotent `e` of `T = B ⊗[A] C`, and the canonical quotient equivalence `β`
with `β(y mod IB) = e mod IT`. Extend `ψ` to `Ψ : T →ₐ[A] Mat_n(C)`:
on `b ⊗ c` send it to the entrywise image of `ψ b` times the scalar matrix of `c`.
Scalar matrices are central, so the tensor universal property gives an algebra map.
Entrywise reduction of `Ψ` kills `IT`: for `a ∈ I`, its scalar matrix reduces to
zero since the image of `a` lies in `IC`. Factor this map through `T/IT` and
apply it to the lifting equality. The specified value of `β` on `y` gives
`Ψ e mod IC = ψ y` transported to `C/IC`. The compatibility of `α` with the
quotient maps identifies this with the entrywise image of `toMatrix' pbar`
under `α`. Take `p' = toLinAlgEquiv' (Ψ e)`; algebra maps preserve idempotency,
and the inverse matrix equivalences give exactly the displayed matrix equality.
No nontriviality assumptions are used, including when `n=0` or `I=top`.
-/
theorem exists_etale_lift_finite_free_projector
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (pbar : Module.End (A ⧸ I) (Fin n → A ⧸ I)) (hpbar : IsIdempotentElem pbar) :
    ∃ (A' : CommRingCat.{u}) (g : CommRingCat.of A ⟶ A'),
      letI : Algebra A A' := g.hom.toAlgebra;
      Etale (Spec.map g) ∧
      ∃ α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A'),
        (∀ a : A, α (Ideal.Quotient.mk I a) =
          Ideal.Quotient.mk _ (algebraMap A A' a)) ∧
        ∃ p' : Module.End A' (Fin n → A'), IsIdempotentElem p' ∧
          (LinearMap.toMatrix' p').map (Ideal.Quotient.mk _) =
            (LinearMap.toMatrix' pbar).map α.toRingHom := by
  classical
  obtain ⟨B, instB, algB, hB, ψ, y, hy, hmatrix⟩ :=
    exists_integral_model_finite_free_projector A I n pbar hpbar
  let : CommRing B := instB
  let : Algebra A B := algB
  let : Algebra.IsIntegral A B := hB
  obtain ⟨C, g, hg, α, hα, e, he, β, hβ, hmod⟩ :=
    exists_etale_lift_isIdempotentElem I (Ideal.Quotient.mk _ y) hy
  let : Algebra A C := g.hom.toAlgebra
  let T := TensorProduct A B (C : Type u)
  let J := I.map (algebraMap A C)
  let K := I.map (algebraMap A T)
  let ψC : B →ₐ[A] Matrix (Fin n) (Fin n) C :=
    ((Algebra.ofId A C).mapMatrix).comp ψ
  let σ : C →ₐ[A] Matrix (Fin n) (Fin n) C :=
    IsScalarTower.toAlgHom A C (Matrix (Fin n) (Fin n) C)
  have hc : ∀ b c, Commute (ψC b) (σ c) := by
    intro b c
    exact (Algebra.commutes c (ψC b)).symm
  let Ψ : T →ₐ[A] Matrix (Fin n) (Fin n) C :=
    Algebra.TensorProduct.lift ψC σ hc
  let q : Matrix (Fin n) (Fin n) C →+* Matrix (Fin n) (Fin n) (C ⧸ J) :=
    (Ideal.Quotient.mk J).mapMatrix
  have hk : K ≤ RingHom.ker (q.comp Ψ.toRingHom) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change q (Ψ (algebraMap A T a)) = 0
    rw [Ψ.commutes]
    have ha' : Ideal.Quotient.mk J (algebraMap A C a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
    change (Matrix.scalar (Fin n) (algebraMap A C a)).map (Ideal.Quotient.mk J) = 0
    ext i j
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.zero_apply]
    split_ifs <;> simp only [ha', map_zero]
  let δ := Ideal.Quotient.lift K (q.comp Ψ.toRingHom) (fun z hz ↦ hk hz)
  have hreduce : q (Ψ e) = q (ψC y) := by
    have hm := congrArg δ hmod
    rw [hβ y] at hm
    change q (Ψ (y ⊗ₜ[A] (1 : C))) = q (Ψ e) at hm
    change q (Algebra.TensorProduct.lift ψC σ hc (y ⊗ₜ[A] (1 : C))) = q (Ψ e) at hm
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one] at hm
    exact hm.symm
  let p' := Matrix.toLinAlgEquiv' (Ψ e)
  have hp' : IsIdempotentElem p' :=
    (he.map Ψ.toRingHom).map Matrix.toLinAlgEquiv'.toRingHom
  refine ⟨C, g, hg, α, hα, p', hp', ?_⟩
  rw [show LinearMap.toMatrix' p' = Ψ e from
    LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (Ψ e)]
  change q (Ψ e) = (LinearMap.toMatrix' pbar).map α.toRingHom
  rw [hreduce, ← hmatrix]
  ext i j
  exact (hα ((ψ y) i j)).symm

end AlgebraicGeometry

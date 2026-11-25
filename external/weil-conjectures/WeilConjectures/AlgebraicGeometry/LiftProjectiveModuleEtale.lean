/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.LinearAlgebra.IdempotentImageBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleLiftFiniteFreeProjector
import Mathlib.RingTheory.Finiteness.Projective

@[expose] public section

universe u v

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-!
# Finite projective modules lift over an etale neighbourhood

Source: Stacks Project, More on Algebra, Lemma Tag 07M5
(blueprint: lem-weil-pbc-lift-projective-module-etale).
-/

private theorem finite_projective_projector
    {R : Type u} [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    ∃ (n : ℕ) (p : Module.End R (Fin n → R)),
      IsIdempotentElem p ∧ Nonempty (P ≃ₗ[R] p.range) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  let p := g.comp f
  have hp : IsIdempotentElem p := by
    change (g.comp f).comp (g.comp f) = g.comp f
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc f g f, hfg, LinearMap.id_comp]
  have hr : p.range = g.range := by
    exact LinearMap.range_comp_of_range_eq_top g (LinearMap.range_eq_top.mpr hf)
  exact ⟨n, p, hp, ⟨(LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ hr.symm)⟩⟩

private theorem quotient_tensor_equiv
    {R : Type u} [CommRing R] (J : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Nonempty ((M ⧸ (J • (⊤ : Submodule R M))) ≃ₗ[R ⧸ J] ((R ⧸ J) ⊗[R] M)) := by
  let e := (TensorProduct.quotTensorEquivQuotSMul M J).symm
  refine ⟨{ e.toAddEquiv with map_smul' := ?_ }⟩
  intro a x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change e (Submodule.Quotient.mk (r • m)) =
    (Ideal.Quotient.mk J r) • e (Submodule.Quotient.mk m)
  simp only [e, TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/--
A finite projective module over `A/I` lifts to a finite projective module over an
étale `A`-algebra `A'` whose induced map `A/I → A'/IA'` is an isomorphism: there is a
finite projective `A'`-module `P'` with `P'/IP' ≅ (A'/IA') ⊗_{A/I} P̄` as `A'/IA'`-modules,
the tensor product formed via `α` (Mathlib's base-change order `B ⊗ M`).

Source: Stacks Project, More on Algebra, Lemma Tag 07M5
(blueprint: lem-weil-pbc-lift-projective-module-etale).
Proof: write `P̄` as the image of an idempotent projector on `(A/I)^n`, lift it to an
endomorphism `p` of `A^n`, let `B = A[x]/(χ_p(x))` (Cayley–Hamilton), lift the idempotent of
`B/IB` given by the projector over an étale `A → A'` inducing `A/I ≅ A'/IA'`
(lem-weil-pbc-lift-idempotent-upstairs), and take `P'` the image of the resulting
idempotent endomorphism of `A'^n`.
-/
theorem lift_finite_projective_module_etale
    (A : Type u) [CommRing A] (I : Ideal A)
    (Pbar : Type v) [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]
    [Module.Finite (A ⧸ I) Pbar] [Module.Projective (A ⧸ I) Pbar] :
    ∃ (A' : CommRingCat.{u}) (g : CommRingCat.of A ⟶ A'),
      letI : Algebra A A' := g.hom.toAlgebra;
      Etale (Spec.map g) ∧
      ∃ α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A'),
        (∀ a : A, α (Ideal.Quotient.mk I a) =
          Ideal.Quotient.mk _ (algebraMap A A' a)) ∧
        ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module A' P'),
          Module.Finite A' P' ∧ Module.Projective A' P' ∧
          letI : Algebra (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) :=
            α.toRingHom.toAlgebra;
          Nonempty ((P' ⧸ (I.map (algebraMap A A') • (⊤ : Submodule A' P'))) ≃ₗ[
              A' ⧸ I.map (algebraMap A A')]
            ((A' ⧸ I.map (algebraMap A A')) ⊗[A ⧸ I] Pbar)) := by
  classical
  obtain ⟨n, pbar, hpbar, ⟨e⟩⟩ := finite_projective_projector (R := A ⧸ I) Pbar
  obtain ⟨A', g, hg, α, hα, p', hp', hmatrix⟩ :=
    exists_etale_lift_finite_free_projector A I n pbar hpbar
  let : Algebra A A' := g.hom.toAlgebra
  let J := I.map (algebraMap A A')
  let Q := A' ⧸ J
  let : Algebra (A ⧸ I) Q := α.toRingHom.toAlgebra
  obtain ⟨_, _, hfin, hproj, _, f', _, _, _, e', _⟩ :=
    LinearMap.idempotent_image_baseChange n p' hp' (Ideal.Quotient.mk J)
  obtain ⟨_, _, _, _, _, fbar, _, _, _, ebar, _⟩ :=
    LinearMap.idempotent_image_baseChange n pbar hpbar α.toRingHom
  let P' := p'.range
  let : Module.Finite A' P' := hfin
  let : Module.Projective A' P' := hproj
  refine ⟨A', g, hg, α, hα, P', inferInstance, inferInstance, hfin, hproj, ?_⟩
  obtain ⟨eq⟩ := quotient_tensor_equiv J P'
  have hps : Matrix.toLin' ((LinearMap.toMatrix' p').map (Ideal.Quotient.mk J)) =
      Matrix.toLin' ((LinearMap.toMatrix' pbar).map α.toRingHom) :=
    congrArg Matrix.toLin' hmatrix
  let er := LinearEquiv.ofEq _ _ (congrArg LinearMap.range hps)
  let et := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q) e
  exact ⟨eq.trans (e'.trans (er.trans (ebar.symm.trans et.symm)))⟩

end AlgebraicGeometry

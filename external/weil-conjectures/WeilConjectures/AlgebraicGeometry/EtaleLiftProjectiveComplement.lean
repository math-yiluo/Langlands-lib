/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.AlgebraicGeometry.LiftProjectiveModuleEtale
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Lifting a projective complement over an étale neighbourhood

Source: Stacks Project, More on Algebra, Tags 07M5 and 07M7.
-/

@[expose] public section

universe u
open scoped TensorProduct
namespace AlgebraicGeometry

private theorem finite_projective_complement
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module R K),
      Module.Finite R K ∧ Module.Projective R K ∧ Module.Free R (P × K) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  have hfg' : ∀ p, f (g p) = p := fun p ↦ LinearMap.congr_fun hfg p
  let r : (Fin n → R) →ₗ[R] f.ker :=
    (LinearMap.id - g.comp f).codRestrict f.ker (by
      intro x
      simp [LinearMap.mem_ker, hfg'])
  have hr : r.comp f.ker.subtype = LinearMap.id := by
    ext x
    simp [r, LinearMap.mem_ker.mp x.property]
  let : Module.Finite R f.ker := Module.Finite.of_surjective r (by
    intro x
    exact ⟨x.val, LinearMap.congr_fun hr x⟩)
  let : Module.Projective R f.ker := Module.Projective.of_split f.ker.subtype r hr
  let e : (P × f.ker) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.ofBijective (g.coprod f.ker.subtype) (by
      constructor
      · intro x y h
        have hxy : x.1 = y.1 := by
          have hh := congrArg f h
          simpa [hfg', LinearMap.mem_ker.mp x.2.property,
            LinearMap.mem_ker.mp y.2.property] using hh
        apply Prod.ext hxy
        apply Subtype.ext
        have hh : g x.1 + x.2.val = g y.1 + y.2.val := h
        rw [hxy] at hh
        exact add_left_cancel hh
      · intro x
        refine ⟨(f x, r x), ?_⟩
        change g (f x) + (x - g (f x)) = x
        exact add_sub_cancel _ _)
  exact ⟨f.ker, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Free.of_equiv e.symm⟩

private theorem quotient_tensor_equiv
    {R : Type u} [CommRing R] (J : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] :
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

/-- A finite projective quotient module acquires a lifted projective complement.

Source: Stacks Project, More on Algebra, Tag 07M7, first paragraph, and Tag 07M5.
(blueprint: lem-weil-pbc-etale-lift-projective-complement)

Proof: split a surjection from a finite free module onto P using projectivity.
Its kernel Kbar is finite projective, and the splitting identifies P × Kbar
with that finite free module. Apply Tag 07M5 to Kbar, obtaining A₁, the quotient
isomorphism alpha and a finite projective lift K. Define eta as alpha inverse
composed with the quotient map A₁ → A₁/JA₁. Compatibility of alpha makes eta an
A-algebra map; it is surjective. The quotient-tensor identification for K and
the lift isomorphism, transported through alpha inverse, identify
(A/J) tensor over A₁ K with Kbar. Transport the free structure along the product
of this identification with the identity on P. For J = top all modules over
A/J are zero; the same splitting and quotient identifications apply.
-/
theorem exists_etale_lift_projective_complement
    (A : Type u) [CommRing A] (J : Ideal A)
    (P : Type u) [AddCommGroup P] [Module (A ⧸ J) P]
    [Module.Finite (A ⧸ J) P] [Module.Projective (A ⧸ J) P] :
    ∃ A₁ : CommAlgCat.{u} A,
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A A₁))) ∧
      ∃ η : A₁ →ₐ[A] A ⧸ J, Function.Surjective η ∧
        ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module A₁ K),
          Module.Finite A₁ K ∧ Module.Projective A₁ K ∧
          letI : Algebra A₁ (A ⧸ J) := η.toRingHom.toAlgebra
          Module.Free (A ⧸ J) (P × ((A ⧸ J) ⊗[A₁] K)) := by
  classical
  obtain ⟨Kbar, hAdd, hMod, hFin, hProj, hFree⟩ :=
    finite_projective_complement (R := A ⧸ J) P
  let : AddCommGroup Kbar := hAdd
  let : Module (A ⧸ J) Kbar := hMod
  let : Module.Finite (A ⧸ J) Kbar := hFin
  let : Module.Projective (A ⧸ J) Kbar := hProj
  let : Module.Free (A ⧸ J) (P × Kbar) := hFree
  obtain ⟨A', g, hEt, α, hα, K, hKAdd, hKMod, hKFin, hKProj, he⟩ :=
    lift_finite_projective_module_etale A J Kbar
  let : Algebra A A' := g.hom.toAlgebra
  let I := J.map (algebraMap A A')
  let Q' := A' ⧸ I
  let η : A' →ₐ[A] A ⧸ J :=
    { α.symm.toRingHom.comp (Ideal.Quotient.mk I) with
      commutes' := by
        intro a
        change α.symm (Ideal.Quotient.mk I (algebraMap A A' a)) =
          Ideal.Quotient.mk J a
        rw [← hα a, α.symm_apply_apply] }
  let : AddCommGroup K := hKAdd
  let : Module A' K := hKMod
  let : Module.Finite A' K := hKFin
  let : Module.Projective A' K := hKProj
  refine ⟨CommAlgCat.of A A', hEt, η, ?_, K, hKAdd, hKMod, hKFin, hKProj, ?_⟩
  · exact α.symm.surjective.comp Ideal.Quotient.mk_surjective
  · let : Algebra (A ⧸ J) Q' := α.toRingHom.toAlgebra
    let : Algebra Q' (A ⧸ J) := α.symm.toRingHom.toAlgebra
    let : Algebra A' (A ⧸ J) := η.toRingHom.toAlgebra
    let : IsScalarTower A' Q' (A ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower (A ⧸ J) Q' (A ⧸ J) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (α.symm_apply_apply _).symm)
    obtain ⟨eq⟩ := quotient_tensor_equiv I K
    obtain ⟨e⟩ := he
    let e₁ := TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (A ⧸ J) (A ⧸ J)) (eq.symm.trans e)
    let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
      A' Q' (A ⧸ J) (A ⧸ J) K
    let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A ⧸ J) Q' (A ⧸ J) (A ⧸ J) Kbar
    let eK := e₂.symm.trans (e₁.trans (e₃.trans (TensorProduct.lid (A ⧸ J) Kbar)))
    exact Module.Free.of_equiv
      ((LinearEquiv.refl (A ⧸ J) P).prodCongr eK).symm

end AlgebraicGeometry

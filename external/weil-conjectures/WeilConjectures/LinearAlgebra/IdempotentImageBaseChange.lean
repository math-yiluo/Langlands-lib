/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Images of finite free projectors under base change

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, final projector argument
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

open TensorProduct

namespace LinearMap

/-- The image of a finite free projector is finite projective and commutes with base change.
Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, final sentences
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof: Put `q = 1 - p`. The identities `q² = q`, `pq = qp = 0`, and `p + q = 1`
decompose every vector as `p v + q v`. Applying `p` to a vector in both images makes
it zero, and `q v = v` on the kernel of `p`. Thus the images are complementary and
`range q = ker p`. A direct summand of a finite free module is finite projective.
Tensor this split decomposition with `S`. The split inclusions and projections remain
split, and the tensor universal property identifies the first inclusion with
`s ⊗ v ↦ s • ρ(v)` (lem-weil-pbc-module-base-change-universal-property).
The hypothesis `p ∘ p = p` is `IsIdempotentElem p` in `Module.End R (Fin n → R)`, whose
multiplication is composition; likewise for `p_S`.
The matrix of the tensor projector is the entrywise image of the original matrix.
It is identity on the first tensor summand and zero on the second. Hence it is
idempotent, and its range is exactly the injective image of the first tensor summand.
The resulting range equivalence is the displayed canonical map. The tensor factors
are ordered `S ⊗[R] range p`, using the canonical commutor to express `range p ⊗[R] S`.
-/
theorem idempotent_image_baseChange
    {R : Type u} [CommRing R] (n : ℕ)
    (p : Module.End R (Fin n → R)) (hp : IsIdempotentElem p)
    {S : Type v} [CommRing S] (ρ : R →+* S) :
    letI : Algebra R S := ρ.toAlgebra
    let pS : Module.End S (Fin n → S) :=
      Matrix.toLin' ((LinearMap.toMatrix' p).map ρ)
    IsCompl p.range (1 - p).range ∧
      (1 - p).range = p.ker ∧
      Module.Finite R p.range ∧ Module.Projective R p.range ∧
      IsIdempotentElem pS ∧
      ∃ f : S ⊗[R] p.range →ₗ[S] (Fin n → S),
        (∀ (s : S) (x : p.range), f (s ⊗ₜ[R] x) = fun i ↦ s * ρ (x.val i)) ∧
        Function.Injective f ∧ f.range = pS.range ∧
        ∃ e : S ⊗[R] p.range ≃ₗ[S] pS.range,
          pS.range.subtype.comp e.toLinearMap = f := by
  classical
  dsimp
  let : Algebra R S := ρ.toAlgebra
  let pS : Module.End S (Fin n → S) :=
    Matrix.toLin' ((LinearMap.toMatrix' p).map ρ)
  have hker : (1 - p).range = p.ker := (LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp).symm
  have hcompl : IsCompl p.range (1 - p).range := by
    rw [hker]
    exact LinearMap.IsIdempotentElem.isCompl hp
  have hfinite : Module.Finite R p.range := by infer_instance
  have hproj : Module.Projective R p.range := by
    apply Module.Projective.of_split p.range.subtype
      (LinearMap.IsIdempotentElem.isProj_range p hp).codRestrict
    ext x
    simp
  let E := TensorProduct.piScalarRight R S S (Fin n)
  let i := p.range.subtype.baseChange S
  let r := (LinearMap.IsIdempotentElem.isProj_range p hp).codRestrict.baseChange S
  let f := E.toLinearMap.comp i
  let g := r.comp E.symm.toLinearMap
  have hri : r.comp i = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    simp [r, i]
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change r (E.symm (E (i x))) = x
    rw [E.symm_apply_apply]
    exact DFunLike.congr_fun hri x
  have hcomm : f.comp r = pS.comp E.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    ext j
    simp only [LinearMap.comp_apply, f, r, i, E, LinearMap.baseChange_tmul,
      LinearMap.IsProj.codRestrict_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, pS, Matrix.toLin'_apply,
      Algebra.smul_def]
    change ρ (p x j) * s =
      ((toMatrix' p).map ρ).mulVec (fun k ↦ ρ (x k) * s) j
    rw [← LinearMap.toMatrix'_mulVec p x, RingHom.map_mulVec]
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  have hfg : f.comp g = pS := by
    apply LinearMap.ext
    intro x
    change f (r (E.symm x)) = pS x
    rw [← LinearMap.comp_apply, hcomm]
    simp
  have hps : IsIdempotentElem pS := by
    change pS * pS = pS
    rw [← hfg]
    change (f.comp g).comp (f.comp g) = f.comp g
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc g f g, hgf]
    simp
  have hinj : Function.Injective f :=
    Function.LeftInverse.injective (f := f) (g := g)
      (fun x ↦ DFunLike.congr_fun hgf x)
  have hrange : f.range = pS.range := by
    rw [← hfg]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨f x, ?_⟩
      change f (g (f x)) = f x
      rw [show g (f x) = x from DFunLike.congr_fun hgf x]
    · exact LinearMap.range_comp_le_range _ _
  refine ⟨hcompl, hker, hfinite, hproj, hps, f, ?_, hinj, hrange, ?_⟩
  · intro s x
    simp [f, i, E, Algebra.smul_def, mul_comm, RingHom.algebraMap_toAlgebra]
  · refine ⟨(LinearEquiv.ofInjective f hinj).trans
      (LinearEquiv.ofEq _ _ hrange), ?_⟩
    ext x j
    simp

end LinearMap

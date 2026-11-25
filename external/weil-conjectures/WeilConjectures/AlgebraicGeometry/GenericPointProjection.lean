/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosurePointDimension
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization

/-!
# Projections to affine space sending a point to the generic point

Let `U` be an affine scheme of finite type over a field `k` and `y ∈ U` a point whose closure has
dimension `r`. Then there is a morphism `p : U ⟶ 𝔸ʳ_k` over `k` sending `y` to the generic point
of `𝔸ʳ_k`: by Noether normalization `Γ(U) ⧸ 𝔭_y` contains `r` algebraically independent elements,
and their lifts to `Γ(U)` define `p`. Conversely, the fibre over the generic point of any morphism
`g : Z ⟶ 𝔸ʳ_k` locally of finite type has dimension at most `dim Z - r`.

## Main statements

- `exists_algHom_mvPolynomial_comap_eq_bot`: the algebraic statement.
- `AlgebraicGeometry.Scheme.exists_hom_mvPolynomial_apply_eq_bot`: the projection.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_preimage_add_le_of_asIdeal_eq_bot`: the
  dimension of the generic fibre.
-/

@[expose] public section

universe u

open CategoryTheory

/-- For a finitely generated algebra `A` over a field `k` and an ideal `P` with
`dim (A ⧸ P) = r`, there is a `k`-algebra map `k[T₁, …, Tᵣ] → A` whose preimage of `P` is zero:
lift the coordinates of a Noether normalization of `A ⧸ P` to `A`. -/
theorem exists_algHom_mvPolynomial_comap_eq_bot (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) (r : ℕ) (hr : ringKrullDim (A ⧸ P) = r) :
    ∃ φ : MvPolynomial (Fin r) k →ₐ[k] A, P.comap φ = ⊥ := by
  have : Algebra.FiniteType k (A ⧸ P) :=
    .of_surjective (Ideal.Quotient.mkₐ k _) Ideal.Quotient.mk_surjective
  obtain ⟨g, hg, -⟩ := exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq k (A ⧸ P) r hr
  let a (i : Fin r) : A := (Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))).choose
  have ha (i : Fin r) : Ideal.Quotient.mk P (a i) = g (MvPolynomial.X i) :=
    (Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))).choose_spec
  have hφ : (Ideal.Quotient.mkₐ k P).comp (MvPolynomial.aeval a) = g :=
    MvPolynomial.algHom_ext fun i ↦ by simp [ha]
  refine ⟨MvPolynomial.aeval a, eq_bot_iff.2 fun x hx ↦ ?_⟩
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.mem_bot]
  refine hg ?_
  rw [← hφ, map_zero]
  exact hx

/-- If `(∀ e : ℕ, e ≤ a → r + e ≤ b)` then `a + r ≤ b` in `WithBot ℕ∞`. -/
lemma WithBot.ENat.add_natCast_le_of_forall {a b : WithBot ℕ∞} {r : ℕ}
    (h : ∀ e : ℕ, (e : WithBot ℕ∞) ≤ a → (r : WithBot ℕ∞) + e ≤ b) : a + r ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    induction a using ENat.recTopCoe with
    | coe a =>
      rw [add_comm]
      exact_mod_cast h a le_rfl
    | top =>
      induction b using WithBot.recBotCoe with
      | bot => simpa using h 0 (by simp)
      | coe b =>
        induction b using ENat.recTopCoe with
        | top => exact le_top
        | coe b =>
          have := h (b + 1) (by exact_mod_cast le_top)
          norm_cast at this
          omega

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **A projection sending a point to the generic point.** For an affine scheme `U` of finite
type over a field `k` and a point `y ∈ U` whose closure has dimension `r`, there is a morphism
`p : U ⟶ 𝔸ʳ_k` over `k` with `p y` the generic point of `𝔸ʳ_k`. -/
theorem Scheme.exists_hom_mvPolynomial_apply_eq_bot {U : Scheme.{u}} [IsAffine U]
    (aU : U ⟶ Spec (.of k)) [LocallyOfFiniteType aU] (y : U) (r : ℕ)
    (hr : topologicalKrullDim (closure {y} : Set U) = r) :
    ∃ p : U ⟶ Spec (.of (MvPolynomial (Fin r) k)),
      p ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = aU ∧ (p y).asIdeal = ⊥ := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ aU.appTop).hom.toAlgebra
  have : Algebra.FiniteType k Γ(U, ⊤) := finiteType_ΓSpecIso_inv_comp_appTop U aU
  rw [topologicalKrullDim_closure_singleton_of_isAffine] at hr
  obtain ⟨φ, hφ⟩ := exists_algHom_mvPolynomial_comap_eq_bot k Γ(U, ⊤) _ r hr
  refine ⟨U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, hφ⟩
  have hC : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom φ.toRingHom =
      (Scheme.ΓSpecIso (.of k)).inv ≫ aU.appTop := by
    ext x
    exact φ.commutes x
  rw [Category.assoc, ← Spec.map_comp, hC, Spec.map_comp, ← Category.assoc,
    Scheme.isoSpec_hom_naturality]
  simp

/-- **Dimension of the generic fibre.** For a morphism `g : Z ⟶ 𝔸ʳ_k` locally of finite type
and the generic point `η` of `𝔸ʳ_k`, `dim g⁻¹(η) + r ≤ dim Z`: the closure of `η` has
dimension `r` (`Scheme.Hom.topologicalKrullDim_closure_singleton_add_le`). -/
theorem Scheme.Hom.topologicalKrullDim_preimage_add_le_of_asIdeal_eq_bot {Z : Scheme.{u}}
    (r : ℕ) (g : Z ⟶ Spec (.of (MvPolynomial (Fin r) k))) [LocallyOfFiniteType g]
    (η : Spec (.of (MvPolynomial (Fin r) k))) (hη : η.asIdeal = ⊥) :
    topologicalKrullDim (g ⁻¹' {η}) + r ≤ topologicalKrullDim Z := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin r)
      (R := k)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hηr : topologicalKrullDim (closure {η} : Set (Spec (.of (MvPolynomial (Fin r) k)))) = r := by
    rw [PrimeSpectrum.topologicalKrullDim_closure_singleton, hη,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_isField (Field.toIsField k)]
    simp
  refine WithBot.ENat.add_natCast_le_of_forall fun e he ↦ ?_
  have h := Scheme.Hom.topologicalKrullDim_closure_singleton_add_le
    (Spec.map (CommRingCat.ofHom MvPolynomial.C)) g isClosed_univ η e (by rwa [Set.univ_inter])
  rw [hηr] at h
  refine h.trans ?_
  exact (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq.le

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.LinearAlgebra.Matrix.GeneralLinearGroup.LocalLift
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Lifting bases along towers of free modules

- `Module.Basis.ofSpanEqTop`: over a commutative ring, a spanning family indexed like a basis is
  a basis (surjective endomorphisms of finite modules are bijective);
- `Module.Basis.exists_basis_map_eq`: along a surjective semilinear map `M → N` over a
  surjective local homomorphism `R → S`, every basis of `N` lifts to a basis of `M` (via the
  lifting of invertible matrices, `Matrix.GeneralLinearGroup.map_surjective_of_isLocalHom`);
- `Module.Basis.exists_tower`: hence a tower of free modules of constant rank over a tower of
  local rings with surjective transitions (e.g. `𝒪_E ⧸ ℓⁿ`) admits compatible bases, i.e. its
  transitions can be made standard.
-/

@[expose] public section

open Module

variable {ι : Type*}

namespace Module.Basis

variable {R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]

/-- A spanning family indexed like a basis of a module over a commutative ring is a basis. -/
noncomputable def ofSpanEqTop (b : Basis ι R M) (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) : Basis ι R M :=
  (Pi.basisFun R ι).map <| LinearEquiv.ofBijective (Fintype.linearCombination R v) <| by
    have hs : Function.Surjective (Fintype.linearCombination R v) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
    refine ⟨fun x y h ↦ ?_, hs⟩
    have := OrzechProperty.injective_of_surjective_endomorphism
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R v) (b.equivFun.surjective.comp hs)
    exact this (by simp [h])

@[simp]
lemma ofSpanEqTop_apply (b : Basis ι R M) (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤)
    (i : ι) : b.ofSpanEqTop v hv i = v i := by
  classical
  simp [ofSpanEqTop, Fintype.linearCombination_apply, Pi.single_apply]

end Module.Basis

section Lift

variable {R S M N : Type*} [Finite ι] [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] {π : R →+* S} [IsLocalHom π] (hπ : Function.Surjective π)
  {t : M →ₛₗ[π] N} (ht : Function.Surjective t)

include hπ ht in
/-- **Lifting bases along a surjection of free modules over a local surjection of rings**: if
`t : M → N` is a surjective `π`-semilinear map, `π : R → S` a surjective local homomorphism,
and `M` has a basis indexed by `ι`, then every basis of `N` indexed by `ι` lifts along `t` to a
basis of `M`. -/
theorem Module.Basis.exists_basis_map_eq (b : Basis ι R M) (b' : Basis ι S N) :
    ∃ c : Basis ι R M, ∀ i, t (c i) = b' i := by
  have hv : Submodule.span S (Set.range fun i ↦ t (b i)) = ⊤ := by
    have : RingHomSurjective π := ⟨hπ⟩
    rw [Set.range_comp', ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 ht]
  classical
  have := Fintype.ofFinite ι
  let v := b'.ofSpanEqTop _ hv
  let C : Matrix ι ι S := v.toMatrix b'
  have hC : IsUnit C.det := by
    have := v.invertibleToMatrix b'
    exact (Matrix.isUnit_iff_isUnit_det C).1 (isUnit_of_invertible C)
  obtain ⟨D, hD⟩ := Matrix.GeneralLinearGroup.map_surjective_of_isLocalHom π hπ
    (Matrix.nonsingInvUnit C hC)
  have hDC (j k : ι) : π (D j k) = C j k := by
    rw [← Matrix.GeneralLinearGroup.map_apply, hD]
    rfl
  have hDdet : IsUnit (D : Matrix ι ι R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  refine ⟨b.map (Matrix.toLinearEquiv b (D : Matrix ι ι R) hDdet), fun k ↦ ?_⟩
  rw [Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self, map_sum]
  simp_rw [LinearMap.map_smulₛₗ, hDC]
  simpa [v] using v.sum_toMatrix_smul_self b' k

end Lift

/-- **Standardising a tower of free modules**: let `Rₙ` be a tower of commutative rings with
surjective local transitions `πₙ : Rₙ₊₁ → Rₙ` (e.g. `𝒪_E ⧸ ℓⁿ⁺¹`), and `Mₙ` free `Rₙ`-modules
with bases indexed by a common finite `ι`, with surjective `πₙ`-semilinear transitions
`tₙ : Mₙ₊₁ → Mₙ`. Then the bases can be chosen compatibly: `tₙ (cₙ₊₁ i) = cₙ i`, i.e. the tower
is isomorphic to the standard tower `Rₙ^ι`. -/
theorem Module.Basis.exists_tower {R M : ℕ → Type*} [∀ n, CommRing (R n)]
    [∀ n, AddCommGroup (M n)] [∀ n, Module (R n) (M n)] [Finite ι]
    (π : ∀ n, R (n + 1) →+* R n) [∀ n, IsLocalHom (π n)] (hπ : ∀ n, Function.Surjective (π n))
    (t : ∀ n, M (n + 1) →ₛₗ[π n] M n) (ht : ∀ n, Function.Surjective (t n))
    (b : ∀ n, Basis ι (R n) (M n)) :
    ∃ c : ∀ n, Basis ι (R n) (M n), ∀ n i, t n (c (n + 1) i) = c n i := by
  choose L hL using fun n (b' : Basis ι (R n) (M n)) ↦
    Basis.exists_basis_map_eq (hπ n) (ht n) (b (n + 1)) b'
  let c : ∀ n, Basis ι (R n) (M n) := fun n ↦
    Nat.rec (motive := fun n ↦ Basis ι (R n) (M n)) (b 0) (fun n c ↦ L n c) n
  exact ⟨c, fun n i ↦ hL n (c n) i⟩

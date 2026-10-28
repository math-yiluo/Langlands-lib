import Langlands.Algebra.ResidueTensorNilpotentInjectivityStatement
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Tensor

universe u v w z

open TensorProduct LinearMap

namespace Langlands.Algebra

/-- The case of coefficients killed by the maximal ideal. -/
private theorem residueTensor_injective_of_annihilated
    (R : Type u) (A : Type v) (B : Type w) (C : Type z)
    [CommRing R] [IsLocalRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] (f : A →ₗ[R] B)
    (hk : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)))
    (hC : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ c : C, r • c = 0) :
    Function.Injective (f.lTensor C) := by
  let k := IsLocalRing.ResidueField R
  have htor : Module.IsTorsionBySet R C (IsLocalRing.maximalIdeal R) :=
    fun {c} {r} => hC r.1 r.2 c
  let : Module k C := htor.module
  let : IsScalarTower R k C := htor.isScalarTower
  let eA := AlgebraTensorModule.cancelBaseChange R k k C A
  let eB := AlgebraTensorModule.cancelBaseChange R k k C B
  have hg : Function.Injective ((f.baseChange k).lTensor C) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hk
  have hnat (x : C ⊗[R] A) :
      (f.baseChange k).lTensor C (eA.symm x) = eB.symm (f.lTensor C x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c a => simp [eA, eB]
    | add x y hx hy => simp [hx, hy]
  intro x y hxy
  apply eA.symm.injective
  apply hg
  rw [hnat, hnat, hxy]

/-- Induction on the power of the maximal ideal, with the coefficients varying. -/
private theorem residueTensor_injective_of_pow_annihilated
    (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [IsLocalRing R] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Module.Flat R B] (f : A →ₗ[R] B)
    (hk : Function.Injective (f.lTensor (IsLocalRing.ResidueField R))) :
    ∀ (n : ℕ) (C : Type z) [AddCommGroup C] [Module R C],
      (∀ r ∈ IsLocalRing.maximalIdeal R ^ n, ∀ c : C, r • c = 0) →
      Function.Injective (f.lTensor C) := by
  intro n
  induction n with
  | zero =>
      intro C _ _ hC
      have hc (c : C) : c = 0 := by
        simpa using hC 1 (by simp) c
      have ht (x : C ⊗[R] A) : x = 0 := by
        induction x using TensorProduct.inductionOn with
        | tmul c a => rw [hc c]; simp
        | add x y hx hy => simp [hx, hy]
      intro x y _
      rw [ht x, ht y]
  | succ n ih =>
      intro C _ _ hC
      let m := IsLocalRing.maximalIdeal R
      let N : Submodule R C := m • ⊤
      have hpow : m ^ (n + 1) • (⊤ : Submodule R C) = ⊥ := by
        apply le_antisymm
        · apply Submodule.smul_le.mpr
          intro r hr c _
          exact (Submodule.mem_bot R).mpr (hC r hr c)
        · exact bot_le
      have hNpow : m ^ n • N = ⊥ := by
        dsimp [N]
        rw [← Submodule.mul_smul, ← pow_succ, hpow]
      have hN : Function.Injective (f.lTensor N) := by
        apply ih N
        intro r hr c
        apply Subtype.ext
        change r • (c : C) = 0
        have hm := Submodule.smul_mem_smul hr c.property
        rw [hNpow] at hm
        exact (Submodule.mem_bot R).mp hm
      have hQ : Function.Injective (f.lTensor (C ⧸ N)) := by
        apply residueTensor_injective_of_annihilated R A B (C ⧸ N) f hk
        intro r hr c
        obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective N c
        change N.mkQ (r • c) = 0
        apply (Submodule.Quotient.mk_eq_zero N).mpr
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      have hnatQ :
          (f.lTensor (C ⧸ N)).comp (N.mkQ.rTensor A) =
            (N.mkQ.rTensor B).comp (f.lTensor C) := by
        ext
        simp
      have hxQ : (N.mkQ.rTensor A) x = 0 := by
        apply hQ
        rw [map_zero, ← LinearMap.comp_apply, hnatQ, LinearMap.comp_apply, hx, map_zero]
      obtain ⟨y, hy⟩ :=
        (rTensor_exact A (LinearMap.exact_subtype_mkQ N)
          (Submodule.mkQ_surjective N) x).mp hxQ
      have hnatN :
          (N.subtype.rTensor B).comp (f.lTensor N) =
            (f.lTensor C).comp (N.subtype.rTensor A) := by
        ext
        simp
      have hyf : (f.lTensor N) y = 0 := by
        apply Module.Flat.rTensor_preserves_injective_linearMap N.subtype
          (Submodule.injective_subtype N)
        rw [map_zero, ← LinearMap.comp_apply, hnatN, LinearMap.comp_apply, hy, hx]
      have hy0 : y = 0 := hN (by simpa using hyf)
      rw [← hy, hy0, map_zero]

/-- Over a local ring, if `B` is flat and `k ⊗ f` is injective for the residue
field `k`, then `C ⊗ f` is injective for every `C` killed by a power of the
maximal ideal. -/
theorem residueTensorNilpotentInjectivity :
    ResidueTensorNilpotentInjectivityStatement.{u,v,w,z} := by
  intro R A B C _ _ _ _ _ _ _ _ f n hB hk hC
  let : Module.Flat R B := hB
  exact residueTensor_injective_of_pow_annihilated R A B f hk n C hC

end Langlands.Algebra

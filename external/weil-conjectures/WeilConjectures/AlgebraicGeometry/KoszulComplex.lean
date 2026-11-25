/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Koszul complex of a finite sequence

Source: literature/stacks-project/more-algebra.tex, Definitions Tags 0622 and 0623
(blueprint: def-weil-pbc-koszul-complex).

## Main definitions

* `ExteriorAlgebra.koszulComplex`: the exterior powers `⋀[R]^n (Fin r →₀ R)` with the
  differential `CliffordAlgebra.contractLeft` at the zero quadratic form (STATE KOSZUL),
  a chain complex indexed by `ℕ` (the terms in negative degrees are zero by the
  extension convention of def-weil-pbc-module-chain-complex-homology).
* `ExteriorAlgebra.koszulComplexTensor`: its degreewise tensor product with a module.

The exterior-algebra multiplication and the graded Leibniz rule of
`koszul_differential` give the commutative differential graded algebra of Tag 0622.
Homology is the existing `HomologicalComplex.homology`, identified with kernel
modulo image by `ShortComplex.moduleCatHomologyIso`, with no separate convention.
The bases and degree-zero/one identifications are Mathlib's
`Module.Basis.exteriorPower`, `exteriorPower.zeroEquiv`, and `exteriorPower.oneEquiv`
(lem-weil-pbc-exterior-power-free-basis).
-/

@[expose] public section

universe u v

open scoped TensorProduct
open CategoryTheory

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R] (r : ℕ)

/-- Contraction with `φ = Finsupp.linearCombination R f` maps the exterior power of degree
`n + 1` into the exterior power of degree `n`. Source: Stacks, Tag 0622
(blueprint: def-weil-pbc-koszul-complex).

Proof: the unique differential `D` of `lem-weil-pbc-koszul-differential` is
`CliffordAlgebra.contractLeft` at the zero quadratic form (`contractLeft_one` and
`contractLeft_ι_mul` are its two defining equations, so uniqueness identifies them);
its degree clause `D(⋀^(n+1)) ⊆ ⋀^n` is the claim. -/
theorem koszul_contract_mem (f : Fin r → R) (n : ℕ) (x : ⋀[R]^(n + 1) (Fin r →₀ R)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R)))
      (Finsupp.linearCombination R f) (x : ExteriorAlgebra R (Fin r →₀ R)) ∈
        ⋀[R]^n (Fin r →₀ R) := by
  obtain ⟨D, hD1, hrec, huniq, hgen, hzero, hdeg, hform, hleib, hderivuniq⟩ :=
    koszul_differential R (Fin r →₀ R)
      (Finsupp.linearCombination R f)
  have hcontract : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm R (Fin r →₀ R)))
      (Finsupp.linearCombination R f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one
        (0 : QuadraticForm R (Fin r →₀ R)) (Finsupp.linearCombination R f)
    · intro v y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R (Fin r →₀ R)))
          (Finsupp.linearCombination R f) v y
  rw [hcontract]
  exact hdeg n (Submodule.mem_map_of_mem x.property)

/-- The Koszul differential `d_{n+1} : ⋀^(n+1) E → ⋀^n E`, the restriction of
contraction with `φ`, `φ(e_i) = f i`. Source: Stacks, Tags 0622/0623
(blueprint: def-weil-pbc-koszul-complex). -/
noncomputable def koszulBoundary (f : Fin r → R) (n : ℕ) :
    ⋀[R]^(n + 1) (Fin r →₀ R) →ₗ[R] ⋀[R]^n (Fin r →₀ R) :=
  LinearMap.codRestrict (⋀[R]^n (Fin r →₀ R))
    ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R)))
      (Finsupp.linearCombination R f)).comp (⋀[R]^(n + 1) (Fin r →₀ R)).subtype)
    (koszul_contract_mem R r f n)

/-- The restricted differentials compose to zero. Source: Stacks, Tag 0622
(blueprint: def-weil-pbc-koszul-complex).

Proof: the inclusions of the exterior powers into the exterior algebra are injective;
after inclusion the composite is the square of contraction, which vanishes by
Mathlib's `CliffordAlgebra.contractLeft_contractLeft`. -/
theorem koszulBoundary_comp (f : Fin r → R) (n : ℕ) :
    ModuleCat.ofHom (koszulBoundary R r f (n + 1)) ≫
      ModuleCat.ofHom (koszulBoundary R r f n) = 0 := by
  ext x
  exact CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm R (Fin r →₀ R)))
    (Finsupp.linearCombination R f) (x : ExteriorAlgebra R (Fin r →₀ R))

/-- The Koszul complex `K_•(f_1, …, f_r)` of a finite sequence in a commutative ring:
`K_n = ⋀^n_R (R^{⊕r})` with `E = Fin r →₀ R`, and differential the restriction of
contraction with the linear form sending the standard basis vector `i` to `f i`.
Source: Stacks, Tags 0622/0623 (blueprint: def-weil-pbc-koszul-complex). -/
noncomputable def koszulComplex
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n (Fin r →₀ R)))
    (fun n ↦ ModuleCat.ofHom (koszulBoundary R r f n)) (koszulBoundary_comp R r f)

/-- Tensoring the Koszul differentials with the identity of `M` still gives square zero.
Source: Stacks, Tag 0623 (blueprint: def-weil-pbc-koszul-complex).

Proof: by `def-weil-pbc-module-tensor-product`, the composite of `rTensor` maps is the
`rTensor` of the composite and `rTensor` sends zero to zero; apply
`koszulBoundary_comp`. -/
theorem koszulBoundary_rTensor_comp (f : Fin r → R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    ModuleCat.ofHom ((koszulBoundary R r f (n + 1)).rTensor M) ≫
      ModuleCat.ofHom ((koszulBoundary R r f n).rTensor M) = 0 := by
  have h : (koszulBoundary R r f n).comp (koszulBoundary R r f (n + 1)) = 0 := by
    exact congrArg ModuleCat.Hom.hom (koszulBoundary_comp R r f n)
  apply ModuleCat.hom_ext
  change ((koszulBoundary R r f n).rTensor M).comp
    ((koszulBoundary R r f (n + 1)).rTensor M) = 0
  rw [← LinearMap.rTensor_comp, h, LinearMap.rTensor_zero]

/-- The degreewise tensor product `K_•(f) ⊗_R M`, terms `K_n ⊗_R M`, differentials
`d_n ⊗ id_M`. Source: Stacks, Tag 0623 and the tensor convention of the node
(blueprint: def-weil-pbc-koszul-complex). -/
noncomputable def koszulComplexTensor (f : Fin r → R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n (Fin r →₀ R) ⊗[R] M))
    (fun n ↦ ModuleCat.ofHom ((koszulBoundary R r f n).rTensor M))
    (koszulBoundary_rTensor_comp R r f M)

end ExteriorAlgebra

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.Topology.Algebra.Group.PowSurjective

/-!

# `n`-th roots in Galois groups of degree prime to `n`

Let `L / K` be a Galois extension, possibly infinite, such that every finite Galois subextension
`E / K` has degree prime to `n`, e.g. a pro-`p` extension and `n` prime to `p`. Then every element
of `Gal(L / K)` is an `n`-th power (`IsGalois.exists_pow_eq_of_coprime`): `Gal(L / K)` is compact
for the Krull topology, and the open normal subgroups `Gal(L / E)` form a basis of neighbourhoods
of `1` with quotients `Gal(E / K)` (`exists_pow_eq_of_forall_nhds_one`). The same holds for the
separable closure of `K` in a normal extension (`IsGalois.exists_pow_eq_separableClosure`).

-/

@[expose] public section

open IntermediateField

namespace IsGalois

/-- **`n`-th roots in Galois groups of degree prime to `n`**: if every finite Galois subextension
of the Galois extension `L / K` has degree prime to `n`, every element of `Gal(L / K)` is an
`n`-th power. -/
theorem exists_pow_eq_of_coprime {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {n : ℕ} (h : ∀ E : IntermediateField K L, FiniteDimensional K E → IsGalois K E →
      (Module.finrank K E).Coprime n) (σ : Gal(L/K)) : ∃ τ, τ ^ n = σ := by
  refine exists_pow_eq_of_forall_nhds_one (fun U hU ↦ ?_) σ
  obtain ⟨E, hfin, hnorm, hEU⟩ := (krullTopology_mem_nhds_one_iff_of_normal K L U).1 hU
  have : IsGalois K E := ⟨⟩
  have hN : E.fixingSubgroup.Normal := E.restrictNormalHom_ker ▸ MonoidHom.normal_ker _
  refine ⟨E.fixingSubgroup, hN, hEU, ?_⟩
  have e : Gal(L/K) ⧸ E.fixingSubgroup ≃* Gal(E/K) :=
    (QuotientGroup.quotientMulEquivOfEq E.restrictNormalHom_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective L))
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
  exact h E hfin this

/-- **`n`-th roots in the Galois group of a separable closure**: if every finite Galois
subextension of the normal extension `E / F` has degree prime to `n`, every element of
`Gal(F^sep / F)`, for the separable closure `F^sep` of `F` in `E`, is an `n`-th power. The
finite Galois subextensions of `F^sep / F` are those of `E / F`. -/
theorem exists_pow_eq_separableClosure {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Normal F E] {n : ℕ}
    (h : ∀ M : IntermediateField F E, FiniteDimensional F M → IsGalois F M →
      (Module.finrank F M).Coprime n) (σ : Gal(separableClosure F E / F)) :
    ∃ τ, τ ^ n = σ := by
  refine exists_pow_eq_of_coprime (fun M _ _ ↦ ?_) σ
  let e := M.equivMap (separableClosure F E).val
  have : FiniteDimensional F (M.map (separableClosure F E).val) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  have : IsGalois F (M.map (separableClosure F E).val) := IsGalois.of_algEquiv e
  rw [e.toLinearEquiv.finrank_eq]
  exact h _ inferInstance inferInstance

end IsGalois

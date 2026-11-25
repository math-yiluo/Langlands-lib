/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.NormalSmooth
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne

/-!
# Rank-one Weil characters on normal curves over a finite field

The blueprint states `proposition-no-fixed-class-degree-one--1` and
`theorem-rank-one-sheaves-have-finite--1` for a curve `U₀ / 𝔽_q` which is normal,
geometrically connected, separated, of finite type and pure of dimension one. Such a curve is
smooth of relative dimension one over the perfect field `𝔽_q`
(`AlgebraicGeometry.IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk`), so
these statements follow from their versions for smooth curves:
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso`,
`AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant`,
`AlgebraicGeometry.WeilGroup.exists_pow_eq_one_of_continuous` and
`AlgebraicGeometry.WeilGroup.finite_range_of_continuous`. The link of the Weil group with the
étale fundamental group of the geometric curve is automatic
(`AlgebraicGeometry.WeilGroup.isEtaleQuotient`).

Normality is expressed by asking the local rings of `U₀` to be integrally closed domains, pure
dimension one by `topologicalKrullDim U₀ = 1` (`U₀` being irreducible, as it is connected and
normal), and separatedness and finite type by `AlgebraicGeometry.IsCurve`.

## Main statements

- `Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso_of_isIntegrallyClosed_stalk`
- `AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant_of_isIntegrallyClosed_stalk`
- `AlgebraicGeometry.WeilGroup.exists_pow_eq_one_of_continuous_of_isIntegrallyClosed_stalk`
- `AlgebraicGeometry.WeilGroup.finite_range_of_continuous_of_isIntegrallyClosed_stalk`
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry

namespace Scheme.EtaleTorsor

open FiniteEtale

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: No Frobenius-fixed compatible class
on an open normal curve.

Let `U₀` be a normal geometrically connected curve of pure dimension one over a finite field
`K = 𝔽_q` (its local rings are integrally closed domains and `dim U₀ = 1`), let
`U = U₀ ×_K K̄` be its geometric fibre with geometric point `s` and fundamental group
`G = π₁(U, s)`, and let `ℓ ≠ char K`. A compatible system of classes
`(z_n) ∈ lim_n H¹(U, ℤ / ℓⁿ)`, all of which are fixed by the Frobenius, is zero: every torsor
`t n` has a section. The curve `U₀` is smooth over `K`
(`AlgebraicGeometry.IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk`), so this
is `AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso`. -/
theorem exists_section_of_isIsomorphic_mapIso_of_isIntegrallyClosed_stalk {K : Type u} [Field K]
    [Finite K] {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p] [GeometricallyConnected p]
    (hU : ∀ x : U, IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x))
    (hdim : topologicalKrullDim U = 1) (l : ℕ) [Fact l.Prime] [Fact (ringChar K ≠ l)]
    [ConnectedSpace p.geometricFiber] (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (t : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) p.geometricFiber)
    (ht : ∀ n g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
      ((t (n + 1)).monodromy s G g).toAdd.down = ((t n).monodromy s G g).toAdd.down)
    (hfix : ∀ n, ((t n).mapIso p.geometricGaloisFrobenius.asIso).IsIsomorphic (t n)) (n : ℕ) :
    ∃ σ : p.geometricFiber ⟶ (t n).P, σ ≫ (t n).π = 𝟙 _ :=
  have := IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk p hU hdim
  exists_section_of_isIsomorphic_mapIso p l s G t ht hfix n

end Scheme.EtaleTorsor

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] (W : WeilGroup p) {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (hC : ∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x))
  (hdim : topologicalKrullDim C = 1)

include hC hdim

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`, the cohomological step, for a
normal geometrically connected curve `C₀ / 𝔽_q` of pure dimension one: a continuous
homomorphism `b : π₁(C) → ℤ_ℓ` invariant under conjugation by the Frobenius lift is trivial.
The curve is smooth
(`AlgebraicGeometry.IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk`),
so this is `AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant`. -/
theorem eq_one_of_conj_invariant_of_isIntegrallyClosed_stalk
    (b : W.geometric →ₜ* Multiplicative ℤ_[l])
    (hb : ∀ g h : W.geometric, (h : W.carrier) = W.frobeniusLift⁻¹ * g * W.frobeniusLift →
      b h = b g) :
    b = 1 :=
  have := IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk p hC hdim
  W.eq_one_of_conj_invariant b hb

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: Finite geometric image of a
rank-one Weil character on a curve.

Let `C₀ / 𝔽_q` be normal, geometrically connected, separated, of finite type and pure of
dimension one. A continuous character `χ : W(C₀) → ℚ̄_ℓˣ` has finite geometric image: there is
`N ≥ 1` with `χ (g) ^ N = 1` for every `g ∈ π₁(C)`. -/
theorem exists_pow_eq_one_of_continuous_of_isIntegrallyClosed_stalk
    (χ : W.carrier →* (PadicAlgCl l)ˣ)
    (hχ : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l)) :
    ∃ N : ℕ, 0 < N ∧ ∀ g : W.geometric, χ g ^ N = 1 :=
  have := IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk p hC hdim
  W.exists_pow_eq_one_of_continuous χ hχ

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: Finite geometric image of a
rank-one Weil character on a curve.

Let `C₀ / 𝔽_q` be normal, geometrically connected, separated, of finite type and pure of
dimension one. A continuous character `χ : W(C₀) → ℚ̄_ℓˣ` takes finitely many values on
`π₁(C)`. -/
theorem finite_range_of_continuous_of_isIntegrallyClosed_stalk
    (χ : W.carrier →* (PadicAlgCl l)ˣ)
    (hχ : Continuous fun g : W.geometric ↦ (χ g : PadicAlgCl l)) :
    (Set.range fun g : W.geometric ↦ χ g).Finite :=
  have := IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk p hC hdim
  W.finite_range_of_continuous χ hχ

end WeilGroup

end AlgebraicGeometry

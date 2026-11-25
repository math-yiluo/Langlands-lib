/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Instances.ZMod
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Counting characters of the fundamental group of a curve

Let `C₀` be a proper smooth curve over a field `K` whose geometric fibre `C = C₀ ×_K K̄` is
connected, let `G = π₁(C, s)` and let `l ≠ char K` be a prime. The identification
`H¹(C_ét, ℤ / lᵏ) ≃ Hom_cont(G, ℤ / lᵏ)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`) and the curve estimate
`H¹(C_ét, ℤ / lᵏ) ≅ (ℤ / lᵏ)^{2g}`
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`)
show that `G` has exactly `l ^ (2 g k)` continuous characters with values in `ℤ / lᵏ`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_card_continuousMonoidHom_zmod_eq`). This is the
counting hypothesis of `ContinuousMonoidHom.exists_surjective_of_card_eq`.

The geometric fibre is a connected curve over `K̄`
(`AlgebraicGeometry.Scheme.Hom.isConnectedCurve_geometricFiberToAlgebraicClosure`): it is smooth
of relative dimension one, hence of dimension one.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- The geometric fibre of a proper scheme `C₀` smooth of relative dimension one over `K` with
connected geometric fibre is a connected curve over `K̄`: being smooth of relative dimension one
and nonempty, it has dimension one. -/
lemma Scheme.Hom.isConnectedCurve_geometricFiberToAlgebraicClosure (p : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 p] [IsProper p] [ConnectedSpace p.geometricFiber] :
    IsConnectedCurve p.geometricFiberToAlgebraicClosure := by
  set q := p.geometricFiberToAlgebraicClosure
  have : SmoothOfRelativeDimension 1 q :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd p _))
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p _))
  exact
    { krullDim_le_one := by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension q 1
      connectedSpace := inferInstance
      krullDim_eq_one := by
        exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension q 1 }

namespace Scheme.EtaleTorsor

open FiniteEtale

/-- **Characters of the geometric fundamental group of a curve.** Let `C₀` be a proper scheme
smooth of relative dimension one over a field `K` with connected geometric fibre `C`, let
`G = π₁(C, s)` and let `l ≠ char K` be a prime. Then there is `r` (namely `2 g`) such that `G`
has exactly `l ^ (r k)` continuous characters with values in `ℤ / lᵏ`, for every `k`: they are
the elements of `H¹(C_ét, ℤ / lᵏ) ≅ (ℤ / lᵏ)^{2g}`. -/
theorem exists_card_continuousMonoidHom_zmod_eq (p : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 p] [IsProper p] (l : ℕ) [Fact l.Prime] [Fact (ringChar K ≠ l)]
    [ConnectedSpace p.geometricFiber] (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G] :
    ∃ r, ∀ k, Nat.card (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ k)))) = l ^ (r * k) := by
  set q := p.geometricFiberToAlgebraicClosure
  have hl : l.Prime := Fact.out
  have : IsConnectedCurve q := p.isConnectedCurve_geometricFiberToAlgebraicClosure
  have : SmoothOfRelativeDimension 1 q :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd p _))
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p _))
  -- `l` is invertible in `K`, hence in `K̄`
  have hlK : (l : K) ≠ 0 := fun h ↦ by
    rcases hl.eq_one_or_self_of_dvd _ ((ringChar.spec K l).1 h) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact (Fact.out : ringChar K ≠ l) h1
  refine ⟨2 * q.genus, fun k ↦ ?_⟩
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hk : ((l ^ k : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Nat.cast_pow, ← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact pow_ne_zero _ ((map_ne_zero _).2 hlK)
  obtain ⟨e⟩ := IsCurve.nonempty_addEquiv_sheafH_constantZMod_one q (l ^ k) hk
  let e' : (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ k)))) ≃
      (Fin (2 * q.genus) → ZMod (l ^ k)) :=
    (sheafHEquivContinuousMonoidHom (ULift.{u + 1} (ZMod (l ^ k))) s G).symm.trans e.toEquiv
  rw [Nat.card_congr e', Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, mul_comm]

end Scheme.EtaleTorsor

end AlgebraicGeometry

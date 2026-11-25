/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms

/-!
# The geometric part of a Weil group and the étale fundamental group of the geometric curve

An `AlgebraicGeometry.WeilGroup` is presented through the étale fundamental group
`π₁(C₀, s)` of the curve `C₀` over `K`, and its geometric part `ker deg` is the kernel of
`π₁(C₀, s) → Gal(K̄ / K)`. That this kernel is the étale fundamental group of the *geometric*
curve `C = C₀ ×_K K̄` is the homotopy exact sequence. The rank-one purity statements of
`theorem-rank-one-sheaves-have-finite` use the geometric curve: they compare Frobenius-fixed classes
in `H¹(C, ℤ / ℓⁿ)` with homomorphisms on `ker deg`.

This file states that identification as `AlgebraicGeometry.WeilGroup.IsEtaleQuotient`: the
geometric part of `W` is isomorphic, as a topological group, to a fundamental group
`G = π₁(C, s)` of the geometric curve, compatibly with the Frobenius. Every Weil group of a
geometrically connected curve satisfies it, by the homotopy exact sequence
(`AlgebraicGeometry.WeilGroup.isEtaleQuotient`).

From it, the cohomological vanishing `lim_n H¹(C, ℤ / ℓⁿ)^{Φ = 1} = 0`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso`) yields the
group-theoretic statement used for rank-one sheaves: a continuous homomorphism
`π₁(C) → ℤ_ℓ` invariant under conjugation by the Frobenius lift is trivial
(`AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant`).

## Main definitions

- `AlgebraicGeometry.WeilGroup.EtaleQuotientData`: an identification of the geometric part of a
  Weil group with the étale fundamental group of the geometric curve, compatible with the
  Frobenius.
- `AlgebraicGeometry.WeilGroup.IsEtaleQuotient`: such a presentation exists.

## Main statements

- `AlgebraicGeometry.WeilGroup.eq_one_of_conj_invariant`
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

open Scheme.FiniteEtale in
/-- Blueprint `situation-weil`: the Weil group of a curve, its link with the étale
fundamental group.

An identification of the geometric part `W.geometric = ker deg` of a Weil group with the étale
fundamental group of the geometric curve `C = C₀ ×_K K̄`, compatible with the Frobenius. It
consists of

* a geometric point `s` of `C` and a fundamental group `G = π₁(C, s)` of the fibre functor
  `F_s` on finite étale `C`-schemes;
* an isomorphism of topological groups `π : G ≃ W.geometric`;
* a transport `τ : F_s ∘ g_* ≅ F_s` of the fibre functor along the geometric Galois Frobenius
  `g` of `C`, with the induced map `σ : G → G`, `τ (h • x) = σ h • τ x`;
* an element `w` of degree `± 1` of `W` with `π (σ h) = w π(h) w⁻¹`.

For the Weil group `W(C₀, s) ⊆ π₁(C₀, s)` itself, `π` is the identity of `π₁(C, s)`, `τ` is the
action of a lift `γ` of Frobenius on fibres, and `w = γ ^ (± 1)`, the sign depending on the
conventions for `γ` and `g`. -/
structure EtaleQuotientData (W : WeilGroup p) where
  /-- The geometric curve is connected. -/
  [connectedSpace : ConnectedSpace p.geometricFiber]
  /-- The geometric point `s` of `C`. -/
  point : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber
  /-- The étale fundamental group `π₁(C, s)`. -/
  G : Type u
  [group : Group G]
  [topologicalSpace : TopologicalSpace G]
  [isTopologicalGroup : IsTopologicalGroup G]
  [compactSpace : CompactSpace G]
  [mulAction (P : p.geometricFiber.FiniteEtale) : MulAction G ((fiber point).obj P)]
  [isFundamentalGroup : IsFundamentalGroup (fiber point) G]
  /-- The identification `π₁(C, s) ≃ W.geometric`. -/
  toGeometric : G ≃ₜ* W.geometric
  /-- The transport of the fibre functor along the geometric Galois Frobenius of `C`. -/
  frobeniusTransport : mapIso p.geometricGaloisFrobenius.asIso ⋙ fiber point ≅ fiber point
  /-- The action of the Frobenius on `π₁(C, s)` induced by the transport. -/
  frobeniusConj : G → G
  frobeniusTransport_smul (P : p.geometricFiber.FiniteEtale) (g : G)
    (x : (fiber point).obj ((mapIso p.geometricGaloisFrobenius.asIso).obj P)) :
    frobeniusTransport.hom.app P (g • x) = frobeniusConj g • frobeniusTransport.hom.app P x
  /-- On `W.geometric`, the Frobenius action is conjugation by an element of degree `± 1`. -/
  exists_conj : ∃ w : W.carrier,
    (W.deg w = Multiplicative.ofAdd 1 ∨ W.deg w = Multiplicative.ofAdd (-1)) ∧
      ∀ g, (toGeometric (frobeniusConj g) : W.carrier) = w * toGeometric g * w⁻¹

attribute [instance] EtaleQuotientData.group
  EtaleQuotientData.topologicalSpace EtaleQuotientData.isTopologicalGroup
  EtaleQuotientData.compactSpace EtaleQuotientData.mulAction
  EtaleQuotientData.isFundamentalGroup

/-- Blueprint `situation-weil`: the Weil group of a curve, its link with the étale
fundamental group.

The geometric part of the Weil group `W` is, Frobenius-equivariantly, the étale fundamental
group of the geometric curve (`AlgebraicGeometry.WeilGroup.EtaleQuotientData`). -/
class IsEtaleQuotient (W : WeilGroup p) : Prop where
  nonempty_etaleQuotientData : Nonempty W.EtaleQuotientData

variable (W : WeilGroup p) {l : ℕ} [Fact l.Prime]

/-- A homomorphism on the geometric part which is invariant under conjugation by the Frobenius
lift is invariant under conjugation by every element of `W`: elements of `W` are products of
geometric elements and powers of the Frobenius lift, and conjugation by a geometric element
does not change a homomorphism to an abelian group. -/
theorem conj_invariant_of_conj_invariant_frobeniusLift {A : Type*} [CommGroup A]
    (b : W.geometric →* A)
    (hb : ∀ g h : W.geometric, (h : W.carrier) = W.frobeniusLift⁻¹ * g * W.frobeniusLift →
      b h = b g)
    (w : W.carrier) (g h : W.geometric) (hgh : (h : W.carrier) = w * g * w⁻¹) : b h = b g := by
  set γ := W.frobeniusLift
  have hnormal : W.geometric.Normal := W.deg.normal_ker
  have hpow : ∀ (n : ℤ) (g h : W.geometric), (h : W.carrier) = γ ^ n * g * (γ ^ n)⁻¹ →
      b h = b g := by
    intro n
    induction n using Int.induction_on with
    | zero => intro g h hgh; simp only [zpow_zero, one_mul, inv_one, mul_one] at hgh;
              rw [Subtype.ext hgh]
    | succ n ih =>
      intro g h hgh
      let k : W.geometric := ⟨γ ^ (n : ℤ) * g * (γ ^ (n : ℤ))⁻¹, hnormal.conj_mem g g.2 _⟩
      rw [← ih g k rfl]
      refine (hb h k ?_).symm
      simp only [k, hgh, zpow_add_one, mul_inv_rev]
      group
    | pred n ih =>
      intro g h hgh
      let k : W.geometric := ⟨γ ^ (-n : ℤ) * g * (γ ^ (-n : ℤ))⁻¹, hnormal.conj_mem g g.2 _⟩
      rw [← ih g k rfl]
      refine hb k h ?_
      simp only [k, hgh, zpow_sub_one, mul_inv_rev]
      group
  set n := Multiplicative.toAdd (W.deg w)
  have hc : w * (γ ^ n)⁻¹ ∈ W.geometric := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, W.deg_frobeniusLift, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact mul_inv_cancel _
  let c : W.geometric := ⟨_, hc⟩
  let k : W.geometric := ⟨γ ^ n * g * (γ ^ n)⁻¹, hnormal.conj_mem g g.2 _⟩
  have hh : h = c * k * c⁻¹ := Subtype.ext <| by
    simp only [c, k, hgh, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hh, map_mul, map_mul, map_inv, mul_inv_cancel_comm, hpow n g k rfl]

/-- Blueprint `theorem-rank-one-sheaves-have-finite--1`: the cohomological step.

Let `W` be the Weil group of a smooth geometrically connected curve `C₀ / 𝔽_q`, linked to the
étale fundamental group (`AlgebraicGeometry.WeilGroup.IsEtaleQuotient`), and `ℓ ≠ char 𝔽_q`.
A continuous homomorphism `b : π₁(C) → ℤ_ℓ` invariant under conjugation by the Frobenius lift
is trivial. Its reductions modulo `ℓⁿ` are classes in `H¹(C, ℤ / ℓⁿ) = Hom_cont(π₁(C), ℤ / ℓⁿ)`
(blueprints `lemma-invariant-additive-characters`) which are fixed
by the Frobenius and compatible in `n`; by blueprint `proposition-no-fixed-class-degree-one--1`
they vanish. -/
theorem eq_one_of_conj_invariant [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient] (b : W.geometric →ₜ* Multiplicative ℤ_[l])
    (hb : ∀ g h : W.geometric, (h : W.carrier) = W.frobeniusLift⁻¹ * g * W.frobeniusLift →
      b h = b g) :
    b = 1 := by
  obtain ⟨D⟩ := ‹W.IsEtaleQuotient›.nonempty_etaleQuotientData
  have := D.connectedSpace
  let b' : D.G →ₜ* Multiplicative ℤ_[l] :=
    b.comp (ContinuousMonoidHom.toContinuousMonoidHom D.toGeometric)
  have hb' (g : D.G) : b' (D.frobeniusConj g) = b' g := by
    obtain ⟨w, -, hw⟩ := D.exists_conj
    exact conj_invariant_of_conj_invariant_frobeniusLift W b.toMonoidHom hb w _ _ (hw g)
  -- the reductions of `b'` modulo `ℓⁿ`, with values in a group of the universe of torsors
  let f := (PadicInt.continuousMonoidHomEquiv l D.G b').1
  let up (n : ℕ) :
      Multiplicative (ZMod (l ^ n)) →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ n))) :=
    { toMonoidHom := (AddEquiv.ulift.symm : ZMod (l ^ n) ≃+ _).toAddMonoidHom.toMultiplicative
      continuous_toFun := continuous_of_discreteTopology }
  have hf (n : ℕ) (g : D.G) : f n (D.frobeniusConj g) = f n g := by
    apply Multiplicative.toAdd.injective
    simp only [f, PadicInt.continuousMonoidHomEquiv_apply_coe, hb']
  choose t ht using fun n ↦
    Scheme.EtaleTorsor.exists_monodromy_eq D.point D.G ((up n).comp (f n))
  have hcompat (n : ℕ) (g : D.G) : ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1))
      (ZMod (l ^ n)) ((t (n + 1)).monodromy D.point D.G g).toAdd.down =
        ((t n).monodromy D.point D.G g).toAdd.down := by
    rw [ht, ht]
    exact ((PadicInt.continuousMonoidHomEquiv l D.G b').2 n g)
  have hfix (n : ℕ) : ((t n).mapIso p.geometricGaloisFrobenius.asIso).IsIsomorphic (t n) := by
    refine Scheme.EtaleTorsor.isIsomorphic_of_monodromy_eq D.point D.G ?_
    ext g
    rw [Scheme.EtaleTorsor.monodromy_mapIso D.point D.G _ D.frobeniusTransport D.frobeniusConj
      D.frobeniusTransport_smul, ht]
    simp only [ContinuousMonoidHom.comp_toFun, hf]
  have htriv (n : ℕ) (g : D.G) : f n g = 1 := by
    obtain ⟨σ, hσ⟩ := Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso p l D.point D.G
      t hcompat hfix n
    have h1 := congrArg (fun φ ↦ (φ g).toAdd.down)
      ((t n).monodromy_eq_one_of_section D.point D.G hσ)
    rw [ht] at h1
    exact Multiplicative.toAdd.injective h1
  have hb'1 : b' = 1 := by
    refine ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective ?_
    refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
    have h := congrArg Multiplicative.toAdd (htriv n g)
    rw [PadicInt.continuousMonoidHomEquiv_apply_coe] at h
    simpa using h
  refine ContinuousMonoidHom.ext fun g ↦ ?_
  obtain ⟨g', rfl⟩ := D.toGeometric.surjective g
  exact congrArg (fun φ ↦ (φ g').toAdd) hb'1

end WeilGroup

end AlgebraicGeometry

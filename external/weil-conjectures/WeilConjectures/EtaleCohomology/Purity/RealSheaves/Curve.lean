/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup

/-!
# Purity of Weil sheaves on actual curves

For a geometrically connected curve `C₀` over a finite field, the geometric part of every Weil
group `W` of `C₀` is the étale fundamental group of the geometric curve, Frobenius-equivariantly
(the homotopy exact sequence, `AlgebraicGeometry.WeilGroup.isEtaleQuotient`). This is the
hypothesis `AlgebraicGeometry.WeilGroup.IsEtaleQuotient` of the purity theorems of
`theorem-rank-one-sheaves-have-finite`, `proposition-bound-largest-determinant-weight--1` and
`theorem-purity-real-sheaves-curves--1`. Since it is an instance, those theorems apply as stated to
every Weil group of a smooth geometrically connected curve, for instance to
`AlgebraicGeometry.WeilGroup.ofFundamentalGroup`.

## Main statements

- `AlgebraicGeometry.WeilGroup.isEtaleQuotient`: the homotopy exact sequence
  `1 → π₁(C) → π₁(C₀) → Gal(𝔽̄_q / 𝔽_q) → 1`, in the form of
  `AlgebraicGeometry.WeilGroup.IsEtaleQuotient`.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K)) [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] (s : Spec (.of (AlgebraicClosure K)) ⟶ C)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- **The homotopy exact sequence** (Stacks `0BTX`, SGA 1 IX.6.1): for a geometrically connected
curve `C₀` over a finite field `𝔽_q`, the geometric part `ker deg` of a Weil group
`W(C₀, s) ⊆ π₁(C₀, s) × ℤ`, that is the kernel of `π₁(C₀, s) → Gal(𝔽̄_q / 𝔽_q)`, is the étale
fundamental group of the geometric curve `C = C₀ ×_{𝔽_q} 𝔽̄_q`, Frobenius-equivariantly.

The map `π₁(C, t) → π₁(C₀, s)` at a `𝔽̄_q`-rational point `t` of `C` lands in `ker deg`
(`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_fundamentalGroupMap`), is injective
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_injective_geometricFiber`), with image
`ker deg` (`AlgebraicGeometry.Scheme.FiniteEtale.mem_range_fundamentalGroupMap_of_mem_weilGroup`),
and a homeomorphism onto it since `π₁(C, t)` is compact. The Frobenius acts on `π₁(C, t)` through
conjugation by an element of degree one
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_transportConj`,
`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_frobeniusElement`). -/
instance isEtaleQuotient (W : WeilGroup p) : W.IsEtaleQuotient := by
  have := W.connectedSpace
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated p
  have : ConnectedSpace p.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := p)
      (Scheme.specAlgebraicClosure K).hom p.geometricFiberProj
      p.geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Nonempty p.geometricFiber := inferInstance
  obtain ⟨t, ht⟩ := p.geometricFiberToAlgebraicClosure.exists_comp_eq_id_of_isAlgClosed
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup t
  have : ∀ P, ContinuousSMul G' ((fiber t).obj P) := fun P ↦ IsFundamentalGroup.continuous_smul P
  have : T2Space W.fundamentalGroup :=
    (toAutHomeo (fiber W.basePoint) W.fundamentalGroup).isEmbedding.t2Space
  have : T2Space W.geometric := W.isEmbedding_ker.t2Space
  let τ : pullback p.geometricFiberProj ⋙ fiber t ≅ fiber W.basePoint :=
    pullbackFiberIso p.geometricFiberProj t ≪≫
      (nonempty_iso_of_fiberFunctor (fiber (t ≫ p.geometricFiberProj))
        (fiber W.basePoint)).some
  let τF := (nonempty_mapIso_fiber_iso t p.geometricGaloisFrobenius.asIso).some
  let ρ := fundamentalGroupMap τ G' W.fundamentalGroup
  let ψ : G' →* weilGroup p W.basePoint W.fundamentalGroup :=
    (ρ.prod (1 : G' →* Multiplicative ℤ)).codRestrict _ fun k ↦
      mem_weilGroup_fundamentalGroupMap p ht τ W.fundamentalGroup G' k
  let f : G' →* W.geometric :=
    (W.weilGroupEquiv.symm.toMonoidHom.comp ψ).codRestrict W.geometric fun k ↦ by
      rw [MonoidHom.mem_ker, W.deg_eq]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      rfl
  have hf (k : G') : (W.weilGroupEquiv (f k) : W.fundamentalGroup × Multiplicative ℤ) =
      (ρ k, 1) := by
    simp [f, ψ]
  have hinj : Function.Injective f := fun k k' h ↦ by
    have h' := congrArg (fun w ↦ (W.weilGroupEquiv w : W.fundamentalGroup × Multiplicative ℤ))
      (congrArg Subtype.val h)
    simp only [hf] at h'
    exact fundamentalGroupMap_injective_geometricFiber p τ G' W.fundamentalGroup
      (congrArg Prod.fst h')
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    have h1 : (W.weilGroupEquiv w : W.fundamentalGroup × Multiplicative ℤ).2 = 1 :=
      (W.deg_eq w).symm.trans hw
    have hmem : ((W.weilGroupEquiv w : W.fundamentalGroup × Multiplicative ℤ).1,
        (1 : Multiplicative ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup := by
      rw [← h1]
      exact (W.weilGroupEquiv w).2
    obtain ⟨k, hk⟩ := mem_range_fundamentalGroupMap_of_mem_weilGroup p τ G' W.fundamentalGroup _
      hmem
    refine ⟨k, Subtype.ext (W.weilGroupEquiv.injective (Subtype.ext ?_))⟩
    rw [hf, hk, ← h1]
  have hcont : Continuous f := by
    refine W.isEmbedding_ker.isInducing.continuous_iff.2 ?_
    have : (fun k ↦ (W.weilGroupEquiv (f k) : W.fundamentalGroup × Multiplicative ℤ).1) = ρ :=
      funext fun k ↦ congrArg Prod.fst (hf k)
    change Continuous fun k ↦ (W.weilGroupEquiv (f k) : W.fundamentalGroup × Multiplicative ℤ).1
    rw [this]
    exact continuous_fundamentalGroupMap τ G' W.fundamentalGroup
  let e := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  let h := Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hcont
  let toGeometric : G' ≃ₜ* W.geometric :=
    { e with
      continuous_toFun := hcont
      continuous_invFun := h.symm.continuous }
  -- the Frobenius element of degree one
  have hw := mem_weilGroup_frobeniusElement p τ τF W.fundamentalGroup ht
  let w : W.carrier := W.weilGroupEquiv.symm ⟨_, hw⟩
  refine ⟨⟨t, G', toGeometric, τF, transportConj t τF G', transportConj_smul t τF G', w, ?_, ?_⟩⟩
  · left
    rw [W.deg_eq]
    simp [w]
  · intro k
    apply W.weilGroupEquiv.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, w, MulEquiv.apply_symm_apply]
    change (W.weilGroupEquiv (f _) : W.fundamentalGroup × Multiplicative ℤ) =
      _ * (W.weilGroupEquiv (f k) : W.fundamentalGroup × Multiplicative ℤ) * _
    rw [hf, hf, fundamentalGroupMap_transportConj]
    ext <;> simp [ρ]

end AlgebraicGeometry.WeilGroup

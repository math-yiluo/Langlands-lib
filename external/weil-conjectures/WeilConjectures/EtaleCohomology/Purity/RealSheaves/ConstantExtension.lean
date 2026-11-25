/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic

/-!
# The Weil group of a curve after a finite constant field extension

Let `p : C₀ ⟶ Spec 𝔽_q` be a geometrically connected curve, `L = 𝔽_{q ^ m}` a finite extension
of `𝔽_q` of degree `m`, and `C₀' = C₀ ×_{𝔽_q} 𝔽_{q ^ m}`, a geometrically connected curve over
`𝔽_{q ^ m}` (`AlgebraicGeometry.Scheme.FiniteEtale.constantExtensionHom`). Given Weil groups
`W` of `C₀` and `W'` of `C₀'` and a path `τ` from the base point of `C₀'` to that of `C₀`, the
projection `C₀' ⟶ C₀` induces the *natural map* `W(C₀') → W(C₀)`
(`AlgebraicGeometry.WeilGroup.constantExtensionMap`). This file proves (blueprint
`lemma-geometric-constituents-after-constant-extension`) that it is a continuous injective
homomorphism with image `W(C₀)^[m] = deg⁻¹(m ℤ)`, carrying the geometric subgroup `π₁(C)` of
`W(C₀')` onto that of `W(C₀)`, and that the degree over `𝔽_{q ^ m}` is the degree over `𝔽_q` divided
by `m`.

## Main definitions

- `AlgebraicGeometry.WeilGroup.constantExtensionMap`: the natural map `W(C₀') → W(C₀)`.
- `AlgebraicGeometry.WeilGroup.degMultiples`: the subgroup `W(C₀)^[m] = deg⁻¹(m ℤ)`.

## Main statements

- `AlgebraicGeometry.WeilGroup.constantExtension`: the identification of `W(C₀')` with
  `W(C₀)^[m]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

open Scheme.FiniteEtale

variable {K : Type u} [Field K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K))
  (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.Etale K L]

/-- The constant field extension `C₀ ×_K Spec L` of a curve is a curve over `L`: the projection
to `C₀` is finite, so it does not increase the dimension. -/
instance [IsCurve p] : IsCurve (constantExtensionHom p L) where
  krullDim_le_one :=
    ((constantExtensionProj p L).topologicalKrullDim_le_of_locallyQuasiFinite).trans
      (IsCurve.krullDim_le_one (f := p))

namespace WeilGroup

variable [Finite K] [Finite L] {p} [IsCurve p] [GeometricallyConnected p] {L} (W : WeilGroup p)
  (W' : WeilGroup (constantExtensionHom p L))

/-- The subgroup `W(C₀)^[m] = deg⁻¹(m ℤ)` of the elements of the Weil group whose degree is a
multiple of `m`. -/
def degMultiples (m : ℕ) : Subgroup W.carrier :=
  (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ))).comap W.deg

omit [GeometricallyConnected p] in
lemma mem_degMultiples_iff (m : ℕ) (w : W.carrier) :
    w ∈ W.degMultiples m ↔ (m : ℤ) ∣ (W.deg w).toAdd := by
  rw [degMultiples, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk, toAdd_zpow, toAdd_ofAdd, smul_eq_mul]
    exact Dvd.intro_left k rfl
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_ofAdd, smul_eq_mul, hk, mul_comm]

omit [GeometricallyConnected p] in
/-- There is a path from the base point of `C₀'` to that of `C₀`: an isomorphism between the fibre
functor at the base point of `C₀'`, precomposed with the base change of finite étale covers along
`C₀' ⟶ C₀`, and the fibre functor at the base point of `C₀`. -/
lemma nonempty_constantExtensionPath :
    Nonempty (Scheme.FiniteEtale.pullback (constantExtensionProj p L) ⋙
      fiber W'.basePoint ≅ fiber W.basePoint) := by
  have := W.connectedSpace
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber (W'.basePoint ≫ constantExtensionProj p L))
    (fiber W.basePoint)
  exact ⟨pullbackFiberIso _ _ ≪≫ τ⟩

variable (τ : Scheme.FiniteEtale.pullback (constantExtensionProj p L) ⋙ fiber W'.basePoint ≅
  fiber W.basePoint)

/-- The map `π₁(C₀', s') → π₁(C₀, s)` induced by the projection `C₀' ⟶ C₀` and the path `τ`. -/
noncomputable def constantExtensionFundamentalGroupMap :
    W'.fundamentalGroup →* W.fundamentalGroup :=
  have := W.connectedSpace
  fundamentalGroupMap τ W'.fundamentalGroup W.fundamentalGroup

lemma mem_weilGroup_constantExtensionFundamentalGroupMap_iff (g : W'.fundamentalGroup)
    (n : Multiplicative ℤ) :
    (g, n) ∈ weilGroup (constantExtensionHom p L) W'.basePoint W'.fundamentalGroup ↔
      (W.constantExtensionFundamentalGroupMap W' τ g, n ^ Module.finrank K L) ∈
        weilGroup p W.basePoint W.fundamentalGroup :=
  have := W.connectedSpace
  mem_weilGroup_constantExtension_iff p W'.basePoint τ W.fundamentalGroup W'.fundamentalGroup g n

/-- Blueprint `lemma-geometric-constituents-after-constant-extension`: Weil group after a finite
constant-field extension.

The natural map `W(C₀') → W(C₀)` from the Weil group of the constant field extension
`C₀' = C₀ ×_{𝔽_q} 𝔽_{q ^ m}` over `𝔽_{q ^ m}` to the Weil group of `C₀` over `𝔽_q`, induced by
the projection `C₀' ⟶ C₀` and a path `τ` between the base points: on the presentations as
subgroups of `π₁ × ℤ` it is `(g, n) ↦ (ρ g, m n)`, `ρ : π₁(C₀', s') → π₁(C₀, s)` being the map
induced by base change of finite étale covers along `C₀' ⟶ C₀`. -/
noncomputable def constantExtensionMap : W'.carrier →* W.carrier :=
  W.weilGroupEquiv.symm.toMonoidHom.comp <|
    ((((W.constantExtensionFundamentalGroupMap W' τ).prodMap
      (powMonoidHom (Module.finrank K L))).comp
        (weilGroup (constantExtensionHom p L) W'.basePoint W'.fundamentalGroup).subtype).codRestrict
          _ fun w ↦ (W.mem_weilGroup_constantExtensionFundamentalGroupMap_iff W' τ _ _).1 w.2).comp
      W'.weilGroupEquiv.toMonoidHom

lemma weilGroupEquiv_constantExtensionMap (w : W'.carrier) :
    ((W.weilGroupEquiv (W.constantExtensionMap W' τ w) : _) :
      W.fundamentalGroup × Multiplicative ℤ) =
      (W.constantExtensionFundamentalGroupMap W' τ (W'.weilGroupEquiv w).1.1,
        (W'.weilGroupEquiv w).1.2 ^ Module.finrank K L) := by
  simp only [constantExtensionMap, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.codRestrict_apply]
  rfl

/-- The natural map is induced by the map `ρ` of fundamental groups. -/
lemma toFundamentalGroup_constantExtensionMap (w : W'.carrier) :
    W.toFundamentalGroup (W.constantExtensionMap W' τ w) =
      W.constantExtensionFundamentalGroupMap W' τ (W'.toFundamentalGroup w) :=
  congrArg Prod.fst (W.weilGroupEquiv_constantExtensionMap W' τ w)

/-- The natural map multiplies degrees by `m`: the normalised degree over `𝔽_{q ^ m}` is the
degree over `𝔽_q` divided by `m`. -/
lemma deg_constantExtensionMap (w : W'.carrier) :
    W.deg (W.constantExtensionMap W' τ w) = W'.deg w ^ Module.finrank K L := by
  rw [W.deg_eq, W'.deg_eq]
  exact congrArg Prod.snd (W.weilGroupEquiv_constantExtensionMap W' τ w)

/-- The natural map is injective, since `π₁(C₀') → π₁(C₀)` is: `C₀' ⟶ C₀` is finite étale. -/
lemma constantExtensionMap_injective :
    Function.Injective (W.constantExtensionMap W' τ) := by
  have := W.connectedSpace
  have := W'.connectedSpace
  intro w₁ w₂ h
  have h' := congrArg (fun w ↦ ((W.weilGroupEquiv w : _) :
    W.fundamentalGroup × Multiplicative ℤ)) h
  simp only [weilGroupEquiv_constantExtensionMap, Prod.mk.injEq] at h'
  apply W'.weilGroupEquiv.injective
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact fundamentalGroupMap_injective τ W.fundamentalGroup W'.fundamentalGroup h'.1
  · have hm : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
    have h2 := congrArg Multiplicative.toAdd h'.2
    rw [toAdd_pow, toAdd_pow, nsmul_eq_mul, nsmul_eq_mul] at h2
    exact Multiplicative.toAdd.injective (mul_left_cancel₀ (by exact_mod_cast hm) h2)

/-- The image of the natural map is `W(C₀)^[m] = deg⁻¹(m ℤ)`. -/
lemma range_constantExtensionMap :
    (W.constantExtensionMap W' τ).range = W.degMultiples (Module.finrank K L) := by
  have := W.connectedSpace
  have := W'.connectedSpace
  ext w
  rw [mem_degMultiples_iff]
  constructor
  · rintro ⟨w', rfl⟩
    rw [deg_constantExtensionMap, toAdd_pow, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · intro hdvd
    set e := W.weilGroupEquiv w with he
    rw [W.deg_eq] at hdvd
    obtain ⟨g, hg⟩ := mem_range_of_mem_weilGroup_constantExtension p W'.basePoint τ
      W.fundamentalGroup W'.fundamentalGroup e.1.1 e.1.2 e.2 hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hk' : e.1.2.toAdd = Module.finrank K L * k := hk
    have hn : e.1.2 = Multiplicative.ofAdd k ^ Module.finrank K L := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, hk']
    have hmem : (g, Multiplicative.ofAdd k) ∈
        weilGroup (constantExtensionHom p L) W'.basePoint W'.fundamentalGroup := by
      rw [W.mem_weilGroup_constantExtensionFundamentalGroupMap_iff W' τ, ← hn]
      have he' : ((W.constantExtensionFundamentalGroupMap W' τ g, e.1.2) :
          W.fundamentalGroup × Multiplicative ℤ) = e.1 := Prod.ext hg rfl
      rw [he']
      exact e.2
    refine ⟨W'.weilGroupEquiv.symm ⟨_, hmem⟩, W.weilGroupEquiv.injective (Subtype.ext ?_)⟩
    rw [weilGroupEquiv_constantExtensionMap, MulEquiv.apply_symm_apply]
    exact Prod.ext hg hn.symm

omit [Algebra.Etale K L] [Finite K] [Finite L] in
lemma pow_finrank_eq_one_iff (x : Multiplicative ℤ) : x ^ Module.finrank K L = 1 ↔ x = 1 := by
  have hm : (Module.finrank K L : ℤ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, one_pow]⟩
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_pow, nsmul_eq_mul, toAdd_one, mul_eq_zero] at h'
  exact h'.resolve_left hm

/-- The natural map carries the geometric subgroup `π₁(C)` of `W(C₀')` onto that of `W(C₀)`: both
are the elements of degree zero. -/
lemma map_geometric_constantExtensionMap :
    W'.geometric.map (W.constantExtensionMap W' τ) = W.geometric := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    rw [MonoidHom.mem_ker, deg_constantExtensionMap, MonoidHom.mem_ker.1 hw', one_pow]
  · intro hw
    have hr : w ∈ (W.constantExtensionMap W' τ).range := by
      rw [range_constantExtensionMap, mem_degMultiples_iff, MonoidHom.mem_ker.1 hw]
      exact dvd_zero _
    obtain ⟨w', rfl⟩ := hr
    refine ⟨w', ?_, rfl⟩
    rw [MonoidHom.mem_ker, deg_constantExtensionMap, pow_finrank_eq_one_iff] at hw
    exact hw

/-- The natural map is continuous: on the open subgroup `π₁(C)` it is the continuous map `ρ`. -/
lemma continuous_constantExtensionMap : Continuous (W.constantExtensionMap W' τ) := by
  have := W.connectedSpace
  refine continuous_of_continuousAt_one _ ?_
  refine ContinuousOn.continuousAt ?_ (W'.isOpen_ker.mem_nhds W'.geometric.one_mem)
  rw [continuousOn_iff_continuous_domRestrict]
  let ψ : W'.geometric → W.geometric := fun g ↦ ⟨W.constantExtensionMap W' τ g, by
    rw [MonoidHom.mem_ker, deg_constantExtensionMap, MonoidHom.mem_ker.1 g.2, one_pow]⟩
  have hψ : Continuous ψ := by
    refine W.isEmbedding_ker.isInducing.continuous_iff.2 ?_
    have hρ : Continuous (W.constantExtensionFundamentalGroupMap W' τ) := by
      have := fun P ↦ IsFundamentalGroup.continuous_smul (F := fiber W'.basePoint)
        (G := W'.fundamentalGroup) P
      exact continuous_fundamentalGroupMap τ W'.fundamentalGroup W.fundamentalGroup
    refine (hρ.comp W'.isEmbedding_ker.continuous).congr fun g ↦ ?_
    exact (W.toFundamentalGroup_constantExtensionMap W' τ g).symm
  exact continuous_subtype_val.comp hψ

/-- The natural map, as an isomorphism `W(C₀') ≃ W(C₀)^[m]`. -/
noncomputable def constantExtensionEquiv :
    W'.carrier ≃* W.degMultiples (Module.finrank K L) :=
  (MonoidHom.ofInjective (W.constantExtensionMap_injective W' τ)).trans
    (MulEquiv.subgroupCongr (W.range_constantExtensionMap W' τ))

/-- Blueprint `lemma-geometric-constituents-after-constant-extension`: Weil group after a finite
constant-field extension.

Let `C₀` be a geometically connected curve over `𝔽_q`, `L = 𝔽_{q ^ m}` and
`C₀' = C₀ ×_{𝔽_q} 𝔽_{q ^ m}`, regarded as a curve over `𝔽_{q ^ m}`. Under the natural map
`W(C₀') → W(C₀)` induced by the projection `C₀' ⟶ C₀` (and a path between the base points, which
exists by `AlgebraicGeometry.WeilGroup.nonempty_constantExtensionPath`), the Weil group of `C₀'`
identifies with `W(C₀)^[m] = deg⁻¹(m ℤ)`: the map is a continuous injective homomorphism with
image `W(C₀)^[m]`, its geometric subgroup `π₁(C)` is carried onto that of `W(C₀)`, and the
normalised degree is `deg_{𝔽_{q ^ m}} = deg_{𝔽_q} / m`. -/
theorem constantExtension :
    Function.Injective (W.constantExtensionMap W' τ) ∧ Continuous (W.constantExtensionMap W' τ) ∧
      (W.constantExtensionMap W' τ).range = W.degMultiples (Module.finrank K L) ∧
      W'.geometric.map (W.constantExtensionMap W' τ) = W.geometric ∧
      ∀ w, (W.deg (W.constantExtensionMap W' τ w)).toAdd =
        Module.finrank K L * (W'.deg w).toAdd := by
  refine ⟨W.constantExtensionMap_injective W' τ, W.continuous_constantExtensionMap W' τ,
    W.range_constantExtensionMap W' τ, W.map_geometric_constantExtensionMap W' τ, fun w ↦ ?_⟩
  rw [deg_constantExtensionMap, toAdd_pow, nsmul_eq_mul]

/-- Blueprint `lemma-geometric-constituents-after-constant-extension`: Weil group after a finite
constant-field extension.

If `s ∈ W(C₀)` has degree one, then `s ^ m` is the image of an element of degree one of the Weil
group of `C₀ ×_{𝔽_q} 𝔽_{q ^ m}` over `𝔽_{q ^ m}`. -/
theorem exists_constantExtensionMap_eq_pow (s : W.carrier)
    (hs : W.deg s = Multiplicative.ofAdd 1) :
    ∃ s' : W'.carrier, W.constantExtensionMap W' τ s' = s ^ Module.finrank K L ∧
      W'.deg s' = Multiplicative.ofAdd 1 := by
  have hmem : s ^ Module.finrank K L ∈ (W.constantExtensionMap W' τ).range := by
    rw [range_constantExtensionMap, mem_degMultiples_iff, map_pow, hs, toAdd_pow, toAdd_ofAdd,
      nsmul_eq_mul, mul_one]
  obtain ⟨s', hs'⟩ := hmem
  refine ⟨s', hs', ?_⟩
  have h := congrArg W.deg hs'
  rw [deg_constantExtensionMap, map_pow, hs, ← div_eq_one, ← div_pow,
    pow_finrank_eq_one_iff, div_eq_one] at h
  exact h

omit [Finite L] in
/-- Blueprint `situation-weil`: Pointer to the properties of `situation-weil`.

The degree `deg : W(C₀) → ℤ` is a surjective homomorphism with kernel the geometric subgroup
`π₁(C)`, and it sends every lift of the geometric Frobenius `Φ` to `1`: an element of `W(C₀)`
acting on the geometric fibres of the constant covers of `C₀` as `Φ` has degree one
(`situation-weil`, through
`AlgebraicGeometry.Scheme.FiniteEtale.exact_weilGroupDeg`). -/
theorem exact_deg :
    Function.Surjective W.deg ∧ W.deg.ker = W.geometric ∧
      ∀ w : W.carrier, (∀ (A : FiniteEtaleAlgebra K)
        (y : (fiber W.basePoint).obj (constantCover p A)),
          W.toFundamentalGroup w • y = geometricFrobenius p W.basePoint A y) →
        W.deg w = Multiplicative.ofAdd 1 := by
  have := W.connectedSpace
  refine ⟨W.deg_surjective, rfl, fun w hw ↦ ?_⟩
  rw [W.deg_eq]
  exact (exact_weilGroupDeg p W.basePoint W.fundamentalGroup).2.2.2 _
    (funext fun A ↦ Equiv.ext fun y ↦ hw A y)

end WeilGroup

end AlgebraicGeometry

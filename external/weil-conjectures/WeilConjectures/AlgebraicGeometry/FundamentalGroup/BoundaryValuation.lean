/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy
public import WeilConjectures.Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Orders of vanishing at a boundary point and inertia

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field `k`
and `z` a point of `C ∖ U`, with an affine chart `c` (`AlgebraicGeometry.WeilGroup.BoundaryChart`):
an affine open `W ∋ z` with ring of sections `R = Γ(C, W)`, a Dedekind domain, in which `z` is a
maximal ideal `m`. Let `Ω` be a separable closure of the function field `k(C)` and `Q` a maximal
ideal over `m` of the integral closure of `R` in `Ω`.

* The `m`-adic valuation of a rational function `f` is `exp (- ord_z f)`
  (`AlgebraicGeometry.WeilGroup.BoundaryChart.valuation_eq_exp_neg_ord`).
* If an `N`-th root of `f` in `Ω` is fixed by the inertia group of `Q`, then `N` divides
  `ord_z f` (`AlgebraicGeometry.WeilGroup.BoundaryChart.dvd_ord_of_forall_inertia`): this is the
  key input for the vanishing of the residue of a torsor which extends over `z`.
* Conversely, if `N` divides `ord_z f` then every `N`-th root of `f` is fixed by the inertia
  group of `Q` (`AlgebraicGeometry.WeilGroup.BoundaryChart.inertia_apply_eq_of_dvd_ord`), as
  inertia fixes the `N`-th roots of units at `z`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsDedekindDomain

namespace AlgebraicGeometry

/-- The order of vanishing of `u ϖ ^ a`, for a unit `u` and a uniformizer `ϖ` of the discrete
valuation ring at a point of coheight one, is `a`. -/
lemma Scheme.ord_algebraMap_mul_zpow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (u : (X.presheaf.stalk x)ˣ) {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ) (a : ℤ) :
    X.ord (algebraMap _ X.functionField (u : X.presheaf.stalk x) *
      algebraMap _ X.functionField ϖ ^ a) x = a := by
  have hϖ0 : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hϖ.ne_zero
  have hu0 : algebraMap _ X.functionField (u : X.presheaf.stalk x) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero
  rw [Scheme.ord_eq_iff hx (mul_ne_zero hu0 (zpow_ne_zero a hϖ0))]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  change Ring.ordFrac (X.presheaf.stalk x) _ = _
  rw [map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible hϖ, one_mul,
    ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilGroup.BoundaryChart

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {C U : Scheme.{u}} {p : C ⟶ Spec (.of k)}
  [IsCurve p] [SmoothOfRelativeDimension 1 p] [Smooth p] [ConnectedSpace C] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [IsLocallyNoetherian C] {z : C}
  (c : BoundaryChart p j z)

local notation "Ω" => SeparableClosure (Scheme.functionField C)

instance : IsDedekindDomain Γ(C, c.W) :=
  isDedekindDomain_of_isAffineOpen p c.isAffineOpen

instance : IsFractionRing Γ(C, c.W) C.functionField :=
  functionField_isFractionRing_of_isAffineOpen C c.W c.isAffineOpen

instance : c.ideal.IsMaximal := c.isMaximal_ideal

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 p] [Smooth p] [ConnectedSpace C]
  [ConnectedSpace U] [IsLocallyNoetherian C] in
include p in
/-- A boundary point with a chart is closed. -/
lemma isClosed_singleton (hz : z ∉ Set.range j.base) : IsClosed ({z} : Set C) := by
  obtain ⟨u₀⟩ := (inferInstance : Nonempty U)
  exact j.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
    (IsCurve.krullDim_le_one (f := p)) ⟨_, u₀, rfl⟩ hz

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 p] [ConnectedSpace U] [IsIntegral C]
  [IsLocallyNoetherian C] in
lemma ideal_ne_bot (hz : z ∉ Set.range j.base) : c.ideal ≠ ⊥ := fun h ↦
  c.ϖ_ne_zero hz (by simpa [h] using c.ϖ_mem)

omit [SmoothOfRelativeDimension 1 p] [ConnectedSpace U] [IsLocallyNoetherian C] in
/-- The residue field of the chart at the boundary point is algebraically closed. -/
lemma isAlgClosed_residueField (hz : z ∉ Set.range j.base) : IsAlgClosed c.ideal.ResidueField := by
  let z' : c.W := ⟨z, c.mem⟩
  let _ : Algebra Γ(C, c.W) (C.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk C.presheaf z'
  have hloc : IsLocalization.AtPrime (C.presheaf.stalk z) c.ideal :=
    c.isAffineOpen.isLocalization_stalk z'
  have := Scheme.isAlgClosed_residueField_of_isClosed p z
    (BoundaryChart.isClosed_singleton (p := p) (j := j) (z := z) hz)
  let e₁ : Γ(C, c.W) ⧸ c.ideal ≃+* C.residueField z :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal c.ideal (C.presheaf.stalk z)).toRingEquiv
  let e₀ : Γ(C, c.W) ⧸ c.ideal ≃+* c.ideal.ResidueField :=
    RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField c.ideal)
  exact IsAlgClosed.of_ringEquiv _ _ (e₁.symm.trans e₀)

/-- The height one prime of `Γ(C, W)` at the boundary point. -/
noncomputable def heightOneSpectrum (hz : z ∉ Set.range j.base) :
    HeightOneSpectrum Γ(C, c.W) :=
  ⟨c.ideal, inferInstance, c.ideal_ne_bot hz⟩

-- the localization instances at the stalk are slow
omit [IsAlgClosed k] [ConnectedSpace U] in
/-- The `m`-adic valuation at the boundary point of a nonzero rational function `f` is
`exp (- ord_z f)`. -/
lemma valuation_eq_exp_neg_ord (hz : z ∉ Set.range j.base) {f : C.functionField} (hf : f ≠ 0) :
    (c.heightOneSpectrum hz).valuation C.functionField f = WithZero.exp (-C.ord f z) := by
  have hcoh := coheight_eq_one_of_isClosed p
    (BoundaryChart.isClosed_singleton (p := p) (j := j) (z := z) hz)
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one p hcoh
  let z' : c.W := ⟨z, c.mem⟩
  let _ : Algebra Γ(C, c.W) (C.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk C.presheaf z'
  have hloc : IsLocalization.AtPrime (C.presheaf.stalk z) c.ideal :=
    c.isAffineOpen.isLocalization_stalk z'
  have := functionField_isScalarTower C c.W z'
  set v := c.heightOneSpectrum hz
  -- valuations of elements of `Γ(C, W)` mapping to units of the stalk
  have hunit (r : Γ(C, c.W)) (hr : r ∈ c.ideal.primeCompl) : v.intValuation r = 1 :=
    (v.intValuation_eq_one_iff_mem_primeCompl r).2 hr
  -- a uniformizer coming from `Γ(C, W)`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk z)
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective c.ideal.primeCompl π
  have hsu : IsUnit (algebraMap Γ(C, c.W) (C.presheaf.stalk z) s) :=
    IsLocalization.map_units _ s
  have htπ : algebraMap Γ(C, c.W) (C.presheaf.stalk z) t =
      π * algebraMap Γ(C, c.W) (C.presheaf.stalk z) s := by
    rw [← hts, IsLocalization.mk'_spec]
  have ht : Irreducible (algebraMap Γ(C, c.W) (C.presheaf.stalk z) t) := by
    rw [htπ]
    exact (irreducible_mul_isUnit hsu).2 hπ
  have htv : v.intValuation t = WithZero.exp (-1) := by
    have hmem : t ∈ c.ideal := by
      by_contra h
      exact ht.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff _ c.ideal t).2 h)
    have hnmem : t ∉ c.ideal ^ 2 := by
      intro h
      have hmap := Ideal.mem_map_of_mem (algebraMap Γ(C, c.W) (C.presheaf.stalk z)) h
      rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal,
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmap
      obtain ⟨d, hd⟩ := hmap
      rw [pow_two, mul_assoc] at hd
      rcases ht.isUnit_or_isUnit hd with h | h
      · exact hπ.not_isUnit h
      · exact hπ.not_isUnit (isUnit_of_mul_isUnit_left h)
    have h1 : v.intValuation t ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
      (v.intValuation_le_pow_iff_mem t 1).2 (by rwa [pow_one])
    have h2 : ¬ v.intValuation t ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
      fun h ↦ hnmem ((v.intValuation_le_pow_iff_mem t 2).1 h)
    have h0 : v.intValuation t ≠ 0 := v.intValuation_ne_zero t (fun h ↦ ht.ne_zero (by simp [h]))
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v.intValuation t = WithZero.exp b :=
      ⟨WithZero.log (v.intValuation t), (WithZero.exp_log h0).symm⟩
    rw [hb, WithZero.exp_le_exp] at h1 h2
    rw [hb, WithZero.exp_inj]
    push_cast at h1 h2
    omega
  -- `f = u t ^ a`
  obtain ⟨u, a, rfl⟩ := IsDiscreteValuationRing.exists_eq_algebraMap_mul_zpow ht hf
  rw [Scheme.ord_algebraMap_mul_zpow hcoh u ht a]
  obtain ⟨⟨r₁, s₁⟩, hrs₁⟩ := IsLocalization.mk'_surjective c.ideal.primeCompl
    (u : C.presheaf.stalk z)
  have hr₁ : r₁ ∈ c.ideal.primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff _ c.ideal r₁ s₁).1 (hrs₁ ▸ u.isUnit)
  have hu₁ : algebraMap _ C.functionField (u : C.presheaf.stalk z) *
      algebraMap Γ(C, c.W) C.functionField s₁ = algebraMap Γ(C, c.W) C.functionField r₁ := by
    rw [IsScalarTower.algebraMap_apply Γ(C, c.W) (C.presheaf.stalk z) C.functionField s₁,
      IsScalarTower.algebraMap_apply Γ(C, c.W) (C.presheaf.stalk z) C.functionField r₁,
      ← map_mul, ← hrs₁, IsLocalization.mk'_spec]
  have hvu : v.valuation C.functionField
      (algebraMap _ C.functionField (u : C.presheaf.stalk z)) = 1 := by
    have h := congrArg (v.valuation C.functionField) hu₁
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, hunit r₁ hr₁, hunit s₁ s₁.2, mul_one] at h
    exact h
  rw [map_mul, map_zpow₀, hvu, one_mul, ← IsScalarTower.algebraMap_apply,
    HeightOneSpectrum.valuation_of_algebraMap, htv, ← WithZero.exp_zsmul, smul_eq_mul,
    mul_neg_one]

-- instance search through `SeparableClosure` and its integral closures is slow
omit [ConnectedSpace U] in
/-- **An `N`-th root fixed by inertia.** If an `N`-th root in `Ω` of a nonzero rational function
`f` is fixed by the inertia group of a point over the boundary point `z`, then `N` divides the
order of vanishing of `f` at `z`. -/
theorem dvd_ord_of_forall_inertia (hz : z ∉ Set.range j.base)
    (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal] [Q.LiesOver c.ideal] {N : ℕ}
    {x : Ω} (hx : x ≠ 0) {f : C.functionField} (hf : algebraMap _ Ω f = x ^ N)
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/C.functionField), σ x = x) : (N : ℤ) ∣ C.ord f z := by
  have := c.isAlgClosed_residueField hz
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact pow_ne_zero N hx (by rw [← hf, map_zero])
  obtain ⟨b, hb⟩ := Ideal.exists_valuation_eq_exp_mul_of_forall_inertia c.ideal (c.ideal_ne_bot hz)
    Q hx hf hI
  have h := c.valuation_eq_exp_neg_ord hz hf0
  rw [heightOneSpectrum, hb, WithZero.exp_inj] at h
  exact ⟨-b, by linarith⟩

-- the localization instances at the stalk are slow
-- instance search through `SeparableClosure` and its integral closures is slow
omit [SmoothOfRelativeDimension 1 p] [ConnectedSpace U] [IsLocallyNoetherian C] in
/-- **Inertia fixes `N`-th roots of units.** The inertia group of a point over the boundary point
`z` fixes every `N`-th root in `Ω` of a unit of the local ring at `z`, for `N` invertible in
`k`. -/
theorem inertia_apply_eq_of_pow_eq (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal]
    [Q.LiesOver c.ideal] {σ : Gal(Ω/C.functionField)}
    (hσ : σ ∈ Q.inertia Gal(Ω/C.functionField)) {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) {w : Ω}
    (u : (C.presheaf.stalk z)ˣ)
    (hw : w ^ N = algebraMap _ Ω (algebraMap _ C.functionField (u : C.presheaf.stalk z))) :
    σ w = w := by
  classical
  let z' : c.W := ⟨z, c.mem⟩
  let _ : Algebra Γ(C, c.W) (C.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk C.presheaf z'
  have hloc : IsLocalization.AtPrime (C.presheaf.stalk z) c.ideal :=
    c.isAffineOpen.isLocalization_stalk z'
  have := functionField_isScalarTower C c.W z'
  set F := C.functionField
  let ι : F →+* Ω := algebraMap F Ω
  -- a primitive `N`-th root of unity of `k`, in `Γ(C, W)` and in `Ω`
  have : NeZero (N : k) := ⟨hN⟩
  obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
  let κ : k →+* F := (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  let lR : k →+* Γ(C, c.W) := (C.presheaf.map (homOfLE (le_top : c.W ≤ ⊤)).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hRF (r : Γ(C, c.W)) : algebraMap Γ(C, c.W) Ω r = ι (algebraMap Γ(C, c.W) F r) :=
    IsScalarTower.algebraMap_apply _ F Ω r
  have hRO (r : Γ(C, c.W)) : algebraMap Γ(C, c.W) F r =
      algebraMap (C.presheaf.stalk z) F (algebraMap Γ(C, c.W) (C.presheaf.stalk z) r) :=
    IsScalarTower.algebraMap_apply _ (C.presheaf.stalk z) F r
  have hlR (b : k) : algebraMap Γ(C, c.W) Ω (lR b) = ι (κ b) := by
    rw [hRF]
    congr 1
    exact C.presheaf.germ_res_apply (homOfLE (le_top : c.W ≤ ⊤)) (genericPoint C) _ _
  have hinj : Function.Injective (algebraMap Γ(C, c.W) Ω) := by
    intro r r' h
    rw [hRF, hRF] at h
    exact (C.germToFunctionField_injective c.W) (ι.injective h)
  have hζ : IsPrimitiveRoot (ι (κ ζk)) N := hζk.map_of_injective (ι.comp κ).injective
  obtain ⟨⟨r, s'⟩, hrs⟩ := IsLocalization.mk'_surjective c.ideal.primeCompl
    (u : C.presheaf.stalk z)
  have hr : r ∈ c.ideal.primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff _ c.ideal r s').1 (hrs ▸ u.isUnit)
  have hs : (s' : Γ(C, c.W)) ∉ c.ideal := s'.2
  have hrs' : r * (s' : Γ(C, c.W)) ^ (N - 1) ∉ c.ideal := fun h ↦
    ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hr fun h' ↦ hs (Ideal.IsPrime.mem_of_pow_mem
      inferInstance _ h'))
  have hζR : IsPrimitiveRoot (algebraMap Γ(C, c.W) Ω (lR ζk)) N := by rw [hlR]; exact hζ
  have hζRu (k' : ℕ) (hk' : lR ζk ^ k' ≠ 1) : IsUnit (lR ζk ^ k' - 1) := by
    have : ζk ^ k' - 1 ≠ 0 := fun h ↦ hk' (by rw [← map_pow, sub_eq_zero.1 h, map_one])
    rw [← map_pow, ← map_one lR, ← map_sub]
    exact (Ne.isUnit this).map lR
  exact Ideal.inertia_smul_eq_of_pow_eq Q hσ hζR hζRu (w := w)
    (r := r * (s' : Γ(C, c.W)) ^ (N - 1)) (s := s')
    (fun h ↦ hrs' ((Ideal.mem_of_liesOver Q c.ideal _).2 h))
    (fun h ↦ hs (by
      rw [show (s' : Γ(C, c.W)) = 0 from hinj (h.trans (map_zero _).symm)]
      exact c.ideal.zero_mem))
    (by
      have he (x : Γ(C, c.W)) : algebraMap Γ(C, c.W) Ω x =
          ι (algebraMap _ F (algebraMap Γ(C, c.W) (C.presheaf.stalk z) x)) := by
        rw [hRF, hRO]
      have hpow : (algebraMap Γ(C, c.W) (C.presheaf.stalk z) s') ^ N =
          algebraMap Γ(C, c.W) (C.presheaf.stalk z) s' *
            (algebraMap Γ(C, c.W) (C.presheaf.stalk z) s') ^ (N - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel NeZero.one_le]
      rw [mul_pow, hw, he, he, ← map_pow ι, ← map_mul ι, ← map_pow (algebraMap _ F),
        ← map_mul (algebraMap _ F), hpow, ← mul_assoc, ← hrs, IsLocalization.mk'_spec]
      simp only [map_mul, map_pow])

-- instance search through `SeparableClosure` and its integral closures is slow
omit [ConnectedSpace U] in
/-- **`N`-th roots of functions of order divisible by `N`.** If `N` is invertible in `k` and
divides the order of vanishing at the boundary point `z` of a nonzero rational function `f`, then
the inertia group of a point over `z` fixes every `N`-th root of `f` in `Ω`. -/
theorem inertia_apply_eq_of_dvd_ord (hz : z ∉ Set.range j.base)
    (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal] [Q.LiesOver c.ideal]
    {σ : Gal(Ω/C.functionField)} (hσ : σ ∈ Q.inertia Gal(Ω/C.functionField)) {N : ℕ} [NeZero N]
    (hN : (N : k) ≠ 0) {x : Ω} {f : C.functionField} (hf0 : f ≠ 0)
    (hf : algebraMap _ Ω f = x ^ N) (hdvd : (N : ℤ) ∣ C.ord f z) : σ x = x := by
  have hcoh := coheight_eq_one_of_isClosed p
    (BoundaryChart.isClosed_singleton (p := p) (j := j) (z := z) hz)
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one p hcoh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk z)
  obtain ⟨u, a, rfl⟩ := IsDiscreteValuationRing.exists_eq_algebraMap_mul_zpow hπ hf0
  rw [Scheme.ord_algebraMap_mul_zpow hcoh u hπ a] at hdvd
  obtain ⟨b, rfl⟩ := hdvd
  rw [map_mul, map_zpow₀] at hf
  have hy : algebraMap _ Ω (algebraMap _ C.functionField π) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap C.functionField Ω).injective).2
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hπ.ne_zero)
  have hσy : σ (algebraMap _ Ω (algebraMap _ C.functionField π)) =
      algebraMap _ Ω (algebraMap _ C.functionField π) := σ.commutes _
  generalize algebraMap _ Ω (algebraMap _ C.functionField π) = y at hf hσy hy
  have hw : (x / y ^ b) ^ N =
      algebraMap _ Ω (algebraMap _ C.functionField (u : C.presheaf.stalk z)) := by
    rw [div_pow, ← hf, ← zpow_natCast (y ^ b), ← zpow_mul, mul_comm b, mul_div_assoc,
      div_self (zpow_ne_zero _ hy), mul_one]
  have h := c.inertia_apply_eq_of_pow_eq Q hσ hN u hw
  rw [map_div₀, map_zpow₀, hσy, div_left_inj' (zpow_ne_zero _ hy)] at h
  exact h

end AlgebraicGeometry.WeilGroup.BoundaryChart

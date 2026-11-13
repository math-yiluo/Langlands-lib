import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.RootReflectionProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Actual affine reflections for explicit integer-valued building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

private theorem eval_sub_zsmul_char {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a b : characterLattice S) (z : ℤ) (w : V S) :
    eval S (a - z • b) w = eval S a w - (z : ℝ) * eval S b w := by
  rw [eval_eq_pair, eval_eq_pair, eval_eq_pair, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul, map_sub, map_zsmul, LinearMap.sub_apply,
    LinearMap.smul_apply, zsmul_eq_mul]

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- `y_a(u) = x_a(u) + a(y - x)` for points `x, y` of the apartment: the translation action
`φ_{v,a}(u) = φ_a(u) + a(v)` of KP §6.1, stated before Lemma 6.1.6. -/
theorem val_apply_eq_add (x y : B.Apartment) (α : relativeRoots B.i) (u : rationalPoints G) :
    y.val α u = x.val α u + ((rootForm B.i α (y -ᵥ x) : ℝ) : WithTop ℝ) := by
  have key : ∀ v : TranslationSpace B.i,
      (v +ᵥ x).val α u = x.val α u + ((rootForm B.i α v : ℝ) : WithTop ℝ) :=
    fun v => Submodule.Quotient.induction_on _ v fun w => by
      rw [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply, rootForm_mk]
  rw [← key, vsub_vadd]

/-- `x_a(1) = ∞` (KP axiom V 1). -/
theorem val_apply_one (α : relativeRoots B.i) (x : B.Apartment) :
    x.val α 1 = ⊤ :=
  (x.isValuation.eq_top_iff α α.2 1 (B.rootGroup α).one_mem).2 rfl

/-- `x_a(u) < ∞` for `u ∈ U_a(F) ∖ {1}` (KP axiom V 1). -/
theorem val_apply_ne_top {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) (x : B.Apartment) : x.val α u ≠ ⊤ :=
  fun h => h1 ((x.isValuation.eq_top_iff α α.2 u hu).1 h)

/-! ### The elements `m(u)`, the hyperplanes `H_u` and the functionals `ψ^u_a` -/

/-- KP's `m(u) = u′ u u″ ∈ N(F)` (Proposition 2.11.17) for an opposite factor pair
`p = (u′, u″)` of `u`. -/
def reflectionElement {α : relativeRoots B.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    normalizerPoints B.i :=
  ⟨p.1 * u * p.2, hp.2.2⟩

@[simp] theorem coe_reflectionElement {α : relativeRoots B.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    (B.reflectionElement hp : rationalPoints G) = p.1 * u * p.2 :=
  rfl

/-- KP's hyperplane `H_u = {x ∈ A | x_a(u) = 0}` (KP §6.2, before Proposition 6.2.1). -/
def reflectionHyperplane (α : relativeRoots B.i) (u : rationalPoints G) : Set B.Apartment :=
  {x | x.val α u = 0}

/-- KP's `ψ^u_a`: the affine functional with derivative `a` whose value at a fixed base point
`x₀` is `x₀_a(u)` (with `0` for `x₀_a(u) = ∞`). For `u ∈ U_a(F) ∖ {1}` its value at every
point `x` is `x_a(u)` (`coe_reflectionFunctional_apply`), so it vanishes exactly on `H_u`. -/
def reflectionFunctional (α : relativeRoots B.i) (u : rationalPoints G) :
    B.Apartment →ᵃ[ℝ] ℝ :=
  B.apartment.affineFunctional α (Classical.arbitrary B.Apartment)
    (((Classical.arbitrary B.Apartment).val α u).untopD 0)

@[simp] theorem reflectionFunctional_linear (α : relativeRoots B.i) (u : rationalPoints G) :
    (B.reflectionFunctional α u).linear = rootForm B.i α :=
  rfl

/-- `ψ^u_a(x) = x_a(u)` for `u ∈ U_a(F) ∖ {1}`. -/
theorem coe_reflectionFunctional_apply {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) (y : B.Apartment) :
    ((B.reflectionFunctional α u y : ℝ) : WithTop ℝ) = y.val α u := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
    (B.val_apply_ne_top hu h1 (Classical.arbitrary B.Apartment))
  rw [reflectionFunctional, KPApartmentData.affineFunctional_apply,
    B.val_apply_eq_add (Classical.arbitrary B.Apartment) y, ← ht, WithTop.untopD_coe,
    add_comm, WithTop.coe_add]

/-- `H_u` is the zero set of `ψ^u_a`, an affine functional with derivative `a`. -/
theorem reflectionHyperplane_eq {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) :
    B.reflectionHyperplane α u = {x | B.reflectionFunctional α u x = 0} := by
  ext x
  change x.val α u = 0 ↔ B.reflectionFunctional α u x = 0
  rw [← B.coe_reflectionFunctional_apply hu h1 x, ← WithTop.coe_zero, WithTop.coe_eq_coe]

/-! ### AS 1 -/

/-- AS 1 of KP Axiom 4.1.6: for `a ∈ Φ`, `u ∈ U_a(F) ∖ {1}` and every opposite factor pair
`(u′, u″)` of `u`, the element `m(u) = u′ u u″` fixes the hyperplane `H_u` pointwise. -/
def HasRootReflections : Prop :=
  ∀ (α : relativeRoots B.i) (u : rationalPoints G), u ∈ B.rootGroup α → u ≠ 1 →
    ∀ (p : rationalPoints G × rationalPoints G)
      (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p),
      ∀ x ∈ B.reflectionHyperplane α u, B.reflectionElement hp • x = x

/-! ### AS 2 and AS 3 in terms of `ψ^u_a` -/

/-- KP's `Ψ′ = {ψ^u_a | a ∈ Φ, u ∈ U_a(F) ∖ {1}}` of AS 2. -/
def reflectionAffineRoots : Set (B.Apartment →ᵃ[ℝ] ℝ) :=
  {ψ | ∃ (α : relativeRoots B.i) (u : rationalPoints G), u ∈ B.rootGroup α ∧ u ≠ 1 ∧
    ψ = B.reflectionFunctional α u}

/-- The `ψ^u_a` are exactly the jumps of the filtrations: `Ψ′` of AS 2 is the published
`extendedAffineRoots` (KP Remark 4.1.7 and Definition 6.3.4). -/
theorem reflectionAffineRoots_eq :
    B.reflectionAffineRoots = B.apartment.extendedAffineRoots := by
  ext ψ
  constructor
  · rintro ⟨α, u, hu, h1, rfl⟩
    refine ⟨α, rfl, fun heq => ?_⟩
    have x : B.Apartment := Classical.arbitrary B.Apartment
    have hmem : u ∈ B.apartment.affineRootGroup α (B.reflectionFunctional α u) :=
      (KPApartmentData.mem_affineRootGroup_iff rfl x).2
        ⟨hu, (B.coe_reflectionFunctional_apply hu h1 x).le⟩
    rw [← heq, KPApartmentData.mem_affineRootGroupPlus_iff rfl x,
      B.coe_reflectionFunctional_apply hu h1 x] at hmem
    exact lt_irrefl _ hmem.2
  · rintro ⟨α, hψ, hne⟩
    have x : B.Apartment := Classical.arbitrary B.Apartment
    obtain ⟨u, hu, hnu⟩ : ∃ u ∈ B.apartment.affineRootGroup α ψ,
        u ∉ B.apartment.affineRootGroupPlus α ψ := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm (B.apartment.affineRootGroupPlus_le α ψ) hcon)
    rw [KPApartmentData.mem_affineRootGroup_iff hψ x] at hu
    rw [KPApartmentData.mem_affineRootGroupPlus_iff hψ x] at hnu
    have heq : x.val α u = ψ x := le_antisymm (not_lt.1 fun h => hnu ⟨hu.1, h⟩) hu.2
    have h1 : u ≠ 1 := by
      rintro rfl
      rw [B.val_apply_one] at heq
      exact WithTop.top_ne_coe heq
    refine ⟨α, u, hu.1, h1, AffineMap.ext_linear (hψ.trans rfl) (p := x) ?_⟩
    exact WithTop.coe_injective ((B.coe_reflectionFunctional_apply hu.1 h1 x).trans heq).symm


/-- Actual rank-one factorization supplies all opposite pairs over this field. -/
theorem hasOppositeFactorPairs : RelativeRoot.HasOppositeFactorPairs B.i := by
  intro a ha g hg hg1
  exact ((rootRankOneFactorization k G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus) a ha g hg hg1).1.exists

open RootReflectionProof in
/-- Every actual opposite pair fixes its valuation-zero hyperplane pointwise. -/
theorem hasRootReflections : B.HasRootReflections := by
  intro α u hu h1 p hp x hx
  have := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hfin := hS.finite_relativeRoots B.i
  obtain ⟨a, ha⟩ := α
  have ha0 : a ≠ 0 := ha.1
  set m := B.reflectionElement hp with hm_def
  have hmG : (m : rationalPoints G) = p.1 * u * p.2 := rfl
  have hφ := x.isValuation
  obtain ⟨v, hv⟩ := B.apartment.equipollent_of_mem x.mem (m • x).mem
  rw [KPApartmentData.val_smul] at hv
  obtain ⟨hν, hr⟩ := hp.coroot_spec B.i hS ha0 hu h1
  set ν := hp.coroot B.i hS ha0 hu h1 with hν_def
  have hr' : ∀ χ, weylAction B.i m χ = χ - latticePairing B.S χ ν • a := hr
  have h2 : ∀ χ, weylAction B.i m (weylAction B.i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction B.i m⁻¹ χ = χ - latticePairing B.S χ ν • a := by
    intro χ
    calc weylAction B.i m⁻¹ χ = weylAction B.i m⁻¹ (weylAction B.i m (weylAction B.i m χ)) := by
          rw [h2]
      _ = weylAction B.i m χ := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one,
            id]
      _ = _ := hr' χ
  have hma : weylAction B.i m a = -a := by
    rw [hr', hν, show a - (2 : ℤ) • a = -a by module]
  have hmna : weylAction B.i m⁻¹ (-a) = a := by
    rw [hinv, map_neg, LinearMap.neg_apply, hν, show -a - (-2 : ℤ) • a = a by module]
  have hna : -a ∈ relativeRoots B.i := hma ▸ weylAction_mapsTo_relativeRoots B.i m ha
  -- Depths: `u ∈ U_{a,0}` and `p.1, p.2 ∈ U_{-a,0}` (V 5 for `m` and `m⁻¹`).
  have hu0 : x.val a u = 0 := hx
  have hp1 : x.val (-a) p.1 = 0 := by
    have := hφ.opposite a ha u hu h1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rwa [hu0, add_zero] at this
  have hminv : p.2⁻¹ * u⁻¹ * p.1⁻¹ ∈ normalizerPoints B.i := by
    have : p.2⁻¹ * u⁻¹ * p.1⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2 : x.val (-a) p.2 = 0 := by
    have := hφ.opposite a ha u⁻¹ (inv_mem hu) (inv_ne_one.2 h1) p.2⁻¹ (inv_mem hp.2.1)
      p.1⁻¹ (inv_mem hp.1) hminv
    rwa [apply_inv hφ, apply_inv hφ, hu0, add_zero] at this
  have hmc : (m : rationalPoints G) ∈
      Subgroup.closure (rootFiltration B.i x.val a 0 ∪ rootFiltration B.i x.val (-a) 0) := by
    rw [hmG]
    refine mul_mem (mul_mem (Subgroup.subset_closure (Or.inr ⟨hp.1, ?_⟩))
      (Subgroup.subset_closure (Or.inl ⟨hu, ?_⟩)))
      (Subgroup.subset_closure (Or.inr ⟨hp.2.1, ?_⟩))
    · rw [hp1, WithTop.coe_zero]
    · rw [hu0, WithTop.coe_zero]
    · rw [hp2, WithTop.coe_zero]
  -- `a(v) = 0`, through `y = m⁻¹ p.1 m ∈ U_a` and `m⁻¹ = y⁻¹ p.2⁻¹ u⁻¹`.
  obtain ⟨y, hy_def⟩ : ∃ y, y = (m : rationalPoints G)⁻¹ * p.1 * m := ⟨_, rfl⟩
  have hy : y ∈ rootGroupPoints B.i a := by
    have := conj_mem_rootGroupPoints m⁻¹ (a := -a) hp.1
    rwa [hmna, InvMemClass.coe_inv, inv_inv, ← hy_def] at this
  have hminv' : y⁻¹ * p.2⁻¹ * u⁻¹ ∈ normalizerPoints B.i := by
    have : y⁻¹ * p.2⁻¹ * u⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hy_def, hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2ne := (hp.factors_ne_one B.i hS ha0 hu h1).2
  have hy0 : x.val a y = 0 := by
    have := hφ.opposite (-a) hna p.2⁻¹ (inv_mem hp.2.1) (inv_ne_one.2 hp2ne) y⁻¹
      (by rw [neg_neg]; exact inv_mem hy) u⁻¹ (by rw [neg_neg]; exact inv_mem hu) hminv'
    rwa [neg_neg, apply_inv hφ, apply_inv hφ, hp2, add_zero] at this
  have hav : eval B.S a v = 0 := by
    have hval := congrArg (fun ψ : RootFunctionFamily B.S G => ψ (-a) p.1) hv
    simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hmna, ← hy_def,
      hy0, hp1, zero_add, eval_neg_char] at hval
    have := (WithTop.coe_eq_zero.1 hval.symm)
    linarith
  -- Every root vanishes at `v`.
  have hall : ∀ d ∈ relativeRoots B.i, eval B.S d v = 0 := by
    intro d hd
    rcases lt_trichotomy (eval B.S d v) 0 with hlt | heq | hgt
    · exact (not_eval_neg hS hφ hfin ha hν hinv hmc hv hav hd hlt).elim
    · exact heq
    · exfalso
      have hv' : m⁻¹ • x.val = (-(m⁻¹ • v)) +ᵥ x.val := by
        have h := congrArg (m⁻¹ • ·) hv
        simp only [inv_smul_smul, RootFunctionFamily.smul_vadd] at h
        calc m⁻¹ • x.val = -(m⁻¹ • v) +ᵥ ((m⁻¹ • v) +ᵥ m⁻¹ • x.val) := by
              rw [neg_vadd_vadd]
          _ = _ := by rw [← h]
      refine not_eval_neg (n := m⁻¹) hS hφ hfin ha hν (fun χ => by rw [inv_inv]; exact hr' χ)
        ?_ hv' ?_ (weylAction_mapsTo_relativeRoots B.i m hd) ?_
      · rw [InvMemClass.coe_inv]
        exact inv_mem hmc
      · rw [map_neg, eval_normalizer_smul, inv_inv, hma, eval_neg_char, hav, neg_zero, neg_zero]
      · rw [map_neg, eval_normalizer_smul, inv_inv, h2]
        linarith
  refine KPApartmentData.Apartment.ext ?_
  rw [KPApartmentData.val_smul, hv]
  exact hφ.vadd_eq_self_iff.2 (mem_rootAnnihilator.2 hall)


section Action

variable {α : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The class of the integral coroot supplied by the actual opposite pair. -/
def reflectionCoroot (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    TranslationSpace B.i :=
  Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ]
    hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hg hg1)

/-- The derivative of the root functional takes value two on the actual pair coroot. -/
theorem rootForm_reflectionCoroot (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    rootForm B.i α (B.reflectionCoroot hg hg1 hp) = 2 := by
  simp only [reflectionCoroot, rootForm_mk, eval_tmul, one_mul]
  exact_mod_cast (hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
    α.property.1 hg hg1).1

/-- The linear part of the actual normalizer action is the reflection with this coroot. -/
theorem translationAction_reflectionElement (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p)
    (w : TranslationSpace B.i) :
    translationAction B.i (B.reflectionElement hp) w =
      w - rootForm B.i α w • B.reflectionCoroot hg hg1 hp := by
  let ν := hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hg hg1
  obtain ⟨hν, hr⟩ := hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
    α.property.1 hg hg1
  let m := B.reflectionElement hp
  have hr' : ∀ χ, weylAction B.i m χ = χ - latticePairing B.S χ ν • α.val := hr
  have h2 : ∀ χ, weylAction B.i m (weylAction B.i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction B.i m⁻¹ χ = χ - latticePairing B.S χ ν • α.val := by
    intro χ
    calc
      weylAction B.i m⁻¹ χ =
          weylAction B.i m⁻¹ (weylAction B.i m (weylAction B.i m χ)) := by rw [h2]
      _ = weylAction B.i m χ := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          LinearEquiv.coe_one, id]
      _ = _ := hr' χ
  refine Submodule.Quotient.induction_on _ w fun v => ?_
  rw [translationAction_mk]
  change (Submodule.Quotient.mk (m • v) : TranslationSpace B.i) =
    Submodule.Quotient.mk v - eval B.S α.val v •
      Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν)
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  refine mem_rootAnnihilator.2 fun b _ => ?_
  rw [map_sub, map_sub, eval_normalizer_smul, hinv, eval_sub_zsmul_char,
    map_smul, eval_tmul, one_mul]
  ring

/-- The fixed-hyperplane form of AS 1 and the actual linear action determine the full
affine action of a supplied opposite pair. -/
theorem normalizerAffineEquiv_reflectionElement
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional α g)
        (B.rootForm_reflectionCoroot hg hg1 hp) := by
  have hlin :
      (B.apartment.normalizerAffineEquiv (B.reflectionElement hp)).toAffineMap.linear =
        (AffineRootSystem.affineReflection (B.reflectionFunctional α g)
          (B.rootForm_reflectionCoroot hg hg1 hp)).toAffineMap.linear := by
    apply LinearMap.ext
    intro w
    change translationAction B.i (B.reflectionElement hp) w =
      Module.reflection (B.rootForm_reflectionCoroot hg hg1 hp) w
    rw [Module.reflection_apply]
    exact B.translationAction_reflectionElement hg hg1 hp w
  have hne : (B.reflectionFunctional α g).linear ≠ 0 := by
    intro h0
    have h := B.rootForm_reflectionCoroot hg hg1 hp
    change (B.reflectionFunctional α g).linear _ = 2 at h
    rw [h0, LinearMap.zero_apply] at h
    norm_num at h
  obtain ⟨x, hx⟩ := AffineRootSystem.exists_apply_eq_zero hne
  apply AffineEquiv.toAffineMap_injective
  refine AffineMap.ext_linear hlin (p := x) ?_
  have hxH : x ∈ B.reflectionHyperplane α g := by
    rw [B.reflectionHyperplane_eq hg hg1]
    exact hx
  change B.reflectionElement hp • x = _
  rw [B.hasRootReflections α g hg hg1 p hp x hxH]
  exact (AffineRootSystem.affineReflection_apply_of_mem
    (B.reflectionFunctional α g) (B.rootForm_reflectionCoroot hg hg1 hp) hx).symm


end Action

section Coroot

variable {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The coroot of any actual opposite pair preserves the affine roots. Neither
AS 5 nor an affine-root-system hypothesis is needed here. -/
theorem isCoroot_reflectionCoroot_without_apartment_axioms
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g)
      (B.reflectionCoroot hg hg1 hp) := by
  refine ⟨B.rootForm_reflectionCoroot hg hg1 hp, fun f hf => ?_⟩
  have hm := B.apartment.normalizerAffineEquiv_mem_rootStabilizer (B.reflectionElement hp)
  rw [B.normalizerAffineEquiv_reflectionElement hg hg1 hp] at hm
  have hf' := (hm f).2 hf
  change f.comp (AffineRootSystem.affineReflection (B.reflectionFunctional a g)
    (B.rootForm_reflectionCoroot hg hg1 hp) : B.Apartment →ᵃ[ℝ] B.Apartment) ∈
      B.affineRoots at hf'
  exact (AffineRootSystem.comp_affineReflection (B.reflectionFunctional a g)
    (B.rootForm_reflectionCoroot hg hg1 hp) f) ▸ hf'


end Coroot

end IntegerValuationBuildingData

end Langlands.Geometry.Building

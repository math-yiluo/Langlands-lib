/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.ModuleOfRingHom
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimitIso
public import WeilConjectures.Algebra.Module.InverseLimitFinite
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProfiniteCoefficientCohomology

/-!
# Integral `ℓ`-adic pro-étale cohomology

Let `S` be a scheme and `p` a prime (in practice `ℓ`). The pro-étale cohomology
`Hⁿ(S, ℤ_p) = Hⁿ(S_proét, C(-, ℤ_p))` (`AlgebraicGeometry.ProEtale.IntegralAdicH`) is a
`ℤ_p`-module, as is `Hⁿ(S, ℤ/pᵐ) = Hⁿ(S_proét, C(-, ℤ_p / pᵐ))`
(`AlgebraicGeometry.ProEtale.FiniteAdicH`), through the action of `ℤ_p` on the coefficients. This
file proves the structure results relating them:

* the **Bockstein sequence** of `0 ⟶ ℤ_p --pᵐ--> ℤ_p ⟶ ℤ/pᵐ ⟶ 0`: the kernel of the reduction
  `ρₘ : Hⁿ(S, ℤ_p) ⟶ Hⁿ(S, ℤ/pᵐ)` is `pᵐ Hⁿ(S, ℤ_p)`
  (`AlgebraicGeometry.ProEtale.exists_eq_pow_smul_of_reduction_eq_zero`), and if `pᵉ` kills the
  `p`-power torsion of `Hⁿ⁺¹(S, ℤ_p)`, the image of `ρₘ` contains `pᵉ Hⁿ(S, ℤ/pᵐ)`
  (`AlgebraicGeometry.ProEtale.pow_smul_mem_range_reduction`);
* **separation**: by repleteness of the pro-étale topos and the Milnor sequence, a class of
  `Hⁿ(S, ℤ_p)` vanishing in all `Hⁿ(S, ℤ/pᵐ)` is zero, as soon as the groups `Hⁿ⁻¹(S, ℤ/pᵐ)` are
  finite (`AlgebraicGeometry.ProEtale.eq_zero_of_forall_reduction_eq_zero`);
* **finite generation**: if moreover `Hⁿ(S, ℤ/p)` is finite, then `Hⁿ(S, ℤ_p)` is a finitely
  generated `ℤ_p`-module (`AlgebraicGeometry.ProEtale.module_finite_integralAdicH`).

These are the inputs of the transport of Poincaré duality from the finite levels `ℤ/ℓᵐ` to
`ℚ̄_ℓ` (`LinearMap.mem_torsion_of_finiteLevel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The open subgroup `pᵐ ℤ_p` of `ℤ_p`. -/
noncomputable def powOpenAddSubgroup (m : ℕ) : OpenAddSubgroup ℤ_[p] where
  toAddSubgroup := (Ideal.span {(p : ℤ_[p]) ^ m}).toAddSubgroup
  isOpen' := by
    convert IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p])
      (zpow_ne_zero (-(m : ℤ)) (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℝ) ≠ 0))
      using 1
    ext x
    rw [Metric.mem_closedBall, dist_zero_right, norm_le_pow_iff_mem_span_pow]
    rfl

variable {p} in
lemma mem_powOpenAddSubgroup {m : ℕ} {x : ℤ_[p]} :
    x ∈ powOpenAddSubgroup p m ↔ x ∈ Ideal.span {(p : ℤ_[p]) ^ m} :=
  Iff.rfl

lemma powOpenAddSubgroup_succ_le (m : ℕ) :
    powOpenAddSubgroup p (m + 1) ≤ powOpenAddSubgroup p m := fun x hx ↦ by
  rw [mem_powOpenAddSubgroup] at hx ⊢
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ m.le_succ) hx

lemma eq_zero_of_forall_mem_powOpenAddSubgroup (x : ℤ_[p])
    (hx : ∀ m, x ∈ powOpenAddSubgroup p m) : x = 0 := by
  have hI : Ideal.span {(p : ℤ_[p])} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact p_nonunit
  have := Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {(p : ℤ_[p])}) hI
  rw [← Ideal.mem_bot, ← this, Submodule.mem_iInf]
  intro m
  rw [Ideal.span_singleton_pow]
  exact hx m

/-- Multiplication by `c` on `ℤ_p`, as a continuous homomorphism. -/
noncomputable def smulHom (c : ℤ_[p]) : ContinuousAddMonoidHom ℤ_[p] ℤ_[p] :=
  ⟨DistribSMul.toAddMonoidHom ℤ_[p] c, continuous_const.mul continuous_id⟩

/-- Multiplication by `c` on the discrete group `ℤ_p / pᵐ`, as a continuous homomorphism. -/
noncomputable def quotientSmulHom (m : ℕ) (c : ℤ_[p]) :
    ContinuousAddMonoidHom (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))
      (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])) :=
  have := QuotientAddGroup.discreteTopology (powOpenAddSubgroup p m).isOpen
  ⟨QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom ℤ_[p] c)
    (fun _ hx ↦ Ideal.mul_mem_left _ c hx), continuous_of_discreteTopology⟩

end PadicInt

namespace AlgebraicGeometry.ProEtale

open PadicInt

variable (S : Scheme.{u}) {A B : Type} [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A] [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- The morphism of sheaves induced by a sum of homomorphisms is the sum. -/
lemma continuousSheafMap_add (φ ψ : ContinuousAddMonoidHom A B) :
    continuousSheafMap S (φ + ψ) = continuousSheafMap S φ + continuousSheafMap S ψ := by
  ext V x
  rfl

lemma continuousSheafMap_congr {φ ψ : ContinuousAddMonoidHom A B} (h : ∀ x, φ x = ψ x) :
    continuousSheafMap S φ = continuousSheafMap S ψ :=
  congrArg _ (ContinuousAddMonoidHom.ext h)

variable (p : ℕ) [Fact p.Prime]

/-- A ring homomorphism `R ⟶ End (C(-, A))` from a family of continuous endomorphisms of `A`
satisfying the ring homomorphism identities. -/
noncomputable def continuousSheafRingHom {R : Type*} [Ring R]
    (μ : R → ContinuousAddMonoidHom A A) (h1 : ∀ x, μ 1 x = x)
    (hmul : ∀ r s x, μ (r * s) x = μ r (μ s x)) (h0 : ∀ x, μ 0 x = 0)
    (hadd : ∀ r s x, μ (r + s) x = μ r x + μ s x) : R →+* End (continuousSheaf S A) where
  toFun r := .of (continuousSheafMap S (μ r))
  map_one' := End.ext ((continuousSheafMap_congr S h1).trans (continuousSheafMap_id S))
  map_mul' r s := End.ext ((continuousSheafMap_congr S (hmul r s)).trans
    (continuousSheafMap_comp S (μ s) (μ r)))
  map_zero' := End.ext ((continuousSheafMap_congr S h0).trans (continuousSheafMap_zero S))
  map_add' r s := End.ext ((continuousSheafMap_congr S (hadd r s)).trans
    (continuousSheafMap_add S (μ r) (μ s)))

/-- The action of `ℤ_p` on the sheaf `C(-, ℤ_p)`. -/
noncomputable def integralSmulRingHom : ℤ_[p] →+* End (continuousSheaf S ℤ_[p]) :=
  continuousSheafRingHom S (smulHom p) (fun x ↦ one_mul x) (fun r s x ↦ mul_assoc r s x)
    (fun x ↦ zero_mul x) (fun r s x ↦ add_mul r s x)

/-- The action of `ℤ_p` on the sheaf `C(-, ℤ_p / pᵐ)`. -/
noncomputable def finiteSmulRingHom (m : ℕ) :
    ℤ_[p] →+* End (continuousSheaf S (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))) :=
  continuousSheafRingHom S (quotientSmulHom p m)
    (fun x ↦ QuotientAddGroup.induction_on x fun a ↦ congrArg QuotientAddGroup.mk (one_mul a))
    (fun r s x ↦ QuotientAddGroup.induction_on x fun a ↦
      congrArg QuotientAddGroup.mk (mul_assoc r s a))
    (fun x ↦ QuotientAddGroup.induction_on x fun a ↦
      (congrArg QuotientAddGroup.mk (zero_mul a)).trans (QuotientAddGroup.mk_zero _))
    (fun r s x ↦ QuotientAddGroup.induction_on x fun a ↦
      (congrArg QuotientAddGroup.mk (add_mul r s a)).trans (QuotientAddGroup.mk_add _ _ _))

/-- The integral `p`-adic pro-étale cohomology `Hⁿ(S, ℤ_p) = Hⁿ(S_proét, C(-, ℤ_p))`, a
`ℤ_p`-module. -/
def IntegralAdicH (n : ℕ) : Type (u + 1) :=
  Sheaf.H (continuousSheaf S ℤ_[p]) n

noncomputable instance (n : ℕ) : AddCommGroup (IntegralAdicH S p n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H (continuousSheaf S ℤ_[p]) n))

noncomputable instance (n : ℕ) : Module ℤ_[p] (IntegralAdicH S p n) :=
  Ext.moduleOfRingHom (integralSmulRingHom S p) n

/-- The pro-étale cohomology `Hⁿ(S, ℤ/pᵐ) = Hⁿ(S_proét, C(-, ℤ_p / pᵐ))`, a `ℤ_p`-module. -/
def FiniteAdicH (m n : ℕ) : Type (u + 1) :=
  Sheaf.H (continuousSheaf S (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))) n

noncomputable instance (m n : ℕ) : AddCommGroup (FiniteAdicH S p m n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H (continuousSheaf S
    (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))) n))

noncomputable instance (m n : ℕ) : Module ℤ_[p] (FiniteAdicH S p m n) :=
  Ext.moduleOfRingHom (finiteSmulRingHom S p m) n

/-- The reduction `C(-, ℤ_p) ⟶ C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev reductionSheafMap (m : ℕ) :
    continuousSheaf S ℤ_[p] ⟶
      continuousSheaf S (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])) :=
  continuousSheafMap S (openAddSubgroupQuotientMk (powOpenAddSubgroup p) m)

lemma reductionSheafMap_comm (m : ℕ) (c : ℤ_[p]) :
    (integralSmulRingHom S p c).asHom ≫ reductionSheafMap S p m =
      reductionSheafMap S p m ≫ (finiteSmulRingHom S p m c).asHom :=
  (continuousSheafMap_comp S _ _).symm.trans
    ((continuousSheafMap_congr S fun _ ↦ rfl).trans (continuousSheafMap_comp S _ _))

/-- The reduction `ρₘ : Hⁿ(S, ℤ_p) ⟶ Hⁿ(S, ℤ/pᵐ)`. -/
noncomputable def reduction (m n : ℕ) : IntegralAdicH S p n →ₗ[ℤ_[p]] FiniteAdicH S p m n :=
  Ext.postcompLinearMap (integralSmulRingHom S p) (finiteSmulRingHom S p m)
    (reductionSheafMap S p m) (reductionSheafMap_comm S p m) n

lemma reduction_apply (m n : ℕ) (x : IntegralAdicH S p n) :
    reduction S p m n x = Ext.comp (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
      x (Ext.mk₀ (reductionSheafMap S p m)) (add_zero n) :=
  rfl


/-- `pᵐ` kills `Hⁿ(S, ℤ/pᵐ)`. -/
lemma pow_smul_finiteAdicH (m n : ℕ) (y : FiniteAdicH S p m n) : (p : ℤ_[p]) ^ m • y = 0 := by
  have h : finiteSmulRingHom S p m ((p : ℤ_[p]) ^ m) = 0 := by
    apply End.ext
    refine (continuousSheafMap_congr S fun x ↦ ?_).trans (continuousSheafMap_zero S)
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine (QuotientAddGroup.eq_zero_iff _).2 ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  change Ext.comp y (Ext.mk₀ (finiteSmulRingHom S p m ((p : ℤ_[p]) ^ m)).asHom)
    (add_zero n) = 0
  rw [h, End.zero_asHom, Ext.mk₀_zero, Ext.comp_zero]

/-- The Bockstein short complex `C(-, ℤ_p) --pᵐ--> C(-, ℤ_p) ⟶ C(-, ℤ_p / pᵐ)`. -/
noncomputable def bocksteinShortComplex (m : ℕ) :
    ShortComplex (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (integralSmulRingHom S p ((p : ℤ_[p]) ^ m)).asHom (reductionSheafMap S p m)
    ((continuousSheafMap_comp S _ _).symm.trans
      ((continuousSheafMap_congr S fun _ ↦ (QuotientAddGroup.eq_zero_iff _).2
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).trans
        (continuousSheafMap_zero S)))

/-- An element of `pᵐ ℤ_p` divided by `pᵐ`. -/
private noncomputable def divPow {m : ℕ} (x : ℤ_[p]) (hx : x ∈ powOpenAddSubgroup p m) :
    ℤ_[p] :=
  Padic.lift ((x : ℚ_[p]) / (p : ℚ_[p]) ^ m) (by
    rw [mem_powOpenAddSubgroup, ← norm_le_pow_iff_mem_span_pow] at hx
    have hp : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
      zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    rw [norm_div, Padic.norm_p_pow, div_le_one hp]
    exact hx)

private lemma pow_mul_divPow {m : ℕ} (x : ℤ_[p]) (hx : x ∈ powOpenAddSubgroup p m) :
    (p : ℤ_[p]) ^ m * divPow p x hx = x := by
  refine Subtype.ext ?_
  change ((p : ℤ_[p]) : ℚ_[p]) ^ m * ((x : ℚ_[p]) / (p : ℚ_[p]) ^ m) = x
  rw [PadicInt.coe_natCast, mul_div_cancel₀ _
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))]

private lemma continuous_divPow {T : Type*} [TopologicalSpace T] {m : ℕ} (f : C(T, ℤ_[p]))
    (hf : ∀ t, f t ∈ powOpenAddSubgroup p m) : Continuous fun t ↦ divPow p (f t) (hf t) :=
  ((continuous_subtype_val.comp f.continuous).div_const _).subtype_mk _

lemma shortExact_bocksteinShortComplex (m : ℕ) : (bocksteinShortComplex S p m).ShortExact := by
  have hp : (p : ℤ_[p]) ^ m ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hinj (V : (Scheme.ProEt S)ᵒᵖ) :
      Function.Injective ((bocksteinShortComplex S p m).f.hom.app V) := fun x y h ↦
    ULift.ext (ContinuousMap.ext fun t ↦ mul_left_cancel₀ hp (congrArg
      (fun z : ULift.{u + 1} C(V.unop.left, ℤ_[p]) ↦ z.down t) h))
  refine .mk' (Sheaf.exact_of_injective_of_exact_sections hinj fun V y hy ↦ ?_) ?_ ?_
  · let y' : ULift.{u + 1} C(V.unop.left, ℤ_[p]) := y
    have hy' (t : V.unop.left) : y'.down t ∈ powOpenAddSubgroup p m :=
      (QuotientAddGroup.eq_zero_iff _).1 (congrArg (fun z : ULift.{u + 1}
        C(V.unop.left, ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])) ↦ z.down t) hy)
    exact ⟨ULift.up ⟨fun t ↦ divPow p _ (hy' t), continuous_divPow p y'.down hy'⟩,
      ULift.ext (ContinuousMap.ext fun t ↦ pow_mul_divPow p _ (hy' t))⟩
  · have (V : (Scheme.ProEt S)ᵒᵖ) :
        Mono (((sheafToPresheaf _ _).map (bocksteinShortComplex S p m).f).app V) :=
      (AddCommGrpCat.mono_iff_injective _).2 (hinj V)
    have : Mono ((sheafToPresheaf _ _).map (bocksteinShortComplex S p m).f) :=
      NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf _ _).mono_of_mono_map this
  · have := QuotientAddGroup.discreteTopology (powOpenAddSubgroup p m).isOpen
    rw [← Sheaf.isLocallySurjective_iff_epi']
    refine Presheaf.isLocallySurjective_of_surjective _ _ fun V s ↦ ?_
    let s' : ULift.{u + 1} C(V.unop.left, ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])) :=
      s
    refine ⟨ULift.up ((⟨fun q ↦ q.out, continuous_of_discreteTopology⟩ :
      C(ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]), ℤ_[p])).comp s'.down), ?_⟩
    exact ULift.ext (ContinuousMap.ext fun t ↦ QuotientAddGroup.out_eq' _)

/-- **Bockstein, first part.** The kernel of `ρₘ : Hⁿ(S, ℤ_p) ⟶ Hⁿ(S, ℤ/pᵐ)` is
`pᵐ Hⁿ(S, ℤ_p)`. -/
theorem exists_eq_pow_smul_of_reduction_eq_zero (m n : ℕ) {x : IntegralAdicH S p n}
    (hx : reduction S p m n x = 0) : ∃ x', x = (p : ℤ_[p]) ^ m • x' := by
  obtain ⟨x', hx'⟩ := Ext.covariant_sequence_exact₂ _ (shortExact_bocksteinShortComplex S p m)
    (n := n) x hx
  exact ⟨x', hx'.symm⟩

/-- The connecting map `δ : Hⁿ(S, ℤ/pᵐ) ⟶ Hⁿ⁺¹(S, ℤ_p)` of the Bockstein sequence. -/
noncomputable def bocksteinδ (m n : ℕ) : FiniteAdicH S p m n →+ IntegralAdicH S p (n + 1) :=
  AddMonoidHom.mk' (fun y ↦ Ext.comp (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    y (shortExact_bocksteinShortComplex S p m).extClass rfl) fun _ _ ↦ Ext.add_comp _ _ _ _

private lemma pow_smul_eq_nsmul_integral (n e : ℕ) (x : IntegralAdicH S p n) :
    (p : ℤ_[p]) ^ e • x = (p ^ e) • x := by
  rw [← Ext.smul_natCast_eq_nsmul (integralSmulRingHom S p) n (p ^ e) x, Nat.cast_pow]

private lemma pow_smul_eq_nsmul_finite (m n e : ℕ) (y : FiniteAdicH S p m n) :
    (p : ℤ_[p]) ^ e • y = (p ^ e) • y := by
  rw [← Ext.smul_natCast_eq_nsmul (finiteSmulRingHom S p m) n (p ^ e) y, Nat.cast_pow]

/-- **Bockstein, second part.** If `pᵉ` kills the `p`-power torsion of `Hⁿ⁺¹(S, ℤ_p)`, then the
image of `ρₘ : Hⁿ(S, ℤ_p) ⟶ Hⁿ(S, ℤ/pᵐ)` contains `pᵉ Hⁿ(S, ℤ/pᵐ)`. -/
theorem pow_smul_mem_range_reduction (m n e : ℕ)
    (he : ∀ x : IntegralAdicH S p (n + 1), (∃ k, (p : ℤ_[p]) ^ k • x = 0) →
      (p : ℤ_[p]) ^ e • x = 0)
    (y : FiniteAdicH S p m n) : (p : ℤ_[p]) ^ e • y ∈ LinearMap.range (reduction S p m n) := by
  have hδ (k : ℕ) : bocksteinδ S p m n ((p : ℤ_[p]) ^ k • y) =
      (p : ℤ_[p]) ^ k • bocksteinδ S p m n y := by
    rw [pow_smul_eq_nsmul_finite, pow_smul_eq_nsmul_integral, map_nsmul]
  have h0 : bocksteinδ S p m n ((p : ℤ_[p]) ^ e • y) = 0 := by
    rw [hδ, he _ ⟨m, by rw [← hδ, pow_smul_finiteAdicH, map_zero]⟩]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _ (shortExact_bocksteinShortComplex S p m)
    ((p : ℤ_[p]) ^ e • y) rfl h0
  exact ⟨x, hx⟩

/-- **Separation in degree `n + 1`.** If the groups `Hⁿ(S, ℤ/pᵐ)` are finite, a class of
`Hⁿ⁺¹(S, ℤ_p)` whose reductions all vanish is zero: `C(-, ℤ_p)` is the limit of the tower of
epimorphisms `C(-, ℤ/pᵐ)`, the pro-étale topos is replete, and `lim¹ Hⁿ(S, ℤ/pᵐ) = 0`. -/
theorem eq_zero_of_forall_reduction_eq_zero_succ (n : ℕ)
    (hfin : ∀ m, Finite (FiniteAdicH S p m n)) (x : IntegralAdicH S p (n + 1))
    (hx : ∀ m, reduction S p m (n + 1) x = 0) : x = 0 := by
  have hU := powOpenAddSubgroup_succ_le p
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := S)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((continuousSheafTower S (powOpenAddSubgroup p) hU).map (homOfLE k.le_succ).op) := by
    rw [continuousSheafTower_map_succ]
    exact (shortExact_continuousSheafShortComplex S (powOpenAddSubgroup p) hU k).epi_g
  refine Ext.eq_zero_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht)
    (isLimitContinuousSheafCone S (powOpenAddSubgroup p) hU
      (eq_zero_of_forall_mem_powOpenAddSubgroup p)) (q := n) (fun y ↦ ?_) x hx
  let F := continuousSheafTower S (powOpenAddSubgroup p) hU
  have (k : ℕ) : Finite (Sheaf.H (F.obj (op k)) n) := hfin k
  obtain ⟨w, hw⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
    (G := fun k ↦ Sheaf.H (F.obj (op k)) n)
    (fun k ↦ (Ext.mk₀ (F.map (homOfLE k.le_succ).op)).postcomp _ (add_zero n)) y
  exact ⟨w, hw⟩

/-- **Separation in degree `0`.** A continuous function to `ℤ_p` whose reductions modulo all
`pᵐ` vanish is zero. -/
theorem eq_zero_of_forall_reduction_eq_zero_zero (x : IntegralAdicH S p 0)
    (hx : ∀ m, reduction S p m 0 x = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  have hf : f = 0 := by
    refine (isLimitContinuousSheafCone S (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p)
      (eq_zero_of_forall_mem_powOpenAddSubgroup p)).hom_ext fun ⟨m⟩ ↦ ?_
    rw [zero_comp]
    refine (Ext.mk₀_bijective _ _).1 ?_
    rw [Ext.mk₀_zero, ← Ext.mk₀_comp_mk₀]
    exact hx m
  rw [hf, Ext.mk₀_zero]

/-- **Separation.** If the groups `Hⁿ⁻¹(S, ℤ/pᵐ)` are finite (no condition for `n = 0`), a class
of `Hⁿ(S, ℤ_p)` whose reductions modulo all `pᵐ` vanish is zero. -/
theorem eq_zero_of_forall_reduction_eq_zero (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (FiniteAdicH S p m k)) (x : IntegralAdicH S p n)
    (hx : ∀ m, reduction S p m n x = 0) : x = 0 := by
  cases n with
  | zero => exact eq_zero_of_forall_reduction_eq_zero_zero S p x hx
  | succ n => exact eq_zero_of_forall_reduction_eq_zero_succ S p n (fun m ↦ hfin m n rfl) x hx

/-- **Finite generation of `ℓ`-adic cohomology.** If the groups `Hⁿ⁻¹(S, ℤ/pᵐ)` and
`Hⁿ(S, ℤ/p)` are finite, then `Hⁿ(S, ℤ_p)` is a finitely generated `ℤ_p`-module. -/
theorem module_finite_integralAdicH (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (FiniteAdicH S p m k)) [Finite (FiniteAdicH S p 1 n)] :
    Module.Finite ℤ_[p] (IntegralAdicH S p n) :=
  PadicInt.module_finite_of_finite_quotient (fun m ↦ reduction S p m n)
    (fun m y ↦ pow_smul_finiteAdicH S p m n y)
    (fun m _ ha ↦ exists_eq_pow_smul_of_reduction_eq_zero S p m n ha)
    (fun a ha ↦ eq_zero_of_forall_reduction_eq_zero S p n hfin a ha)

end AlgebraicGeometry.ProEtale

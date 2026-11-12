import Langlands.GroupScheme.Reductive.WeilGmPurelyInseparableStatement
import Langlands.GroupScheme.Rational.ReductiveSolvableTorus
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.WeilRestrictionCommutative
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Algebra.CharP.Reduced
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.GroupScheme.Rational.SmoothPointedFamilyRigidity
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range

/-! # A pseudo-reductive group that is not reductive: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme

namespace WeilGmPurelyInseparable

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- A finite purely inseparable extension of degree `> 1` has prime characteristic exponent `p`
and an element outside `k` whose `p`-th power lies in `k`. -/
theorem exists_pthRoot [FiniteDimensional k k'] [IsPurelyInseparable k k'] (p : ℕ)
    [ExpChar k p] (h : 1 < Module.finrank k k') :
    p.Prime ∧ ∃ b : k', b ∉ (algebraMap k k').range ∧ b ^ p ∈ (algebraMap k k').range := by
  classical
  have hex : ∃ a : k', a ∉ (algebraMap k k').range := by
    by_contra hall
    push Not at hall
    have hbij : Function.Bijective (algebraMap k k') :=
      ⟨(algebraMap k k').injective, fun a => hall a⟩
    have h1 := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := k) (E := k')).2 hbij
    omega
  obtain ⟨a, ha⟩ := hex
  have hprime : p.Prime := by
    obtain _ | ⟨hp'⟩ := ‹ExpChar k p›
    · obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem k 1 a
      rw [one_pow, pow_one] at hn
      exact absurd hn ha
    · exact hp'
  refine ⟨hprime, ?_⟩
  have hfind : ∃ n : ℕ, a ^ p ^ n ∈ (algebraMap k k').range := IsPurelyInseparable.pow_mem k p a
  have hn : a ^ p ^ Nat.find hfind ∈ (algebraMap k k').range := Nat.find_spec hfind
  have hn0 : Nat.find hfind ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hn
    exact ha hn
  refine ⟨a ^ p ^ (Nat.find hfind - 1),
    Nat.find_min hfind (Nat.sub_lt (Nat.pos_of_ne_zero hn0) one_pos), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  exact hn

/-- If `b ∉ k` has `b ^ p = c ∈ k` and `β ^ p = c` in a nonzero `k`-algebra `R`, then
`1 + (b ⊗ 1 - 1 ⊗ β)` is a unit of `k' ⊗ R` of order `p`. -/
theorem exists_unit_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP k p] {b : k'}
    (hb : b ∉ (algebraMap k k').range) {c : k} (hc : b ^ p = algebraMap k k' c)
    (R : Type u) [CommRing R] [Algebra k R] [Nontrivial R] {β : R}
    (hβ : β ^ p = algebraMap k R c) :
    ∃ v : (k' ⊗[k] R)ˣ, v ≠ 1 ∧ v ^ p = 1 := by
  classical
  let ε : k' ⊗[k] R := b ⊗ₜ 1 - 1 ⊗ₜ β
  -- `ε ≠ 0`: a functional vanishing on `k` and not on `b`.
  have hbspan : b ∉ Submodule.span k {(1 : k')} := by
    intro hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    apply hb
    refine ⟨t, ?_⟩
    rw [← ht, Algebra.smul_def, mul_one]
  obtain ⟨f, hfb, hf1⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hbspan inferInstance
  have hf1' : f 1 = 0 := by
    have : f 1 ∈ (Submodule.span k {(1 : k')}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hf1] at this
    exact (Submodule.mem_bot k).mp this
  let g : k' ⊗[k] R →ₗ[k] R :=
    (TensorProduct.lid k R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id
  have hgε : g ε = algebraMap k R (f b) := by
    simp only [g, ε, map_sub, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, hf1', zero_smul, sub_zero,
      Algebra.algebraMap_eq_smul_one]
  have hε : ε ≠ 0 := by
    intro h0
    have := hgε
    rw [h0, map_zero] at this
    exact hfb ((algebraMap k R).injective (this.symm.trans (map_zero _).symm))
  -- `ε ^ p = 0`.
  have : Nontrivial (k' ⊗[k] R) := ⟨⟨ε, 0, hε⟩⟩
  have : CharP (k' ⊗[k] R) p :=
    charP_of_injective_algebraMap (algebraMap k (k' ⊗[k] R)).injective p
  have : ExpChar (k' ⊗[k] R) p := ExpChar.prime (Fact.out : p.Prime)
  have hεp : ε ^ p = 0 := by
    change (b ⊗ₜ[k] (1 : R) - (1 : k') ⊗ₜ[k] β) ^ p = 0
    rw [sub_pow_expChar, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
      one_pow, one_pow, hc, hβ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, sub_self]
  have hvp : (1 + ε) ^ p = 1 := by
    rw [add_pow_expChar, one_pow, hεp, add_zero]
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hunit : IsUnit (1 + ε) := by
    refine IsUnit.of_mul_eq_one ((1 + ε) ^ (p - 1)) ?_
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0), hvp]
  refine ⟨hunit.unit, ?_, ?_⟩
  · intro h1
    apply hε
    have h2 : (1 + ε : k' ⊗[k] R) = 1 := congrArg Units.val h1
    simpa using h2
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hvp, Units.val_one]

/-- In a field of characteristic `p`, the only `p`-th root of unity is `1`. -/
theorem eq_one_of_pow_char_eq_one {Ω : Type u} [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]
    {x : Ω} (hx : x ^ p = 1) : x = 1 := by
  apply frobenius_inj Ω p
  rw [frobenius_def, frobenius_def, hx, one_pow]

/-- `R_{k'/k}(𝔾ₘ)` is not connected reductive for a finite purely inseparable `k'/k` of degree
`> 1`: otherwise, being commutative, it would be a torus, but over an algebraically closed
field its points contain a nontrivial `p`-th root of unity. -/
theorem not_isConnectedReductive [FiniteDimensional k k'] [IsPurelyInseparable k k']
    (h : 1 < Module.finrank k k') :
    ¬ IsConnectedReductive (WeilGm.groupScheme (CommRingCat.of k) k') := by
  classical
  intro hG
  let G := WeilGm.groupScheme (CommRingCat.of k) k'
  obtain ⟨p, hexp⟩ : ∃ p, ExpChar k p := ⟨ringExpChar k, inferInstance⟩
  obtain ⟨hprime, b, hb, ⟨c, hc⟩⟩ := exists_pthRoot (k := k) (k' := k') p h
  have : Fact p.Prime := ⟨hprime⟩
  have : CharP k p := by
    obtain _ | ⟨_⟩ := hexp
    · exact absurd hprime Nat.not_prime_one
    · infer_instance
  have : IsCommMonObj G.X := WeilGm.isCommMonObj (CommRingCat.of k) k'
  have hT : IsTorus G :=
    hG.isTorus_of_isSolvableGroupScheme (isSolvableGroupScheme_of_isCommMonObj G)
  obtain ⟨K, _, _, I, _, ⟨e⟩⟩ := hT
  let Ω := AlgebraicClosure K
  let T : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let b0 : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Φ₁ := (isoPointsEquiv e T).trans (splitTorus.pointsEquiv I T)
  let Φ₂ := GroupScheme.baseChangePointsEquiv b0 G T
  let Φ₃ := WeilGm.pointsEquiv (CommRingCat.of k) k' ((Over.map b0).obj T)
  let R := ((algΓ (CommRingCat.of k)).obj ((Over.map b0).obj T)).unop
  let ψ : Γ(Spec (CommRingCat.of Ω), ⊤) ≃+* Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  let ψR : R ≃+* Ω := ψ
  have : CharP Ω p :=
    charP_of_injective_ringHom ((algebraMap K Ω).comp (algebraMap k K)).injective p
  have : Nontrivial R := ψR.symm.injective.nontrivial
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (ψR (algebraMap k R c)) hprime.pos
  have hβ : (ψR.symm w) ^ p = algebraMap k R c := by
    rw [← map_pow, hw, RingEquiv.symm_apply_apply]
  obtain ⟨v, hv1, hvp⟩ := exists_unit_pow_eq_one (k := k) (k' := k') p hb hc.symm R hβ
  let x := Φ₂.symm (Φ₃.symm v)
  have hxp : Φ₁ x ^ p = 1 := by
    rw [← map_pow, ← map_pow, ← map_pow, hvp, map_one, map_one, map_one]
  have hx1 : Φ₁ x = 1 := by
    funext i
    apply Units.ext
    apply ψ.injective
    rw [Pi.one_apply, Units.val_one, map_one]
    apply eq_one_of_pow_char_eq_one p
    have hi := congrArg (fun y => ((y i : (Γ(Spec (CommRingCat.of Ω), ⊤))ˣ) :
      Γ(Spec (CommRingCat.of Ω), ⊤))) hxp
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one] at hi
    rw [← map_pow, hi, map_one]
  apply hv1
  have hx : x = 1 := by
    rw [← map_one Φ₁] at hx1
    exact Φ₁.injective hx1
  have : Φ₃.symm v = 1 := by
    rw [← map_one Φ₂.symm] at hx
    exact Φ₂.symm.injective hx
  rw [← map_one Φ₃.symm] at this
  exact Φ₃.symm.injective this

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
/-- The separable closure tensored with a purely inseparable extension is a field. -/
theorem isReduced_tensor_separableClosure [IsPurelyInseparable k k'] :
    IsReduced (k' ⊗[k] SeparableClosure k) := by
  have hF : IsField (k' ⊗[k] SeparableClosure k) :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range k k'
      (SeparableClosure k) (fun y hy => IsPurelyInseparable.inseparable k y hy)
  let : Field (k' ⊗[k] SeparableClosure k) :=
    IsField.toField (R := k' ⊗[k] SeparableClosure k) hF
  infer_instance

/-- Every smooth unipotent closed subgroup of `R_{k'/k}(𝔾ₘ)` is trivial: its points over the
separable closure are `p`-power torsion units of the field `k' ⊗ k_s`, and these points are
dense. -/
theorem hasTrivialUnipotentRadical [FiniteDimensional k k'] [IsPurelyInseparable k k']
    (h : 1 < Module.finrank k k') :
    HasTrivialUnipotentRadical (WeilGm.groupScheme (CommRingCat.of k) k') := by
  classical
  intro H i hi hsm _ hunip _
  let G := WeilGm.groupScheme (CommRingCat.of k) k'
  obtain ⟨p, hexp⟩ : ∃ p, ExpChar k p := ⟨ringExpChar k, inferInstance⟩
  obtain ⟨hprime, -⟩ := exists_pthRoot (k := k) (k' := k') p h
  have : Fact p.Prime := ⟨hprime⟩
  have : CharP k p := by
    obtain _ | ⟨_⟩ := hexp
    · exact absurd hprime Nat.not_prime_one
    · infer_instance
  -- `H` is affine and of finite type, so it has a uniform `p`-power exponent.
  have hGaff : IsAffineHom G.X.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  have hHaff : IsAffineHom H.X.hom := by
    have : IsClosedImmersion i.hom.hom.left := hi
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hunip
  -- Base change to the separable closure.
  let K := SeparableClosure k
  let b := GaloisPointComparison.baseMap k K
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc k K
  have : Surjective b := hb₁
  have : Flat b := hb₂
  have : QuasiCompact b := hb₃
  let HK := (GroupScheme.baseChange b).obj H
  let GK := (GroupScheme.baseChange b).obj G
  let iK := (GroupScheme.baseChange b).map i
  have : Smooth HK.X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  have : IsSeparated GK.X.hom := by
    change IsSeparated (pullback.snd G.X.hom b)
    infer_instance
  have : IsReduced HK.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ HK.X.hom
  have hdense := Langlands.AlgebraicGeometry.PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed
    K HK.X
  have hK : iK.hom.hom = 1 := by
    apply Langlands.AlgebraicGeometry.PointTopology.hom_ext_of_denseRationalPoints hdense
    intro pt
    rw [MonObj.comp_one]
    let q := p ^ r
    have hpt : pt ^ q = 1 := by
      apply (GroupScheme.baseChangePointsEquiv b H _).injective
      rw [map_pow, map_one]
      exact hr _ _
    let y : rationalPoints GK := pt ≫ iK.hom.hom
    have hy : y ^ q = 1 := by
      change (pt ≫ iK.hom.hom) ^ q = 1
      rw [← MonObj.pow_comp, hpt, MonObj.one_comp]
    let u := WeilGm.extensionUnitsEquiv k K k' y
    have hu : u ^ q = 1 := by
      change WeilGm.extensionUnitsEquiv k K k' y ^ q = 1
      rw [← map_pow, hy, map_one]
    have : IsReduced (k' ⊗[k] K) := isReduced_tensor_separableClosure
    have : Nontrivial (k' ⊗[k] K) := ⟨⟨u, 0, (Units.ne_zero u)⟩⟩
    have : CharP (k' ⊗[k] K) p :=
      charP_of_injective_algebraMap (algebraMap k (k' ⊗[k] K)).injective p
    have : ExpChar (k' ⊗[k] K) p := ExpChar.prime hprime
    have hu1 : u = 1 := by
      apply Units.ext
      rw [Units.val_one]
      have hnil : IsNilpotent ((u : k' ⊗[k] K) - 1) := by
        refine ⟨q, ?_⟩
        rw [sub_pow_expChar_pow, one_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, sub_self]
      exact sub_eq_zero.mp (IsNilpotent.eq_zero hnil)
    have hy1 : y = 1 := by
      apply (WeilGm.extensionUnitsEquiv k K k').injective
      rw [map_one]
      exact hu1
    exact hy1
  have hi1 : i.hom.hom = 1 := by
    apply (Over.pullback b).map_injective
    rw [Functor.map_one]
    exact hK
  ext T x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨y, rfl⟩
    rw [hi1, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

/-! ### Connectedness: an explicit coordinate algebra -/

section Coordinates

variable {n : ℕ} (b : Module.Basis (Fin n) k k') (q : ℕ) (c : Fin n → k)

/-- The polynomial `∑ cᵢ Xᵢ^q`, the `q`-th power of the generic element `∑ bᵢ Xᵢ` when
`bᵢ^q = cᵢ`. -/
def powPoly : MvPolynomial (Fin n) k :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i ^ q

/-- The coordinates `r ↦ ∑ bᵢ ⊗ rᵢ` of `k' ⊗ R`. -/
def coordEquiv (R : Type u) [CommRing R] [Algebra k R] : (Fin n → R) ≃ k' ⊗[k] R :=
  (Algebra.TensorProduct.basis R b).equivFun.symm.toEquiv.trans
    (TensorProduct.comm k R k').toEquiv

theorem coordEquiv_apply (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R) :
    coordEquiv b R r = ∑ i, b i ⊗ₜ[k] r i := by
  simp only [coordEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, map_sum,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.comm_tmul]

theorem lTensor_coordEquiv {R S : Type u} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (g : R →ₐ[k] S) (r : Fin n → R) :
    Algebra.TensorProduct.lTensor (S := k') k' g (coordEquiv b R r) =
      coordEquiv b S (fun i => g (r i)) := by
  rw [coordEquiv_apply, coordEquiv_apply, map_sum]
  simp

variable {b q c}
variable (p m : ℕ) [Fact p.Prime] [CharP k p]

theorem coordEquiv_pow (hc : ∀ i, algebraMap k k' (c i) = b i ^ (p ^ m))
    (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R) :
    coordEquiv b R r ^ (p ^ m) =
      (1 : k') ⊗ₜ[k] MvPolynomial.aeval r (powPoly (p ^ m) c) := by
  by_cases hR : Nontrivial (k' ⊗[k] R)
  · have : CharP (k' ⊗[k] R) p :=
      charP_of_injective_algebraMap (algebraMap k (k' ⊗[k] R)).injective p
    have : ExpChar (k' ⊗[k] R) p := ExpChar.prime (Fact.out : p.Prime)
    rw [coordEquiv_apply, sum_pow_char_pow]
    simp only [powPoly, map_sum, map_mul, MvPolynomial.aeval_C, map_pow, MvPolynomial.aeval_X,
      TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_mul_assoc, one_mul]
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact Subsingleton.elim _ _

omit [Fact p.Prime] [CharP k p] in
/-- A tensor `1 ⊗ s` is a unit only if `s` is. -/
theorem isUnit_of_isUnit_one_tmul (R : Type u) [CommRing R] [Algebra k R] {s : R}
    (hs : IsUnit ((1 : k') ⊗ₜ[k] s)) : IsUnit s := by
  classical
  have h1 : (1 : k') ∉ (⊥ : Submodule k k') := by
    rw [Submodule.mem_bot]
    exact one_ne_zero
  obtain ⟨f, hf1, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h1 inferInstance
  let g : k' →ₗ[k] k := (f 1)⁻¹ • f
  have hg : g 1 = 1 := by
    simp only [g, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hf1
  let φ : k' ⊗[k] R →ₗ[k] R := (TensorProduct.lid k R).toLinearMap ∘ₗ LinearMap.rTensor R g
  have hφ : ∀ y : k' ⊗[k] R, φ (((1 : k') ⊗ₜ[k] s) * y) = s * φ y := by
    intro y
    induction y with
    | tmul a r =>
      simp only [φ, Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.comp_apply,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, mul_smul_comm]
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
  obtain ⟨u, hu⟩ := hs
  refine IsUnit.of_mul_eq_one (φ ↑u⁻¹) ?_
  rw [← hφ, ← hu, Units.mul_inv]
  change φ ((1 : k') ⊗ₜ[k] (1 : R)) = 1
  simp only [φ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, hg, one_smul]

/-- `x ∈ k' ⊗ R` with coordinates `r` is a unit exactly when `∑ cᵢ rᵢ^q` is. -/
theorem isUnit_coordEquiv_iff (hc : ∀ i, algebraMap k k' (c i) = b i ^ (p ^ m))
    (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R) :
    IsUnit (coordEquiv b R r) ↔ IsUnit (MvPolynomial.aeval r (powPoly (p ^ m) c)) := by
  rw [← isUnit_pow_iff (pow_ne_zero m (Fact.out : p.Prime).ne_zero), coordEquiv_pow p m hc]
  refine ⟨isUnit_of_isUnit_one_tmul R, fun h => ?_⟩
  exact h.map (Algebra.TensorProduct.includeRight : R →ₐ[k] k' ⊗[k] R)

end Coordinates

section Corepresentation

variable {n : ℕ} {b : Module.Basis (Fin n) k k'} {c : Fin n → k}
variable (p m : ℕ) [Fact p.Prime] [CharP k p]

/-- The localized polynomial algebra `k[X₁, …, Xₙ][(∑ cᵢ Xᵢ^q)⁻¹]`. -/
abbrev locAlg (q : ℕ) (c : Fin n → k) : Type u := Localization.Away (powPoly q c)

omit [Fact p.Prime] [CharP k p] in
theorem aeval_powPoly_isUnit (R : Type u) [CommRing R] [Algebra k R]
    (f : locAlg (p ^ m) c →ₐ[k] R) :
    IsUnit (MvPolynomial.aeval
      (fun i => f (algebraMap (MvPolynomial (Fin n) k) (locAlg (p ^ m) c) (MvPolynomial.X i)))
      (powPoly (p ^ m) c)) := by
  have hcomp : f.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (locAlg (p ^ m) c)) =
      MvPolynomial.aeval
        (fun i => f (algebraMap (MvPolynomial (Fin n) k) (locAlg (p ^ m) c) (MvPolynomial.X i))) :=
    MvPolynomial.algHom_ext fun i => by simp
  rw [← hcomp]
  exact (IsLocalization.Away.algebraMap_isUnit (powPoly (p ^ m) c)).map f

omit [Fact p.Prime] [CharP k p] in
theorem lift_algebraMap (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R)
    (hr : IsUnit (MvPolynomial.aeval r (powPoly (p ^ m) c))) (x : MvPolynomial (Fin n) k) :
    IsLocalization.Away.liftAlgHom (powPoly (p ^ m) c) (f := MvPolynomial.aeval r) hr
        (algebraMap (MvPolynomial (Fin n) k) (locAlg (p ^ m) c) x) = MvPolynomial.aeval r x := by
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

variable [FiniteDimensional k k']

/-- `k[X][(∑ cᵢ Xᵢ^q)⁻¹]` corepresents `R ↦ (k' ⊗ R)ˣ`. -/
def corep (hc : ∀ i, algebraMap k k' (c i) = b i ^ (p ^ m)) :
    (WeilGm.functor (CommRingCat.of k) k' ⋙ forget GrpCat).CorepresentableBy
      (CommAlgCat.of (CommRingCat.of k) (locAlg (p ^ m) c)) where
  homEquiv {R} :=
    { toFun := fun f =>
        ((isUnit_coordEquiv_iff p m hc R _).2 (aeval_powPoly_isUnit p m R f.hom)).unit
      invFun := fun u =>
        let u' : (k' ⊗[k] R)ˣ := u
        CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (powPoly (p ^ m) c)
          (f := MvPolynomial.aeval ((coordEquiv b R).symm (u' : k' ⊗[k] R)))
          ((isUnit_coordEquiv_iff p m hc R _).1 (by
            rw [Equiv.apply_symm_apply]
            exact u'.isUnit)))
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        apply AlgHom.coe_ringHom_injective
        apply IsLocalization.ringHom_ext (Submonoid.powers (powPoly (p ^ m) c))
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
          rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
            AlgHom.commutes, AlgHom.commutes]
        · intro i
          simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
          erw [lift_algebraMap]
          simp only [MvPolynomial.aeval_X, IsUnit.unit_spec, Equiv.symm_apply_apply]
      right_inv := fun u => by
        let u' : (k' ⊗[k] R)ˣ := u
        apply Units.ext
        change coordEquiv b R _ = (u' : k' ⊗[k] R)
        conv_rhs => rw [← Equiv.apply_symm_apply (coordEquiv b R) (u' : k' ⊗[k] R)]
        congr 1
        funext i
        dsimp only
        erw [lift_algebraMap]
        simp only [MvPolynomial.aeval_X]
        rfl }
  homEquiv_comp {R R'} g f := by
    apply Units.ext
    change coordEquiv b R' _ =
      Algebra.TensorProduct.lTensor (S := k') k' g.hom (coordEquiv b R _)
    rw [lTensor_coordEquiv]
    rfl

end Corepresentation

/-- Some `p ^ m` sends every vector of a finite family into `k`. -/
theorem exists_pow_mem_range [IsPurelyInseparable k k'] (p : ℕ) [ExpChar k p] {J : Type*}
    [Fintype J] (v : J → k') : ∃ m : ℕ, ∀ i, v i ^ p ^ m ∈ (algebraMap k k').range := by
  classical
  choose N hN using fun i => IsPurelyInseparable.pow_mem k p (v i)
  refine ⟨Finset.univ.sup N, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := N) (Finset.mem_univ i))
  rw [hd, pow_add, pow_mul]
  exact pow_mem (hN i) _

theorem powPoly_ne_zero {n : ℕ} (hn : 0 < n) {q : ℕ} (hq : q ≠ 0) (c : Fin n → k)
    (hc0 : ∀ i, c i ≠ 0) : powPoly q c ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPolynomial.eval (Pi.single (⟨0, hn⟩ : Fin n) (1 : k))) h0
  simp only [powPoly, map_sum, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
    Pi.single_apply, ite_pow, one_pow, zero_pow hq, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero] at h1
  exact hc0 _ h1

/-- `R_{k'/k}(𝔾ₘ)` is connected: its coordinate algebra is a localization of a polynomial
ring. -/
theorem connectedSpace_groupScheme [FiniteDimensional k k'] [IsPurelyInseparable k k']
    (h : 1 < Module.finrank k k') :
    ConnectedSpace (WeilGm.groupScheme (CommRingCat.of k) k').X.left := by
  classical
  obtain ⟨p, hexp⟩ : ∃ p, ExpChar k p := ⟨ringExpChar k, inferInstance⟩
  obtain ⟨hprime, -⟩ := exists_pthRoot (k := k) (k' := k') p h
  have : Fact p.Prime := ⟨hprime⟩
  have : CharP k p := by
    obtain _ | ⟨_⟩ := hexp
    · exact absurd hprime Nat.not_prime_one
    · infer_instance
  let b : Module.Basis (Fin (Module.finrank k k')) k k' := Module.finBasis k k'
  obtain ⟨m, hm⟩ := exists_pow_mem_range (k := k) (k' := k') p b
  simp only [RingHom.mem_range] at hm
  choose c hc using hm
  have hq : p ^ m ≠ 0 := pow_ne_zero m hprime.ne_zero
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i hci
    have h2 := hc i
    rw [hci, map_zero] at h2
    exact b.ne_zero i ((pow_eq_zero_iff hq).mp h2.symm)
  have hN : powPoly (p ^ m) c ≠ 0 := powPoly_ne_zero (by omega) hq c hc0
  have : IsDomain (locAlg (p ^ m) c) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hN)
  let e := corep (k := k) (k' := k') (b := b) p m hc
  let iso := (WeilGm.corepresentableBy (CommRingCat.of k) k').uniqueUpToIso e
  let isoS := (Over.forget _).mapIso ((algSpec (CommRingCat.of k)).mapIso iso.op.symm)
  have hP : ConnectedSpace (Spec (CommRingCat.of (locAlg (p ^ m) c))) := inferInstance
  have : ConnectedSpace ((Over.forget (Spec (CommRingCat.of k))).obj
      ((algSpec (CommRingCat.of k)).obj
        (Opposite.op (CommAlgCat.of (CommRingCat.of k) (locAlg (p ^ m) c))))) := hP
  exact (Scheme.homeoOfIso isoS.symm).surjective.connectedSpace
    (Scheme.homeoOfIso isoS.symm).continuous

end WeilGmPurelyInseparable

open WeilGmPurelyInseparable in
/-- **CGP Example 1.1.3.** For a finite purely inseparable extension `k'/k` of degree `> 1`,
`R_{k'/k}(𝔾ₘ)` is pseudo-reductive and not connected reductive. -/
theorem weilGmPurelyInseparablePseudoReductive :
    WeilGmPurelyInseparablePseudoReductiveStatement.{u} := by
  intro k k' _ _ _ _ _ h
  refine ⟨{ smooth := WeilGm.smooth _ _
            isAffineHom := ?_
            connectedSpace := connectedSpace_groupScheme h
            hasTrivialUnipotentRadical := hasTrivialUnipotentRadical h },
    not_isConnectedReductive h⟩
  change IsAffineHom (Spec.map _)
  infer_instance

end Langlands.GroupScheme

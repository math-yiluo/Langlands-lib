import Langlands.BushnellKutzko.MinimalSimpleStratumResidue
import Langlands.BushnellKutzko.MinimalElement

/-! # Ramification index and residue degree of a minimal generator

Let `E` be a field acting on `V` whose units normalize a lattice chain of period `e`, and let
`β ∈ E` be a minimal generator (`IsMinimalOver`, Bushnell–Kutzko (1993), (1.4.14), printed
p. 41) shifting the chain by `-n`. Put `g = gcd(e, n)`.
`LatticeChain.ramificationIndex_and_residue_adjoin_of_isMinimalOver` shows that
`e(E|F) = e / g` and that the residue of the integral unit `ϖ^{n/g} β^{e/g}` generates the residue
field of `E` over `𝒪_F`, for any prime element `ϖ` of `F`. These are the formulas (1.5) of
Bushnell–Kutzko (1994), printed p. 113. `LatticeChain.isMinimalOver_of_mem_range` treats a
generator in the image of `F`, where the extension is trivial.

`natDegree_minpoly_eq_finrank_of_adjoin_eq_top` and `subfieldResidueDegree_eq_finrank` identify the
residue degree `subfieldResidueDegree F E` with the degree of the minimal polynomial over `k_F` of a
generator of the residue field of `E`.
-/

open ValuativeRel IsLocalRing IsDiscreteValuationRing

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

/-- Generation of the residue ring of the minimality condition gives generation of the residue
field. -/
theorem residue_adjoin_eq_top_of_mk {F : Type uF} [Field F] [ValuativeRel F] (E : Type uE)
    [Field E] [Algebra F E] [IsDiscreteValuationRing 𝒪ₑ[F,E]] (a : 𝒪ₑ[F,E])
    (h : Algebra.adjoin 𝒪[F]
        ({Ideal.Quotient.mk (subfieldMaximalIdeal F E) a} : Set (subfieldResidueRing F E)) = ⊤) :
    Algebra.adjoin 𝒪[F] ({residue 𝒪ₑ[F,E] a} : Set (ResidueField 𝒪ₑ[F,E])) = ⊤ := by
  let f := subfieldResidueEquiv (F := F) E
  have hr : f.toAlgHom.range = ⊤ := by
    apply top_unique
    intro y _
    exact f.surjective y
  have hm : (Algebra.adjoin 𝒪[F]
      ({Ideal.Quotient.mk (subfieldMaximalIdeal F E) a} : Set (subfieldResidueRing F E))).map
        f.toAlgHom = Algebra.adjoin 𝒪[F] ({residue 𝒪ₑ[F,E] a} : Set (ResidueField 𝒪ₑ[F,E])) := by
    rw [AlgHom.map_adjoin_singleton]
    rfl
  rw [← hm, h, Algebra.map_top, hr]

namespace LatticeChain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
  [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]

/-- For a minimal generator `β` of shift `-n`, the unit `ϖ^{n/g} β^{e/g}` of shift zero has
residue generating the residue field, and the ramification index of `E` is `e / g`, where
`g = gcd(e, n)`. -/
theorem ramificationIndex_and_residue_adjoin_of_isMinimalOver (β : Eˣ) {n : ℤ}
    (hβ : (𝓛.fieldShift E hE β).toAdd = -n) (hmin : IsMinimalOver F E (β : E))
    {π : 𝒪[F]} (hπ : Irreducible π) (w : 𝒪ₑ[F,E]ˣ)
    (hw : baseIntegerUnit E hπ.ne_zero ^ (n / (Nat.gcd 𝓛.period n.natAbs : ℤ)) *
      β ^ (𝓛.period / Nat.gcd 𝓛.period n.natAbs) = subfieldIntegerUnits E w) :
    subfieldRamificationIndex F E = 𝓛.period / Nat.gcd 𝓛.period n.natAbs ∧
      Algebra.adjoin 𝒪[F] ({residue 𝒪ₑ[F,E] (w : 𝒪ₑ[F,E])} : Set (ResidueField 𝒪ₑ[F,E])) =
        ⊤ := by
  obtain ⟨-, ν, hν, hcop, π₀, -, hπ₀span, y₀, hy₀, hres⟩ := hmin
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪ₑ[F,E]
  obtain ⟨ν', u', hu'⟩ := subfieldUnit_factorization E hϖ β
  have hval := 𝓛.subfieldNormalizedValuation_eq_of_factorization E hE hϖ hu'
  have hνν : ν' = ν := WithTop.coe_injective (hval.symm.trans hν)
  subst hνν
  set t : ℤ := (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd with htdef
  have ht : 0 < t := 𝓛.fieldShift_uniformizer_pos E hE hϖ
  have hte : t * (subfieldRamificationIndex F E : ℤ) = 𝓛.period :=
    𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ
  have hb := 𝓛.fieldShift_eq_mul_of_factorization E hE hϖ.ne_zero hu'
  rw [← htdef, hβ] at hb
  have hn : n = t * -ν' := by linarith
  set e' := subfieldRamificationIndex F E with he'def
  have hperiod : 𝓛.period = t.toNat * e' := by
    have : ((t.toNat * e' : ℕ) : ℤ) = 𝓛.period := by
      push_cast
      rw [Int.toNat_of_nonneg ht.le]
      exact hte
    exact_mod_cast this.symm
  have hnabs : n.natAbs = t.toNat * ν'.natAbs := by
    rw [hn, Int.natAbs_mul, Int.natAbs_neg]
    congr 1
    omega
  have hgcd : Nat.gcd 𝓛.period n.natAbs = t.toNat := by
    rw [hperiod, hnabs, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop.symm, mul_one]
  have htpos : 0 < t.toNat := by omega
  have hdiv : 𝓛.period / Nat.gcd 𝓛.period n.natAbs = e' := by
    rw [hgcd, hperiod, Nat.mul_div_cancel_left _ htpos]
  have hndiv : n / (Nat.gcd 𝓛.period n.natAbs : ℤ) = -ν' := by
    rw [hgcd, Int.toNat_of_nonneg ht.le, hn, Int.mul_ediv_cancel_left _ ht.ne']
  refine ⟨hdiv.symm, ?_⟩
  have hπ₀ : Irreducible π₀ := (irreducible_iff_uniformizer π₀).mpr hπ₀span.symm
  obtain ⟨v, hv⟩ := associated_of_irreducible 𝒪[F] hπ₀ hπ
  have hv0 : algebraMap 𝒪[F] E (v : 𝒪[F]) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap 𝒪[F] E) (v.mul_inv)
    rw [map_mul, h, zero_mul, map_one] at h'
    exact zero_ne_one h'
  have hwE : ((w : 𝒪ₑ[F,E]) : E) =
      algebraMap 𝒪[F] E (v : 𝒪[F]) ^ (-ν') * (y₀ : E) := by
    have h := congrArg (fun z : Eˣ => (z : E)) hw
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      baseIntegerUnit_val] at h
    rw [hndiv, hdiv] at h
    rw [hy₀]
    change _ = _ at h
    rw [show ((w : 𝒪ₑ[F,E]) : E) = algebraMap F E (π : F) ^ (-ν') * (β : E) ^ e' from h.symm,
      ← hv, MulMemClass.coe_mul, map_mul, mul_zpow, IsScalarTower.algebraMap_apply 𝒪[F] F E,
      show algebraMap 𝒪[F] F (v : 𝒪[F]) = ((v : 𝒪[F]) : F) from rfl]
    ring
  have hvE : algebraMap 𝒪[F] E ((v ^ ν' : 𝒪[F]ˣ) : 𝒪[F]) =
      algebraMap 𝒪[F] E (v : 𝒪[F]) ^ ν' := by
    have h1 : ((Units.map (algebraMap 𝒪[F] E).toMonoidHom (v ^ ν') : Eˣ) : E) =
        algebraMap 𝒪[F] E ((v ^ ν' : 𝒪[F]ˣ) : 𝒪[F]) := rfl
    rw [← h1, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hy₀w : (y₀ : 𝒪ₑ[F,E]) =
      algebraMap 𝒪[F] 𝒪ₑ[F,E] ((v ^ ν' : 𝒪[F]ˣ) : 𝒪[F]) * w := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, Subalgebra.coe_algebraMap, hvE, hwE, ← mul_assoc,
      ← zpow_add₀ hv0, add_neg_cancel, zpow_zero, one_mul]
  have hres' := residue_adjoin_eq_top_of_mk E y₀ hres
  rw [eq_top_iff, ← hres']
  apply Algebra.adjoin_le
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [hy₀w, map_mul]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)

include 𝓛 hE in
/-- A generator lying in the image of the base field is minimal: the extension is trivial. -/
theorem isMinimalOver_of_mem_range (β : Eˣ) (hgen : Algebra.adjoin F ({(β : E)} : Set E) = ⊤)
    (hscalar : ∃ a : F, algebraMap F E a = β) : IsMinimalOver F E (β : E) := by
  obtain ⟨a, ha⟩ := hscalar
  have hbot : ∀ x : E, ∃ c : F, algebraMap F E c = x := by
    intro x
    have hle : Algebra.adjoin F ({(β : E)} : Set E) ≤ ⊥ := by
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, SetLike.mem_coe, Algebra.mem_bot]
      exact ⟨a, ha⟩
    rw [hgen] at hle
    exact Algebra.mem_bot.mp (hle Algebra.mem_top)
  have hinjE : Function.Injective (algebraMap 𝒪[F] E) := by
    rw [IsScalarTower.algebraMap_eq 𝒪[F] F E]
    exact (algebraMap F E).injective.comp Subtype.val_injective
  have hinj : Function.Injective (algebraMap 𝒪[F] 𝒪ₑ[F,E]) := by
    intro x y hxy
    apply hinjE
    exact congrArg (fun z : 𝒪ₑ[F,E] => (z : E)) hxy
  have hsurj : Function.Surjective (algebraMap 𝒪[F] 𝒪ₑ[F,E]) := by
    intro x
    obtain ⟨c, hc⟩ := hbot (x : E)
    have hxint : IsIntegral 𝒪[F] (x : E) := x.prop
    rw [← hc] at hxint
    have hcint : IsIntegral 𝒪[F] c :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).mp
        hxint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
    refine ⟨y, Subtype.ext ?_⟩
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[F] F E, hy, hc]
  let φ : 𝒪[F] ≃+* 𝒪ₑ[F,E] := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  obtain ⟨π₀, hπ₀⟩ := exists_irreducible 𝒪[F]
  have hϖ : Irreducible (algebraMap 𝒪[F] 𝒪ₑ[F,E] π₀) := by
    have : φ π₀ = algebraMap 𝒪[F] 𝒪ₑ[F,E] π₀ := rfl
    rw [← this, MulEquiv.irreducible_iff]
    exact hπ₀
  have hunit : subfieldIntegerUnit E hϖ.ne_zero = baseIntegerUnit E hπ₀.ne_zero := by
    apply Units.ext
    rw [subfieldIntegerUnit_val, baseIntegerUnit_val, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply 𝒪[F] F E]
    rfl
  have hram : subfieldRamificationIndex F E = 1 := by
    have h := 𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ
    have hb := 𝓛.fieldShift_baseUniformizer E hE hπ₀
    change (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd * _ = _ at h
    change (𝓛.fieldShift E hE (baseIntegerUnit E hπ₀.ne_zero)).toAdd = _ at hb
    rw [hunit, hb] at h
    have hp : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    have h1 : (𝓛.period : ℤ) * (subfieldRamificationIndex F E : ℤ) = (𝓛.period : ℤ) * 1 := by
      rw [h, mul_one]
    exact_mod_cast mul_left_cancel₀ hp.ne' h1
  obtain ⟨ν, u, hu⟩ := subfieldUnit_factorization E hϖ β
  have hval := 𝓛.subfieldNormalizedValuation_eq_of_factorization E hE hϖ hu
  refine ⟨hgen, ν, hval, by rw [hram]; exact Nat.coprime_one_right _, π₀, hπ₀.ne_zero,
    hπ₀.maximalIdeal_eq.symm, (u : 𝒪ₑ[F,E]), ?_, ?_⟩
  · have hβE := congrArg (fun z : Eˣ => (z : E)) hu
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, subfieldIntegerUnit_val] at hβE
    rw [hram, pow_one, hβE]
    have hϖE : ((algebraMap 𝒪[F] 𝒪ₑ[F,E] π₀ : 𝒪ₑ[F,E]) : E) = algebraMap F E (π₀ : F) := by
      rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[F] F E]
      rfl
    have hne : algebraMap F E (π₀ : F) ≠ 0 := by
      rw [← hϖE]
      exact fun h => hϖ.ne_zero (Subtype.ext h)
    rw [hϖE, ← mul_assoc, mul_comm (algebraMap F E (π₀ : F) ^ (-ν)), mul_assoc,
      ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one]
    rfl
  · apply eq_top_iff.mpr
    intro z _
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, rfl⟩ := hsurj x
    exact Subalgebra.algebraMap_mem _ y

end LatticeChain

section Residue

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E]
  [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E])]

/-- An element generating the residue field over the base integers has minimal polynomial of
degree the residue degree. -/
theorem natDegree_minpoly_eq_finrank_of_adjoin_eq_top (c : ResidueField 𝒪ₑ[F,E])
    (hc : IsIntegral (ResidueField 𝒪[F]) c)
    (h : Algebra.adjoin 𝒪[F] ({c} : Set (ResidueField 𝒪ₑ[F,E])) = ⊤) :
    (minpoly (ResidueField 𝒪[F]) c).natDegree =
      Module.finrank (ResidueField 𝒪[F]) (ResidueField 𝒪ₑ[F,E]) := by
  have h' : Algebra.adjoin (ResidueField 𝒪[F]) ({c} : Set (ResidueField 𝒪ₑ[F,E])) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin 𝒪[F] ({c} : Set (ResidueField 𝒪ₑ[F,E])) := h ▸ Algebra.mem_top
    have hle : Algebra.adjoin 𝒪[F] ({c} : Set (ResidueField 𝒪ₑ[F,E])) ≤
        (Algebra.adjoin (ResidueField 𝒪[F]) ({c} : Set (ResidueField 𝒪ₑ[F,E]))).restrictScalars
          𝒪[F] :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle hx
  have hIF : IntermediateField.adjoin (ResidueField 𝒪[F]) ({c} : Set (ResidueField 𝒪ₑ[F,E])) =
      ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hc.isAlgebraic, h',
      IntermediateField.top_toSubalgebra]
  rw [← IntermediateField.adjoin.finrank hc, hIF, IntermediateField.finrank_top']

/-- The residue degree, defined as a length, is the dimension of the residue field of `E` over
that of `F`. -/
theorem subfieldResidueDegree_eq_finrank [FiniteDimensional F E] :
    subfieldResidueDegree F E =
      Module.finrank (ResidueField 𝒪[F]) (ResidueField 𝒪ₑ[F,E]) := by
  rw [PureApproximation.subfieldResidueDegree_eq_inertiaDeg,
    Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal 𝒪[F]) (maximalIdeal 𝒪ₑ[F,E])]
  rfl

end Residue



end Langlands.BushnellKutzko

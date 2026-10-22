import Langlands.ClassFieldTheory.Local.UnramifiedInvariantCompatibilityStatement
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Cohomology.CyclicH2.Proof
import Langlands.Weil.Local.ExtensionResidue

/-! # Base-change degree scaling of the finite unramified invariant -/

noncomputable section

open CategoryTheory IsLocalRing

namespace Langlands.ClassFieldTheory.Local

universe u

namespace UnramifiedBaseChange

/-! ### Carry sums -/

/-- Summing the carry identity along the multiples of `t` telescopes. -/
theorem carry_sum_telescope {n : ℕ} [NeZero n] (t : ZMod n) (m : ℕ) :
    n * ∑ i ∈ Finset.range m, cyclicCarry (i • t) t + (m • t).val = m * t.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := cyclicCarry_spec (m • t) t
    rw [Finset.sum_range_succ, succ_nsmul, mul_add]
    nlinarith

/-! ### Cyclic H2 classes from cocycle sums -/

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- A cocycle whose generator sum is a base unit `b` is sent by the cyclic norm
comparison to the class of `b`. -/
theorem cyclicH2NormEquiv_H2π_of_sum
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (c : groupCohomology.cocycles₂ (unitsRepresentation K L)) (b : Kˣ)
    (hc : ∑ i ∈ Finset.range (Module.finrank K L), c (σ ^ i, σ) = baseUnit K L b) :
    cyclicH2NormEquiv K L σ hσ (groupCohomology.H2π (unitsRepresentation K L) c) =
      Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L b) := by
  let : Fintype Gal(L/K) := Fintype.ofFinite _
  let : IsCyclic Gal(L/K) := ⟨σ, hσ⟩
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A := unitsRepresentation K L
  let x : LinearMap.ker (Rep.applyAsHom A σ - 𝟙 A).hom.toLinearMap :=
    ⟨baseUnit K L b, by
      change A.ρ σ (baseUnit K L b) - baseUnit K L b = 0
      rw [baseUnit_fixed, sub_self]⟩
  have hcard : Fintype.card Gal(L/K) = Module.finrank K L := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  have h := Langlands.Cohomology.CyclicH2.cocycleSumComparison IntegerScalars Gal(L/K) A σ hσ
    c x (by rw [hcard]; exact hc.symm)
  change invariantsModNormEquiv K L
    (cyclicH2InvariantsEquiv K L σ hσ (groupCohomology.H2π A c)) = _
  rw [h]
  apply (invariantsModNormEquiv K L).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change _ = (invariantsModNormEquiv K L).symm
    ((Langlands.LocalClassField.normQuotientProjection K L).toAdditive (Additive.ofMul b))
  rw [invariantsModNormEquiv_symm_projection]
  simp only [cyclicH2InvariantsEquiv, Rep.FiniteCyclicGroup.groupCohomologyπEven,
    LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, Iso.trans_hom,
    ModuleCat.comp_apply]
  dsimp only [A]
  simp only [← ConcreteCategory.comp_apply, Category.assoc,
    ShortComplex.moduleCatCyclesIso_inv_π_assoc, Iso.inv_hom_id,
    Category.comp_id]
  rfl

/-- A power of a base unit is the corresponding multiple in additive notation. -/
theorem baseUnit_pow (K L : Type u) [Field K] [Field L] [Algebra K L] (a : Kˣ) (k : ℕ) :
    baseUnit K L (a ^ k) = k • baseUnit K L a := by
  change (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom (a ^ k)) : Additive Lˣ) =
    k • (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a) : Additive Lˣ)
  rw [map_pow, ofMul_pow]

/-- Generator sums of the carry cocycle are base units. -/
theorem cyclicUnitCocycle_sum (K L : Type u) [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ)
    (σ : Gal(L/K)) (m : ℕ) :
    ∑ i ∈ Finset.range m, cyclicUnitCocycle K L χ a (σ ^ i, σ) =
      baseUnit K L (a ^ ∑ i ∈ Finset.range m, cyclicCarry (i • (χ σ).toAdd) (χ σ).toAdd) := by
  rw [baseUnit_pow, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  change cyclicCarry (χ (σ ^ i)).toAdd (χ σ).toAdd • baseUnit K L a = _
  rw [map_pow, toAdd_pow]

/-- For `n > 1` the carries along the multiples of `1` add up to one. -/
theorem carry_sum_one {n : ℕ} [NeZero n] (hn : 1 < n) :
    ∑ i ∈ Finset.range n, cyclicCarry (i • (1 : ZMod n)) 1 = 1 := by
  have : Fact (1 < n) := ⟨hn⟩
  have h := carry_sum_telescope (1 : ZMod n) n
  have h1 : (n • (1 : ZMod n)).val = 0 := by simp
  rw [h1, ZMod.val_one, add_zero] at h
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) h

/-- The positive generator of a cyclic coordinate has order dividing `d`. -/
theorem coordinateGenerator_pow_card {G : Type*} [Group G] {d : ℕ}
    (χ : G ≃* Multiplicative (ZMod d)) : cyclicCoordinateGenerator χ ^ d = 1 := by
  apply χ.injective
  rw [map_pow, cyclicCoordinateGenerator, χ.apply_symm_apply, ← ofAdd_nsmul, nsmul_one,
    ZMod.natCast_self, ofAdd_zero, map_one]

/-- Every class is a positive carry class when the degree exceeds one. -/
theorem exists_cyclicClass_eq (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [NeZero (Module.finrank K L)]
    (χ : Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)))
    (hn : 1 < Module.finrank K L) (x : relativeCohomology K L 2) :
    ∃ a : Kˣ, x = cyclicClass K L χ.toMonoidHom a := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Langlands.LocalClassField.normSubgroup K L)
    (cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
      (cyclicCoordinateGenerator_generates χ) x).toMul
  refine ⟨a, (cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)).injective ?_⟩
  have hsum : ∑ i ∈ Finset.range (Module.finrank K L),
      cyclicUnitCocycle K L χ.toMonoidHom a
        (cyclicCoordinateGenerator χ ^ i, cyclicCoordinateGenerator χ) = baseUnit K L a := by
    rw [cyclicUnitCocycle_sum]
    have h1 : (χ.toMonoidHom (cyclicCoordinateGenerator χ)).toAdd = 1 := by
      simp [cyclicCoordinateGenerator]
    rw [h1, carry_sum_one hn, pow_one]
  rw [cyclicClass, cyclicH2NormEquiv_H2π_of_sum K L _ _ _ a hsum]
  exact (congrArg Additive.ofMul ha).symm

/-! ### Restriction after inflation -/

section Square

variable (K E L M : Type u) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]

/-- The composite `Gal(M/E) → Gal(M/K) → Gal(L/K)` of a square of fields. -/
abbrev squareRestriction : Gal(M/E) →* Gal(L/K) :=
  (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)

omit [Normal K L] in
/-- Both routes from `K` to `M` include a base unit in the same way. -/
theorem unitInclusion_baseUnit (a : Kˣ) :
    unitInclusionLinear L M (baseUnit K L a) =
      baseUnit E M (Units.map (algebraMap K E).toMonoidHom a) := by
  apply Units.ext
  change algebraMap L M (algebraMap K L (a : K)) = algebraMap E M (algebraMap K E (a : K))
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

omit [Normal K L] in
/-- The same comparison for multiples of base units. -/
theorem unitInclusion_nsmul_baseUnit (k : ℕ) (a : Kˣ) :
    unitInclusionLinear L M (k • baseUnit K L a) =
      k • baseUnit E M (Units.map (algebraMap K E).toMonoidHom a) := by
  rw [← baseUnit_pow, unitInclusion_baseUnit K E L M, map_pow, baseUnit_pow]

/-- Restriction after inflation of a positive carry class is the carry class of the
composite character and the included base unit. -/
theorem restriction_inflation_cyclicClass {n : ℕ} [NeZero n]
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    relativeRestriction K E M 2 (relativeInflation K L M 2 (cyclicClass K L χ a)) =
      cyclicClass E M (χ.comp (squareRestriction K E L M))
        (Units.map (algebraMap K E).toMonoidHom a) := by
  simp only [cyclicClass, relativeInflation, relativeRestriction,
    groupCohomology.H2π_comp_map_apply]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro s t
  change unitInclusionLinear L M (cyclicCarry _ _ • baseUnit K L a) = cyclicCarry _ _ • _
  exact unitInclusion_nsmul_baseUnit K E L M _ a

end Square

/-! ### Rational arithmetic -/

/-- Integers vanish in `ℚ/ℤ`. -/
theorem rationalClass_intCast (z : ℤ) : rationalClass (z : ℚ) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨z, by simp⟩)

/-- The final rational identity: the two fractions differ by an integer. -/
theorem rationalClass_scaling {n m f q t S N : ℕ} (hn : 0 < n) (hm : 0 < m) {oE oF : ℤ}
    (hS : n * S = m * t) (hf : n * q + t = f) (hord : (f : ℤ) * oE = N * oF) :
    rationalClass ((((S : ℤ) * oE : ℤ) : ℚ) / m) = N • rationalClass ((oF : ℚ) / n) := by
  rw [← map_nsmul]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hS' : (n : ℚ) * S = m * t := by exact_mod_cast hS
  have hf' : (n : ℚ) * q + t = f := by exact_mod_cast hf
  have hord' : (f : ℚ) * oE = N * oF := by exact_mod_cast hord
  have key : (((S : ℤ) * oE : ℤ) : ℚ) / m =
      N • ((oF : ℚ) / n) + ((-(q : ℤ) * oE : ℤ) : ℚ) := by
    rw [nsmul_eq_mul]
    push_cast
    field_simp
    linear_combination (oE : ℚ) * hS' + (m : ℚ) * hord' + (m : ℚ) * oE * hf'
  rw [key, map_add, rationalClass_intCast, add_zero]

/-! ### Residue Frobenius and valuations -/

section Arithmetic

variable {p : ℕ} [Fact p.Prime]
variable (F E L M : PadicField.{u} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

/-- The relative residue degree, as the dimension of the actual residue extension. -/
abbrev residueDeg [Algebra F.Carrier E.Carrier] [FiniteDimensional F.Carrier E.Carrier] : ℕ :=
  Module.finrank (ResidueField (LocalGalois.baseIntegers F.Carrier))
    (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier))

variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]

local instance baseResidueFinite' :
    Finite (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
  letI := F.canonicalTopologicalData.finite_residueField
  Finite.of_equiv F.canonicalTopologicalData.ResidueField
    (ArithmeticCoordinate.baseResidueEquiv F).symm.toEquiv

local instance extensionResidueFinite' :
    Finite (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) :=
  letI := E.canonicalTopologicalData.finite_residueField
  Finite.of_equiv E.canonicalTopologicalData.ResidueField
    (ArithmeticCoordinate.extensionResidueEquiv F E).symm.toEquiv

/-- The base residue field cardinality is the canonical residue cardinality. -/
theorem baseResidue_card :
    Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) =
      F.canonicalTopologicalData.residueCardinality :=
  Nat.card_congr (ArithmeticCoordinate.baseResidueEquiv F).toEquiv

/-- The residue field of `E` has `q_F ^ f` elements. -/
theorem residue_card_pow :
    Nat.card (ResidueField (LocalGalois.baseIntegers E.Carrier)) =
      Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) ^ residueDeg F E := by
  rw [baseResidue_card E, ← Module.natCard_eq_pow_finrank]
  exact (Nat.card_congr (ArithmeticCoordinate.extensionResidueEquiv F E).toEquiv).symm

/-- The absolute residue degrees multiply. -/
theorem residueDegree_eq_mul :
    E.canonicalTopologicalData.residueDegree =
      F.canonicalTopologicalData.residueDegree * residueDeg F E := by
  have h := residue_card_pow F E
  rw [baseResidue_card, baseResidue_card,
    E.canonicalTopologicalData.residueCardinality_eq_pow,
    F.canonicalTopologicalData.residueCardinality_eq_pow, ← pow_mul] at h
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h

/-- Valuation comparison along `F → E`, with the residue degree in place of a
ramification index. -/
theorem residueDeg_mul_ord_algebraMap (a : F.Carrier) :
    (residueDeg F E : ℤ) * E.canonicalTopologicalData.ord (algebraMap F.Carrier E.Carrier a) =
      (Module.finrank F.Carrier E.Carrier : ℤ) * F.canonicalTopologicalData.ord a := by
  set TF := F.canonicalTopologicalData
  set TE := E.canonicalTopologicalData
  have hord := Langlands.LocalClassField.ramificationIndex_mul_ord_relative_algebraMap
    F E TF TE a
  have hdeg : TE.ramificationIndex * TE.residueDegree =
      Module.finrank F.Carrier E.Carrier * (TF.ramificationIndex * TF.residueDegree) := by
    rw [TE.ramificationIndex_mul_residueDegree, TF.ramificationIndex_mul_residueDegree,
      mul_comm, Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier]
  rw [residueDegree_eq_mul F E] at hdeg
  have hef : (TE.ramificationIndex : ℤ) * residueDeg F E =
      (Module.finrank F.Carrier E.Carrier : ℤ) * TF.ramificationIndex := by
    have hf : (TF.residueDegree : ℤ) ≠ 0 := by exact_mod_cast TF.residueDegree_pos.ne'
    apply mul_right_cancel₀ hf
    have h' : TE.ramificationIndex * residueDeg F E * TF.residueDegree =
        Module.finrank F.Carrier E.Carrier * TF.ramificationIndex * TF.residueDegree := by
      calc TE.ramificationIndex * residueDeg F E * TF.residueDegree
          = TE.ramificationIndex * (TF.residueDegree * residueDeg F E) := by ring
        _ = Module.finrank F.Carrier E.Carrier * (TF.ramificationIndex * TF.residueDegree) :=
          hdeg
        _ = _ := by ring
    exact_mod_cast h'
  have he : (TF.ramificationIndex : ℤ) ≠ 0 := by exact_mod_cast TF.ramificationIndex_pos.ne'
  apply mul_left_cancel₀ he
  linear_combination (residueDeg F E : ℤ) * hord + TF.ord a * hef

variable [Algebra F.Carrier L.Carrier] [Algebra F.Carrier M.Carrier]
  [Algebra E.Carrier M.Carrier] [Algebra L.Carrier M.Carrier]
  [IsScalarTower (Padic p) F.Carrier L.Carrier]
  [IsScalarTower (Padic p) E.Carrier M.Carrier]
  [IsScalarTower F.Carrier E.Carrier M.Carrier]
  [IsScalarTower F.Carrier L.Carrier M.Carrier]
  [FiniteDimensional F.Carrier L.Carrier] [FiniteDimensional E.Carrier M.Carrier]

include F E in
omit [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier L.Carrier]
  [FiniteDimensional E.Carrier M.Carrier] in
/-- The square forces the p-adic structures of `L` and `M` to be compatible. -/
theorem padic_tower : IsScalarTower (Padic p) L.Carrier M.Carrier :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Padic p) F.Carrier L.Carrier x,
      ← IsScalarTower.algebraMap_apply F.Carrier L.Carrier M.Carrier,
      IsScalarTower.algebraMap_apply F.Carrier E.Carrier M.Carrier,
      ← IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier,
      ← IsScalarTower.algebraMap_apply (Padic p) E.Carrier M.Carrier]

omit [FiniteDimensional F.Carrier E.Carrier] in
/-- The relative spectral norms agree along `L → M`. -/
theorem spectralNorm_algebraMap (z : L.Carrier) :
    spectralNorm E.Carrier M.Carrier (algebraMap L.Carrier M.Carrier z) =
      spectralNorm F.Carrier L.Carrier z := by
  have := padic_tower F E L M
  rw [ArithmeticCoordinate.spectralNorm_eq_canonicalNorm E M,
    ArithmeticCoordinate.spectralNorm_eq_canonicalNorm F L]
  exact Langlands.Weil.Local.canonicalNorm_map L M
    (IsScalarTower.toAlgHom (Padic p) L.Carrier M.Carrier) z

/-- A residue-field identity is a spectral-norm inequality. -/
theorem residue_eq_iff {K : PadicField.{u} p} {X : Type u} [Field X] [Algebra K.Carrier X]
    [FiniteDimensional K.Carrier X] (y z : LocalGalois.extensionIntegers K.Carrier X) :
    residue _ y = residue _ z ↔ spectralNorm K.Carrier X ((y : X) - z) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  rfl

variable [IsGalois F.Carrier L.Carrier]

omit [FiniteDimensional F.Carrier E.Carrier] in
/-- Restricting an `E`-automorphism of `M` that acts as the `q`-th power on
the residue field of `M` gives an automorphism of `L` with the same action. -/
theorem residueHom_restriction (q : ℕ) (g : Gal(M.Carrier/E.Carrier))
    (hg : ∀ y, LocalGalois.residueHom E.Carrier M.Carrier g y = y ^ q)
    (x : ResidueField (LocalGalois.extensionIntegers F.Carrier L.Carrier)) :
    LocalGalois.residueHom F.Carrier L.Carrier
      (AlgEquiv.restrictNormalHom L.Carrier (AlgEquiv.restrictScalarsHom F.Carrier g)) x =
        x ^ q := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  set h := AlgEquiv.restrictNormalHom L.Carrier (AlgEquiv.restrictScalarsHom F.Carrier g)
  have hcomm : algebraMap L.Carrier M.Carrier (h x) = g (algebraMap L.Carrier M.Carrier x) :=
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalarsHom F.Carrier g) L.Carrier x
  have hy : spectralNorm E.Carrier M.Carrier (algebraMap L.Carrier M.Carrier x) ≤ 1 := by
    rw [spectralNorm_algebraMap F E L M]
    exact x.property
  let y : LocalGalois.extensionIntegers E.Carrier M.Carrier := ⟨_, hy⟩
  have h1 : residue _ (LocalGalois.integerAut E.Carrier M.Carrier g y) =
      residue _ (y ^ q) := by
    rw [map_pow]
    exact hg (residue _ y)
  rw [residue_eq_iff] at h1
  change residue _ (LocalGalois.integerAut F.Carrier L.Carrier h x) = residue _ x ^ q
  rw [← map_pow, residue_eq_iff, ← spectralNorm_algebraMap F E L M]
  change spectralNorm E.Carrier M.Carrier (g (algebraMap L.Carrier M.Carrier x) -
    (algebraMap L.Carrier M.Carrier x) ^ q) < 1 at h1
  change spectralNorm E.Carrier M.Carrier (algebraMap L.Carrier M.Carrier
    (h (x : L.Carrier) - (x : L.Carrier) ^ q)) < 1
  rw [map_sub, map_pow, hcomm]
  exact h1

/-- Powers of an automorphism acting by `q`-th powers act by iterated powers. -/
theorem residueHom_pow_apply {K : PadicField.{u} p} {X : Type u} [Field X]
    [Algebra K.Carrier X] [FiniteDimensional K.Carrier X] (q : ℕ) (σ : Gal(X/K.Carrier))
    (hσ : ∀ y, LocalGalois.residueHom K.Carrier X σ y = y ^ q) (j : ℕ)
    (y : ResidueField (LocalGalois.extensionIntegers K.Carrier X)) :
    LocalGalois.residueHom K.Carrier X (σ ^ j) y = y ^ q ^ j := by
  induction j generalizing y with
  | zero => simp
  | succ j ih => rw [pow_succ, map_mul, AlgEquiv.mul_apply, hσ, ih, ← pow_mul, ← pow_succ']

/-- The arithmetic generator over `E`, restricted to `L`, is the `f`-th power of the
arithmetic generator over `F`. -/
theorem coordinate_restriction
    [NeZero (Module.finrank F.Carrier L.Carrier)] [NeZero (Module.finrank E.Carrier M.Carrier)]
    (χL : Gal(L.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier L.Carrier)))
    (χM : Gal(M.Carrier/E.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank E.Carrier M.Carrier)))
    (hL : IsArithmeticUnramifiedCoordinate F L.Carrier χL)
    (hM : IsArithmeticUnramifiedCoordinate E M.Carrier χM) :
    χL (squareRestriction F.Carrier E.Carrier L.Carrier M.Carrier
        (cyclicCoordinateGenerator χM)) =
      Multiplicative.ofAdd (residueDeg F E : ZMod (Module.finrank F.Carrier L.Carrier)) := by
  obtain ⟨hinj, hσ⟩ := hL
  obtain ⟨-, hg⟩ := hM
  have h : squareRestriction F.Carrier E.Carrier L.Carrier M.Carrier
      (cyclicCoordinateGenerator χM) = cyclicCoordinateGenerator χL ^ residueDeg F E := by
    apply hinj
    ext y
    refine (residueHom_restriction F E L M _ (cyclicCoordinateGenerator χM) hg y).trans ?_
    rw [residueHom_pow_apply _ (cyclicCoordinateGenerator χL) hσ, residue_card_pow F E]
  rw [h, map_pow, cyclicCoordinateGenerator, χL.apply_symm_apply, ← ofAdd_nsmul, nsmul_one]

end Arithmetic

/-! ### The invariant of a cocycle with a base-unit generator sum -/

section Invariant

variable {p : ℕ} [Fact p.Prime]

/-- The canonical order of a natural power. -/
theorem ord_pow {K : PadicField.{u} p} (x : K.Carrier) (k : ℕ) :
    K.canonicalTopologicalData.ord (x ^ k) = k * K.canonicalTopologicalData.ord x := by
  simpa using K.canonicalTopologicalData.ord_zpow x k

/-- A cocycle whose generator sum is the base unit `b` has invariant `ord b / d`. -/
theorem invariant_H2π_of_sum (K X : PadicField.{u} p) [Algebra K.Carrier X.Carrier]
    [IsScalarTower (Padic p) K.Carrier X.Carrier] [FiniteDimensional K.Carrier X.Carrier]
    [IsGalois K.Carrier X.Carrier]
    (hram : K.canonicalTopologicalData.ramificationIndex =
      X.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(X.Carrier/K.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank K.Carrier X.Carrier)))
    (c : groupCohomology.cocycles₂ (unitsRepresentation K.Carrier X.Carrier))
    (b : K.Carrierˣ)
    (hc : ∑ i ∈ Finset.range (Module.finrank K.Carrier X.Carrier),
      c (cyclicCoordinateGenerator χ ^ i, cyclicCoordinateGenerator χ) =
        baseUnit K.Carrier X.Carrier b) :
    unramifiedH2Invariant K X hram χ (groupCohomology.H2π _ c) =
      rationalClass ((K.canonicalTopologicalData.ord (b : K.Carrier) : ℚ) /
        Module.finrank K.Carrier X.Carrier) := by
  rw [← (cyclicH2NormEquiv K.Carrier X.Carrier (cyclicCoordinateGenerator χ)
      (cyclicCoordinateGenerator_generates χ)).symm_apply_apply (groupCohomology.H2π _ c),
    cyclicH2NormEquiv_H2π_of_sum K.Carrier X.Carrier _ _ c b hc]
  exact unramifiedH2Invariant_normRepresentative K X hram χ b

end Invariant

/-! ### Assembly -/

section Assembly

variable {p : ℕ} [Fact p.Prime] (F E L M : PadicField.{u} p)
  [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier] [Algebra F.Carrier M.Carrier]
  [Algebra E.Carrier M.Carrier] [Algebra L.Carrier M.Carrier]
  [IsScalarTower (Padic p) F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
  [IsScalarTower (Padic p) E.Carrier M.Carrier]
  [IsScalarTower F.Carrier E.Carrier M.Carrier] [IsScalarTower F.Carrier L.Carrier M.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier L.Carrier]
  [FiniteDimensional E.Carrier M.Carrier]
  [IsGalois F.Carrier L.Carrier] [IsGalois E.Carrier M.Carrier]
  [NeZero (Module.finrank F.Carrier L.Carrier)] [NeZero (Module.finrank E.Carrier M.Carrier)]

/-- The base-change formula for fixed instances. -/
theorem invariant_restriction_inflation
    (hFL : F.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex)
    (hEM : E.canonicalTopologicalData.ramificationIndex =
      M.canonicalTopologicalData.ramificationIndex)
    (χL : Gal(L.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier L.Carrier)))
    (χM : Gal(M.Carrier/E.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank E.Carrier M.Carrier)))
    (hL : IsArithmeticUnramifiedCoordinate F L.Carrier χL)
    (hM : IsArithmeticUnramifiedCoordinate E M.Carrier χM)
    (x : relativeCohomology F.Carrier L.Carrier 2) :
    unramifiedH2Invariant E M hEM χM
        (relativeRestriction F.Carrier E.Carrier M.Carrier 2
          (relativeInflation F.Carrier L.Carrier M.Carrier 2 x)) =
      Module.finrank F.Carrier E.Carrier • unramifiedH2Invariant F L hFL χL x := by
  by_cases hn1 : Module.finrank F.Carrier L.Carrier = 1
  · have h0 : x = 0 := unramifiedH2Invariant_injective F L hFL χL (by
      rw [map_zero]; exact unramifiedH2Invariant_degree_one F L hFL χL hn1 x)
    subst h0
    simp only [map_zero, smul_zero]
  have hn : 1 < Module.finrank F.Carrier L.Carrier := by
    have := NeZero.pos (Module.finrank F.Carrier L.Carrier); omega
  obtain ⟨a, rfl⟩ := exists_cyclicClass_eq F.Carrier L.Carrier χL hn x
  -- the `F` side
  have hsumF : ∑ i ∈ Finset.range (Module.finrank F.Carrier L.Carrier),
      cyclicUnitCocycle F.Carrier L.Carrier χL.toMonoidHom a
        (cyclicCoordinateGenerator χL ^ i, cyclicCoordinateGenerator χL) =
        baseUnit F.Carrier L.Carrier a := by
    rw [cyclicUnitCocycle_sum]
    have h1 : (χL.toMonoidHom (cyclicCoordinateGenerator χL)).toAdd = 1 := by
      simp [cyclicCoordinateGenerator]
    rw [h1, carry_sum_one hn, pow_one]
  -- the `E` side
  let χ' := χL.toMonoidHom.comp (squareRestriction F.Carrier E.Carrier L.Carrier M.Carrier)
  have ht : (χ' (cyclicCoordinateGenerator χM)).toAdd =
      (residueDeg F E : ZMod (Module.finrank F.Carrier L.Carrier)) := by
    change (χL (squareRestriction F.Carrier E.Carrier L.Carrier M.Carrier
      (cyclicCoordinateGenerator χM))).toAdd = _
    rw [coordinate_restriction F E L M χL χM hL hM]
    rfl
  have hmt : Module.finrank E.Carrier M.Carrier • (χ' (cyclicCoordinateGenerator χM)).toAdd =
      0 := by
    have h := congrArg (fun y => (χ' y).toAdd) (coordinateGenerator_pow_card χM)
    simpa only [map_pow, toAdd_pow, map_one, toAdd_one] using h
  have hS := carry_sum_telescope (χ' (cyclicCoordinateGenerator χM)).toAdd
    (Module.finrank E.Carrier M.Carrier)
  rw [hmt, ZMod.val_zero, add_zero] at hS
  have hsumE := cyclicUnitCocycle_sum E.Carrier M.Carrier χ'
    (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a)
    (cyclicCoordinateGenerator χM) (Module.finrank E.Carrier M.Carrier)
  rw [restriction_inflation_cyclicClass, cyclicClass, cyclicClass,
    invariant_H2π_of_sum E M hEM χM _ _ hsumE, invariant_H2π_of_sum F L hFL χL _ a hsumF,
    Units.val_pow_eq_pow_val, ord_pow]
  have hf : Module.finrank F.Carrier L.Carrier *
      (residueDeg F E / Module.finrank F.Carrier L.Carrier) +
      (χ' (cyclicCoordinateGenerator χM)).toAdd.val = residueDeg F E := by
    rw [ht, ZMod.val_natCast]
    exact Nat.div_add_mod _ _
  exact rationalClass_scaling (NeZero.pos _) (NeZero.pos _) hS hf
    (residueDeg_mul_ord_algebraMap F E (a : F.Carrier))

end Assembly

end UnramifiedBaseChange

open UnramifiedBaseChange in
/-- Finite base change multiplies the unramified `H²` invariant by `[E : F]`. -/
theorem unramifiedInvariantBaseChangeCompatibility :
    UnramifiedInvariantBaseChangeCompatibility.{u} := by
  intro p _ F E L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hFL hEM χL χM hL hM x
  have : NeZero (Module.finrank F.Carrier L.Carrier) := ⟨Module.finrank_pos.ne'⟩
  have : NeZero (Module.finrank E.Carrier M.Carrier) := ⟨Module.finrank_pos.ne'⟩
  exact invariant_restriction_inflation F E L M hFL hEM χL χM hL hM x

end Langlands.ClassFieldTheory.Local

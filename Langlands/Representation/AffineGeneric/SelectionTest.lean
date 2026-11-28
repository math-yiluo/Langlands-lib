import Langlands.Representation.AffineGeneric.Supercuspidality
import Langlands.Representation.AffineGeneric.Kloosterman
import Langlands.Representation.AffineGeneric.Elliptic
import Langlands.BaseChange.OrbitalIntegralPositivity
import Langlands.Group.GL.LocalFieldTopology

/-!
# A supercuspidal selection test for `GL_{m+1}` over a local field

Let `F` be a nonarchimedean local field of characteristic zero with residue field `k`,
uniformizer `ϖ`, a nontrivial additive character `ψ` of `k` and `A ∈ kˣ` with
`Kl_{m+1}(ψ, A) ≠ 0`. The test function
`φ = Kl_{m+1}(ψ, A)⁻¹ · Σ_{r ∈ k^{m+1}, r₁ ⋯ r_{m+1} = 1} f_{ψ,r}`
is a normalized sum of the test functions `f_{ψ,r} = 1_{I⁺} · ψ(λ_r)` of `TestFunction`. All
`r_i` in the sum are nonzero, so for `m ≥ 1` each `ψ ∘ λ_r` is an affine generic character of
`I⁺`. For `m = 0` the only term is `r = (1)`, with `λ_r(g) = res(ϖ⁻¹ (g - 1))` on `I⁺ = 1 + 𝔭`.
The function `φ` has vanishing constant terms, every irreducible admissible representation
whose distribution character does not vanish at `φ` is supercuspidal, and its orbital
integrals do not vanish on the nonempty open set `U = {γ ∈ I⁺ | D(γ) = A}`.

If `γ ∈ U` and `x⁻¹ γ x ∈ I⁺`, then `D(x⁻¹ γ x) = A`, so all
coordinates of `x⁻¹ γ x` are nonzero and averaging over `r₁ ⋯ r_{m+1} = 1` gives
`φ(x⁻¹ γ x) = 1`. Hence `φ(x⁻¹ γ x) = 1_{I⁺}(x⁻¹ γ x)` for all `x`, and the orbital integral of
`φ` at `γ` is that of the indicator function of `I⁺`, which is positive since `γ` is regular
semisimple.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear HarmonicAnalysis JacquetLanglands
  Langlands.QuotientIntegration Langlands.BaseChange Langlands.TraceFormula

universe u uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {m : ℕ}

/-! ### Elements of `I⁺` with prescribed coordinates -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a uniformizer `ϖ`, every tuple of residues is the tuple of cyclic coordinates of
an element of `I⁺`. -/
theorem exists_mem_groupCoord_eq {ϖ : Fˣ}
    (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ) (a : Fin (m + 1) → Residue F) :
    ∃ γ ∈ iwahoriRadical m, ∀ i, groupCoord ϖ γ i = a i := by
  choose c hc hca using fun i => exists_resOf_eq (F := F) (a i)
  let Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    Matrix.of fun i j => if j = finRotate (m + 1) i then (weight ϖ i)⁻¹ * c i else 0
  have hY : IsIwahoriRadical Y := by
    intro i j
    by_cases h : j = finRotate (m + 1) i
    · subst h
      simp only [Y, Matrix.of_apply, eq_self, ↓reduceIte]
      unfold weight
      split_ifs with hs
      · rw [inv_inv]
        have hlt : valuation F ((ϖ : F) * c i) < 1 := val_mul_lt_one_left hϖ.1 (hc i)
        exact ⟨hlt.le, fun _ => hlt⟩
      · rw [inv_one, one_mul]
        exact ⟨hc i, fun hle => absurd hle (not_le.mpr (lt_finRotate_of_ne_last hs))⟩
    · simp only [Y, Matrix.of_apply, h, ↓reduceIte, map_zero]
      exact ⟨zero_le, fun _ => zero_lt_one⟩
  obtain ⟨γ, hγ, hγY⟩ := exists_mem_iwahoriRadical_coe_eq hY
  refine ⟨γ, hγ, fun i => ?_⟩
  unfold groupCoord coord
  rw [hγY, add_sub_cancel_left]
  simp only [Y, Matrix.of_apply, eq_self, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (weight_ne_zero ϖ i), one_mul, hca i]

/-- The invariant `D` is locally constant on `GL_{m+1}(F)`. -/
theorem isLocallyConstant_coordProd (ϖ : Fˣ) :
    IsLocallyConstant (coordProd (m := m) (F := F) ϖ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  filter_upwards [Filter.eventually_all.2 fun i => groupCoord_eventuallyEq ϖ g i] with h hh
  unfold coordProd
  simp only [hh]

/-! ### The averaged test function -/

section Test

variable (ϖ : Fˣ) (ψ : AddChar (Residue F) ℂ) [Fintype (Residue F)] [DecidableEq (Residue F)]
  (A : Residue F)

variable (m) in
/-- The tuples `r ∈ k^{m+1}` with `r₁ ⋯ r_{m+1} = 1`. -/
def normOneTuples : Finset (Fin (m + 1) → Residue F) :=
  Finset.univ.filter fun r => ∏ i, r i = 1

/-- The averaged test function `Kl_{m+1}(ψ, A)⁻¹ · Σ_{r₁ ⋯ r_{m+1} = 1} f_{ψ,r}`, where
`f_{ψ,r} = 1_{I⁺} · ψ(λ_r)`. -/
def selectionTest : SchwartzBruhat (GeneralLinear (m + 1) F) :=
  (kloosterman ψ (m + 1) A)⁻¹ • ∑ r ∈ normOneTuples m, affineGenericTest ϖ ψ r

theorem selectionTest_apply (g : GeneralLinear (m + 1) F) :
    selectionTest ϖ ψ A g =
      (kloosterman ψ (m + 1) A)⁻¹ * ∑ r ∈ normOneTuples m, testFunction ϖ ψ r g := by
  simp only [selectionTest, Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem ne_zero_of_mem_normOneTuples {r : Fin (m + 1) → Residue F} (hr : r ∈ normOneTuples m)
    (i : Fin (m + 1)) : r i ≠ 0 := by
  have h1 : ∏ j, r j = 1 := (Finset.mem_filter.mp hr).2
  intro h0
  have : ∏ j, r j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
  rw [h1] at this
  exact one_ne_zero this

theorem selectionTest_apply_of_not_mem {g : GeneralLinear (m + 1) F}
    (hg : g ∉ iwahoriRadical m) : selectionTest ϖ ψ A g = 0 := by
  rw [selectionTest_apply]
  simp only [testFunction_of_not_mem ϖ ψ _ hg, Finset.sum_const_zero, mul_zero]

theorem selectionTest_apply_of_mem
    (hKl : kloosterman ψ (m + 1) A ≠ 0) (hA : A ≠ 0) {g : GeneralLinear (m + 1) F}
    (hg : g ∈ iwahoriRadical m) (hgA : coordProd ϖ g = A) : selectionTest ϖ ψ A g = 1 := by
  rw [selectionTest_apply]
  have hc : ∀ i, groupCoord ϖ g i ≠ 0 := by
    intro i h0
    apply hA
    rw [← hgA]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hsum : ∑ r ∈ normOneTuples m, testFunction ϖ ψ r g = kloosterman ψ (m + 1) A := by
    rw [← hgA]
    unfold coordProd
    rw [← sum_prod_eq_one ψ hc]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [testFunction_of_mem ϖ ψ r hg]
    rfl
  rw [hsum, inv_mul_cancel₀ hKl]

end Test

/-! ### The indicator function of `I⁺` -/

/-- For the trivial character and `r = 0` the test function `1_{I⁺} · ψ(λ_r)` is the
indicator function of `I⁺`. -/
theorem affineGenericTest_one_of_mem (ϖ : Fˣ) {g : GeneralLinear (m + 1) F}
    (hg : g ∈ iwahoriRadical m) :
    affineGenericTest ϖ (1 : AddChar (Residue F) ℂ) 0 g = 1 := by
  rw [affineGenericTest_apply, testFunction_of_mem ϖ _ _ hg, AddChar.one_apply]

theorem affineGenericTest_one_of_not_mem (ϖ : Fˣ) {g : GeneralLinear (m + 1) F}
    (hg : g ∉ iwahoriRadical m) :
    affineGenericTest ϖ (1 : AddChar (Residue F) ℂ) 0 g = 0 := by
  rw [affineGenericTest_apply, testFunction_of_not_mem ϖ _ _ hg]

/-! ### The three properties of the averaged test function -/

section Properties

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
  {ψ : AddChar (Residue F) ℂ} [Fintype (Residue F)] [DecidableEq (Residue F)] {A : Residue F}

include hϖ

/-- **Cuspidality.** For a uniformizer `ϖ` and nontrivial `ψ`, the averaged test function
has vanishing constant terms. -/
theorem hasVanishingConstantTerms_selectionTest (hψ : ψ ≠ 1) :
    HasVanishingConstantTerms ⇑(selectionTest (m := m) ϖ ψ A) := by
  have he : ⇑(selectionTest (m := m) ϖ ψ A) = fun g => (kloosterman ψ (m + 1) A)⁻¹ *
      ∑ r ∈ normOneTuples m, testFunction ϖ ψ r g :=
    funext (selectionTest_apply ϖ ψ A)
  rw [he]
  exact (hasVanishingConstantTerms_sum _ _ fun r hr =>
    hasVanishingConstantTerms_testFunction ψ r hϖ hψ
      (ne_zero_of_mem_normOneTuples hr)).const_mul _

/-- **Selection.** For a uniformizer `ϖ` and nontrivial `ψ`, an irreducible admissible
representation whose distribution character does not vanish at the averaged test function is
supercuspidal. -/
theorem isSupercuspidal_of_distribution_selectionTest_ne_zero
    [MeasurableSpace (GeneralLinear (m + 1) F)] [BorelSpace (GeneralLinear (m + 1) F)]
    [T2Space (GeneralLinear (m + 1) F)] [LocallyCompactSpace (GeneralLinear (m + 1) F)]
    [TotallyDisconnectedSpace (GeneralLinear (m + 1) F)] (hψ : ψ ≠ 1)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (m + 1) F) W) (hπ : IsAdmissible π)
    (hirr : π.IsIrreducible) (μ : Measure (GeneralLinear (m + 1) F)) [μ.IsHaarMeasure]
    (hdist : Character.distribution μ π hπ (selectionTest ϖ ψ A) ≠ 0) :
    GeneralLinear.IsSupercuspidal π := by
  unfold selectionTest at hdist
  rw [map_smul, map_sum] at hdist
  obtain ⟨r, hr, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_smul hdist)
  exact isSupercuspidal_of_distribution_ne_zero hϖ ψ r hψ (ne_zero_of_mem_normOneTuples hr)
    π hπ hirr μ hne

omit hϖ [Fintype (Residue F)] [DecidableEq (Residue F)] in
/-- The set `{γ ∈ I⁺ | D(γ) = A}` is open. -/
theorem isOpen_selectionSet (ϖ : Fˣ) (A : Residue F) :
    IsOpen {γ : GeneralLinear (m + 1) F | γ ∈ iwahoriRadical m ∧ coordProd ϖ γ = A} :=
  isOpen_iwahoriRadical.inter ((isLocallyConstant_coordProd ϖ).isOpen_fiber A)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype (Residue F)]
  [DecidableEq (Residue F)] in
/-- For a uniformizer `ϖ`, the set `{γ ∈ I⁺ | D(γ) = A}` is nonempty. -/
theorem selectionSet_nonempty (A : Residue F) :
    {γ : GeneralLinear (m + 1) F | γ ∈ iwahoriRadical m ∧ coordProd ϖ γ = A}.Nonempty := by
  classical
  obtain ⟨γ, hγ, hc⟩ := exists_mem_groupCoord_eq hϖ fun i : Fin (m + 1) => if i = 0 then A else 1
  refine ⟨γ, hγ, ?_⟩
  simp only [coordProd, hc, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]

attribute [local instance high] leftQuotientMeasurableSpace in
open scoped ComplexOrder in
/-- **Orbital nonvanishing.** For a uniformizer `ϖ`, a characteristic-zero local field `F`,
`Kl_{m+1}(ψ, A) ≠ 0` and `A ≠ 0`, the orbital integral of the averaged test function at every
`γ ∈ I⁺` with `D(γ) = A` is nonzero for every Haar measure on `GL_{m+1}(F)`, right Haar
measure on the centralizer of `γ` and compatible quotient measure. -/
theorem orbitalIntegral_selectionTest_ne_zero [CharZero F]
    [MeasurableSpace (GeneralLinear (m + 1) F)] [BorelSpace (GeneralLinear (m + 1) F)]
    (hKl : kloosterman ψ (m + 1) A ≠ 0) (hA : A ≠ 0)
    {γ : GeneralLinear (m + 1) F} (hγ : γ ∈ iwahoriRadical m) (hγA : coordProd ϖ γ = A)
    (μ : Measure (GeneralLinear (m + 1) F)) [μ.IsHaarMeasure]
    (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    (νγ : Measure (LeftQuotient (glCentralizer γ)))
    (hcompat : IsCompatible (glCentralizer γ) μ μγ νγ) :
    orbitalIntegral γ νγ ⇑(selectionTest ϖ ψ A) ≠ 0 := by
  obtain rfl : ‹MeasurableSpace (GeneralLinear (m + 1) F)› = borel _ := BorelSpace.measurable_eq
  have hD : coordProd ϖ γ ≠ 0 := hγA ▸ hA
  have hrs := isRegularSemisimple_of_coordProd_ne_zero hϖ hγ hD
  let f₀ := affineGenericTest (m := m) ϖ (1 : AddChar (Residue F) ℂ) 0
  have hkey (x : GeneralLinear (m + 1) F) :
      selectionTest ϖ ψ A (x⁻¹ * γ * x) = f₀ (x⁻¹ * γ * x) := by
    by_cases hx : x⁻¹ * γ * x ∈ iwahoriRadical m
    · rw [selectionTest_apply_of_mem ϖ ψ A hKl hA hx ((coordProd_conj hϖ hγ hx).trans hγA),
        affineGenericTest_one_of_mem ϖ hx]
    · rw [selectionTest_apply_of_not_mem ϖ ψ A hx, affineGenericTest_one_of_not_mem ϖ hx]
  have heq : orbitalIntegral γ νγ ⇑(selectionTest ϖ ψ A) = orbitalIntegral γ νγ ⇑f₀ := by
    simp only [orbitalIntegral, twistedOrbitalIntegral]
    congr 1
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      simp only [twistedOrbitFunction_mk, MonoidHom.id_apply]
      exact hkey x
  have hnonneg (g : GeneralLinear (m + 1) F) : 0 ≤ f₀ g := by
    by_cases hg : g ∈ iwahoriRadical m
    · rw [affineGenericTest_one_of_mem ϖ hg]
      exact zero_le_one
    · rw [affineGenericTest_one_of_not_mem ϖ hg]
  have hpos : 0 < f₀ γ := by
    rw [affineGenericTest_one_of_mem ϖ hγ]
    exact zero_lt_one
  rw [heq]
  exact (orbitalIntegralPositivity F (m + 1) μ inferInstance f₀ γ hrs hnonneg hpos μγ νγ
    hcompat).ne'

end Properties

/-! ### The selection test -/

attribute [local instance high] leftQuotientMeasurableSpace in
/-- **Supercuspidal selection test for `GL_{m+1}`.** Let `F` be a nonarchimedean local field of
characteristic zero and give `GL_{m+1}(F)` its Borel σ-algebra. There is
`φ ∈ C^∞_c(GL_{m+1}(F))` such that:

1. `φ` has vanishing constant terms;
2. every irreducible admissible representation whose distribution character does not vanish
   at `φ`, for some Haar measure, is supercuspidal;
3. there is a nonempty open set `U ⊆ GL_{m+1}(F)` such that at every `γ ∈ U` the orbital
   integral of `φ` is nonzero, for every Haar measure on `GL_{m+1}(F)`, every right Haar
   measure on the centralizer of `γ` and every compatible quotient measure. -/
theorem exists_supercuspidalSelectionTest (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] (m : ℕ) :
    letI : MeasurableSpace (GeneralLinear (m + 1) F) := borel _
    haveI : BorelSpace (GeneralLinear (m + 1) F) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space F (m + 1)
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (m + 1)
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (m + 1)
    ∃ φ : SchwartzBruhat (GeneralLinear (m + 1) F),
      HasVanishingConstantTerms (⇑φ) ∧
      (∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (m + 1) F) W)
        (hπ : IsAdmissible π), π.IsIrreducible →
        ∀ (μ : Measure (GeneralLinear (m + 1) F)) [μ.IsHaarMeasure],
          Character.distribution μ π hπ φ ≠ 0 → GeneralLinear.IsSupercuspidal π) ∧
      ∃ U : Set (GeneralLinear (m + 1) F), IsOpen U ∧ U.Nonempty ∧
        ∀ γ ∈ U, ∀ (μ : Measure (GeneralLinear (m + 1) F))
          [μ.IsHaarMeasure] (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure]
          [μγ.IsMulRightInvariant] (νγ : Measure (LeftQuotient (glCentralizer γ))),
          IsCompatible (glCentralizer γ) μ μγ νγ → orbitalIntegral γ νγ ⇑φ ≠ 0 := by
  let : MeasurableSpace (GeneralLinear (m + 1) F) := borel _
  have : BorelSpace (GeneralLinear (m + 1) F) := ⟨rfl⟩
  have := LocalFieldTopology.generalLinear_t2Space F (m + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F (m + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (m + 1)
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F
  let := Fintype.ofFinite (Residue F)
  classical
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one (k := Residue F)
  obtain ⟨A, hA, hKl⟩ := exists_kloosterman_ne_zero ψ hψ (m + 1)
  refine ⟨selectionTest ϖ ψ A, hasVanishingConstantTerms_selectionTest hϖ hψ,
    fun W _ _ π hπ hirr μ _ hdist =>
      isSupercuspidal_of_distribution_selectionTest_ne_zero hϖ hψ π hπ hirr μ hdist,
    _, isOpen_selectionSet ϖ A, selectionSet_nonempty hϖ A, ?_⟩
  rintro γ ⟨hγ, hγA⟩ μ _ μγ _ _ νγ hcompat
  exact orbitalIntegral_selectionTest_ne_zero hϖ hKl hA hγ hγA μ μγ νγ hcompat

end Langlands.AffineGeneric

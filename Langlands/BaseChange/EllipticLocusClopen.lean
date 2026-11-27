import Langlands.BaseChange.RegularOrbitParameters
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The elliptic loci are open in the regular loci

For a nonarchimedean local field `F` of characteristic zero, this module shows that in the
coefficient space `Fin n → F` of monic polynomials of degree `n` both the separable irreducible
polynomials and the separable reducible polynomials form open sets. The proof is Krasner's
lemma (Mathlib's `IsKrasner`, for the algebraic closure of `F` with its spectral norm)
combined with the continuity of roots in the coefficients
(`exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`).

Pulling back along the characteristic coefficients `coefficients` on `GL_n(F)` and the norm
coefficients `normCoefficients` on `GL_n(E)` (`Langlands.BaseChange.RegularOrbitParameters`)
gives: the regular semisimple non-elliptic elements of `GL_n(F)` form an open set, and the
σ-elliptic and the σ-regular non-σ-elliptic elements of `GL_n(E)` form open sets. The module
also characterizes ellipticity and σ-ellipticity through these coefficients and shows their
invariance under conjugation and σ-conjugation. These are the topological and
conjugation-invariance facts used to cut test functions off to the elliptic sets (Henniart–
Lemaire 2011, I.2.5 and II.1.2). See the paired Markdown.
-/

noncomputable section

open Polynomial IntermediateField

namespace Langlands.BaseChange

section Krasner

variable {K : Type*} {L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L]

/-- Distinct roots in `L` of a polynomial are at distance at least `3 * r` for some `r > 0`. -/
theorem exists_pos_three_mul_le_norm_sub_rootSet (f : K[X]) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ f.rootSet L, ∀ a' ∈ f.rootSet L, a ≠ a' → 3 * r ≤ ‖a - a'‖ := by
  classical
  let S : Finset L := (f.aroots L).toFinset
  let D : Finset ℝ := insert 3
    (((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => ‖p.1 - p.2‖)
  have hD : D.Nonempty := Finset.insert_nonempty _ _
  refine ⟨D.min' hD / 3, ?_, ?_⟩
  · apply div_pos _ (by norm_num)
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · norm_num
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
  · intro a ha a' ha' hne
    rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
    apply Finset.min'_le
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨(a, a'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha'⟩, hne⟩, rfl⟩

/-- The roots of a polynomial in `L` are bounded. -/
theorem exists_max_norm_one_le_rootSet (f : K[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ a ∈ f.rootSet L, max ‖a‖ 1 ≤ B := by
  classical
  let S : Finset L := (f.aroots L).toFinset
  let D : Finset ℝ := insert 1 (S.image fun a => max ‖a‖ 1)
  have hD : D.Nonempty := Finset.insert_nonempty _ _
  refine ⟨D.max' hD, zero_lt_one.trans_le (D.le_max' _ (Finset.mem_insert_self _ _)), ?_⟩
  intro a ha
  exact D.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha))

/-- Continuity of roots: for a monic `f` and `r > 0`, every monic `g` of the same degree whose
coefficients are close enough to those of `f` has a root within `r` of each root of `f` in
the algebraically closed field `L`. -/
theorem exists_coeff_nhds_forall_root_near [IsAlgClosed L] (f : K[X]) (hf : f.Monic) {r : ℝ}
    (hr : 0 < r) :
    ∃ ε > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) →
      ∀ a ∈ f.rootSet L, ∃ b ∈ g.rootSet L, ‖a - b‖ < r := by
  obtain ⟨B, hB, hBa⟩ := exists_max_norm_one_le_rootSet (L := L) f
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · refine ⟨1, one_pos, fun g _ _ _ a ha => ?_⟩
    rw [hf.natDegree_eq_zero.mp h0, rootSet_one] at ha
    exact absurd ha (Set.notMem_empty a)
  let ε := (r / B) ^ f.natDegree / (f.natDegree + 1)
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, fun g hg hdeg hcoeff a ha => ?_⟩
  have hgs : (g.map (algebraMap K L)).Splits := IsAlgClosed.splits _
  obtain ⟨b, hb, hdist⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε
    (hf.mem_rootSet.mp ha) hf hg hdeg hcoeff hgs
  refine ⟨b, hg.mem_rootSet.mpr (mem_aroots.mp hb).2, hdist.trans_le ?_⟩
  have hbound : (((f.natDegree : ℝ) + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ = r / B := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (by positivity) hpos.ne']
  rw [hbound]
  calc r / B * max ‖a‖ 1 ≤ r / B * B :=
        mul_le_mul_of_nonneg_left (hBa a ha) (div_nonneg hr.le hB.le)
    _ = r := div_mul_cancel₀ r hB.ne'

/-- Krasner's lemma for irreducibility: a monic separable irreducible polynomial has a
coefficient neighbourhood of monic irreducible polynomials of the same degree. -/
theorem exists_coeff_nhds_irreducible [IsAlgClosed L] [IsKrasner K L] {f : K[X]}
    (hf : f.Monic) (hs : f.Separable) (hirr : Irreducible f) :
    ∃ ε > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → Irreducible g := by
  obtain ⟨r, hr, hsep⟩ := exists_pos_three_mul_le_norm_sub_rootSet (L := L) f
  obtain ⟨ε, hε, hnear⟩ := exists_coeff_nhds_forall_root_near (L := L) f hf hr
  refine ⟨ε, hε, fun g hg hdeg hcoeff => ?_⟩
  have hfs : (f.map (algebraMap K L)).Splits := IsAlgClosed.splits _
  obtain ⟨a, ha⟩ : ∃ a : L, aeval a f = 0 :=
    IsAlgClosed.exists_aeval_eq_zero L f (degree_pos_of_irreducible hirr).ne'
  have ha' : a ∈ f.rootSet L := hf.mem_rootSet.mpr ha
  obtain ⟨b, hb, hab⟩ := hnear g hg hdeg hcoeff a ha'
  have hbg : aeval b g = 0 := hg.mem_rootSet.mp hb
  have hai : IsIntegral K a := ⟨f, hf, ha⟩
  have hbi : IsIntegral K b := ⟨g, hg, hbg⟩
  have hmin : minpoly K a = f := (minpoly.eq_of_irreducible_of_monic hirr ha hf).symm
  have hmem : a ∈ K⟮b⟯ := by
    refine IsKrasner.krasner (by rw [hmin]; exact hs) (by rw [hmin]; exact hfs) hbi ?_
    intro a' ha'c hne
    have ha'f : a' ∈ f.rootSet L := by
      rw [hf.mem_rootSet, ← hmin]
      exact ha'c.aeval_eq_zero
    have h3 := hsep a ha' a' ha'f hne
    linarith
  have hle : K⟮a⟯ ≤ K⟮b⟯ := IntermediateField.adjoin_simple_le_iff.mpr hmem
  have : FiniteDimensional K K⟮b⟯ := IntermediateField.adjoin.finiteDimensional hbi
  have h1 := IntermediateField.finrank_le_of_le_right hle
  rw [IntermediateField.adjoin.finrank hai, IntermediateField.adjoin.finrank hbi, hmin] at h1
  have hdvd : minpoly K b ∣ g := minpoly.dvd K b hbg
  have heq : g = minpoly K b :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hbi) hg hdvd (by omega)
  rw [heq]
  exact minpoly.irreducible hbi

/-- Krasner's lemma for reducibility: a monic separable reducible polynomial has a
coefficient neighbourhood of monic reducible polynomials of the same degree. -/
theorem exists_coeff_nhds_not_irreducible [IsAlgClosed L] [IsKrasner K L] {f : K[X]}
    (hf : f.Monic) (hs : f.Separable) (hred : ¬ Irreducible f) :
    ∃ ε > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → ¬ Irreducible g := by
  classical
  obtain ⟨r, hr, hsep⟩ := exists_pos_three_mul_le_norm_sub_rootSet (L := L) f
  obtain ⟨ε, hε, hnear⟩ := exists_coeff_nhds_forall_root_near (L := L) f hf hr
  refine ⟨ε, hε, fun g hg hdeg hcoeff hgirr => hred ?_⟩
  have hfs : (f.map (algebraMap K L)).Splits := IsAlgClosed.splits _
  have hgs : (g.map (algebraMap K L)).Splits := IsAlgClosed.splits _
  choose ψ hψ hψd using fun a : f.rootSet L => hnear g hg hdeg hcoeff a a.property
  let Ψ : f.rootSet L → g.rootSet L := fun a => ⟨ψ a, hψ a⟩
  have hinj : Function.Injective Ψ := by
    intro a a' h
    by_contra hne
    have hne' : (a : L) ≠ a' := fun h' => hne (Subtype.ext h')
    have h1 := hsep a a.property a' a'.property hne'
    have h2 := hψd a
    have h3 := hψd a'
    have hψeq : ψ a = ψ a' := congrArg Subtype.val h
    have h4 : ‖(a : L) - a'‖ ≤ ‖(a : L) - ψ a‖ + ‖(a' : L) - ψ a'‖ := by
      rw [hψeq, ← norm_sub_rev (ψ a') (a' : L)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  have hcardf : Fintype.card (f.rootSet L) = f.natDegree := card_rootSet_eq_natDegree hs hfs
  have hcardg : Fintype.card (g.rootSet L) ≤ g.natDegree := by
    simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans g.card_roots_map_le_natDegree
  have hle := Fintype.card_le_of_injective Ψ hinj
  have hbij : Function.Bijective Ψ :=
    (Fintype.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, by omega⟩
  have hgsep : g.Separable :=
    (card_rootSet_eq_natDegree_iff_of_splits hg.ne_zero hgs).mp (by omega)
  obtain ⟨a₀, ha₀⟩ : ∃ a : L, aeval a f = 0 :=
    IsAlgClosed.exists_aeval_eq_zero L f
      (natDegree_pos_iff_degree_pos.mp (hdeg ▸ hgirr.natDegree_pos)).ne'
  let A : f.rootSet L := ⟨a₀, hf.mem_rootSet.mpr ha₀⟩
  have hbg : aeval (ψ A) g = 0 := hg.mem_rootSet.mp (hψ A)
  have hbi : IsIntegral K (ψ A) := ⟨g, hg, hbg⟩
  have hai : IsIntegral K a₀ := ⟨f, hf, ha₀⟩
  have hming : g = minpoly K (ψ A) := minpoly.eq_of_irreducible_of_monic hgirr hbg hg
  have hmem : ψ A ∈ K⟮a₀⟯ := by
    refine IsKrasner.krasner (by rw [← hming]; exact hgsep) (by rw [← hming]; exact hgs) hai ?_
    intro x hx hne
    have hxg : x ∈ g.rootSet L := by
      rw [hg.mem_rootSet, hming]
      exact hx.aeval_eq_zero
    obtain ⟨a', ha'⟩ := hbij.2 ⟨x, hxg⟩
    have hx' : ψ a' = x := congrArg Subtype.val ha'
    have hne' : a₀ ≠ (a' : L) := by
      intro h
      apply hne
      rw [← hx']
      exact congrArg ψ (Subtype.ext h)
    have h1 := hsep a₀ A.property a' a'.property hne'
    have h2 := hψd A
    have h3 := hψd a'
    rw [hx'] at h3
    have h4 : ‖a₀ - (a' : L)‖ ≤ ‖a₀ - ψ A‖ + ‖ψ A - x‖ + ‖(a' : L) - x‖ := by
      calc ‖a₀ - (a' : L)‖ ≤ ‖a₀ - ψ A‖ + ‖ψ A - (a' : L)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖a₀ - ψ A‖ + (‖ψ A - x‖ + ‖x - (a' : L)‖) := by
          gcongr
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = _ := by rw [norm_sub_rev x (a' : L)]; ring
    rw [norm_sub_rev (ψ A) a₀]
    change ‖a₀ - ψ A‖ < r at h2
    linarith
  have hle' : K⟮ψ A⟯ ≤ K⟮a₀⟯ := IntermediateField.adjoin_simple_le_iff.mpr hmem
  have : FiniteDimensional K K⟮a₀⟯ := IntermediateField.adjoin.finiteDimensional hai
  have h1 := IntermediateField.finrank_le_of_le_right hle'
  rw [IntermediateField.adjoin.finrank hbi, IntermediateField.adjoin.finrank hai, ← hming] at h1
  have hdvd : minpoly K a₀ ∣ f := minpoly.dvd K a₀ ha₀
  have hdeg' : (minpoly K a₀).natDegree ≤ f.natDegree := natDegree_le_of_dvd hdvd hf.ne_zero
  have heq : f = minpoly K a₀ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hai) hf hdvd (by omega)
  rw [heq]
  exact minpoly.irreducible hai

end Krasner

section Coefficients

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Below the degree, the coefficients of `polynomialOfCoefficients b` are the entries of `b`;
from the degree on they do not depend on `b`. -/
theorem coeff_polynomialOfCoefficients_sub (b b' : Fin n → R) (k : ℕ) :
    (polynomialOfCoefficients b).coeff k - (polynomialOfCoefficients b').coeff k =
      if h : k < n then b ⟨k, h⟩ - b' ⟨k, h⟩ else 0 := by
  have hsum (c : Fin n → R) : (∑ i : Fin n, C (c i) * X ^ (i : ℕ)).coeff k =
      if h : k < n then c ⟨k, h⟩ else 0 := by
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨k, h⟩]
      · simp
      · intro i _ hi
        exact ite_eq_right_iff.mpr fun hk => absurd (Fin.ext hk.symm) hi
      · simp
    · exact Finset.sum_eq_zero fun i _ => ite_eq_right_iff.mpr fun hk => absurd (hk ▸ i.isLt) h
  simp only [polynomialOfCoefficients, coeff_add, hsum]
  split_ifs <;> ring

end Coefficients

section LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

open _root_.Topology

/-- A property of monic polynomials that holds on a coefficient neighbourhood (for the norm
`LocalGalois.localNormedField F`, which induces the topology of `F`) of
`polynomialOfCoefficients b₀` holds on a neighbourhood of `b₀` in `Fin n → F`. -/
theorem setOf_mem_nhds_of_coeff_nhds {n : ℕ} (P : F[X] → Prop) (b₀ : Fin n → F)
    (h : letI := LocalGalois.localNormedField F
      ∃ ε > 0, ∀ g : F[X], g.Monic → g.natDegree = (polynomialOfCoefficients b₀).natDegree →
        (∀ i, ‖g.coeff i - (polynomialOfCoefficients b₀).coeff i‖ < ε) → P g) :
    {b : Fin n → F | P (polynomialOfCoefficients b)} ∈ 𝓝 b₀ := by
  let := LocalGalois.localNormedField F
  obtain ⟨ε, hε, hP⟩ := h
  have hU : IsOpen (⋂ i : Fin n, (fun b : Fin n → F => b i) ⁻¹' Metric.ball (b₀ i) ε) :=
    isOpen_iInter_of_finite fun i => Metric.isOpen_ball.preimage (continuous_apply i)
  refine Filter.mem_of_superset
    (hU.mem_nhds (Set.mem_iInter.mpr fun i => Metric.mem_ball_self hε)) fun b hbU => ?_
  have hb := polynomialOfCoefficients_isMonicOfDegree b
  have hb₀ := polynomialOfCoefficients_isMonicOfDegree b₀
  refine hP _ hb.monic (by rw [hb.natDegree_eq, hb₀.natDegree_eq]) fun k => ?_
  rw [coeff_polynomialOfCoefficients_sub]
  split_ifs with hk
  · have := Set.mem_iInter.mp hbU ⟨k, hk⟩
    simpa [Metric.mem_ball, dist_eq_norm] using this
  · simpa using hε

variable [CharZero F]

/-- The monic polynomials of degree `n` that are separable and irreducible over `F` form an
open subset of the coefficient space `Fin n → F` (Krasner's lemma). -/
theorem isOpen_separable_irreducible_polynomialOfCoefficients (n : ℕ) :
    IsOpen {b : Fin n → F | (polynomialOfCoefficients b).Separable ∧
      Irreducible (polynomialOfCoefficients b)} := by
  rw [isOpen_iff_mem_nhds]
  rintro b₀ ⟨hs, hirr⟩
  refine Filter.inter_mem ((isOpen_separable_polynomialOfCoefficients n).mem_nhds hs) ?_
  apply setOf_mem_nhds_of_coeff_nhds Irreducible b₀
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.localNormedField_complete F
  let : NontriviallyNormedField (AlgebraicClosure F) :=
    spectralNorm.nontriviallyNormedField F (AlgebraicClosure F)
  let : NormedAlgebra F (AlgebraicClosure F) := spectralNorm.normedAlgebra F (AlgebraicClosure F)
  exact exists_coeff_nhds_irreducible (L := AlgebraicClosure F)
    (polynomialOfCoefficients_isMonicOfDegree b₀).monic hs hirr

/-- The monic polynomials of degree `n` that are separable and reducible over `F` form an
open subset of the coefficient space `Fin n → F` (Krasner's lemma). -/
theorem isOpen_separable_not_irreducible_polynomialOfCoefficients (n : ℕ) :
    IsOpen {b : Fin n → F | (polynomialOfCoefficients b).Separable ∧
      ¬ Irreducible (polynomialOfCoefficients b)} := by
  rw [isOpen_iff_mem_nhds]
  rintro b₀ ⟨hs, hred⟩
  refine Filter.inter_mem ((isOpen_separable_polynomialOfCoefficients n).mem_nhds hs) ?_
  apply setOf_mem_nhds_of_coeff_nhds (fun p => ¬ Irreducible p) b₀
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.localNormedField_complete F
  let : NontriviallyNormedField (AlgebraicClosure F) :=
    spectralNorm.nontriviallyNormedField F (AlgebraicClosure F)
  let : NormedAlgebra F (AlgebraicClosure F) := spectralNorm.normedAlgebra F (AlgebraicClosure F)
  exact exists_coeff_nhds_not_irreducible (L := AlgebraicClosure F)
    (polynomialOfCoefficients_isMonicOfDegree b₀).monic hs hred

end LocalField

section GeneralLinear

open Langlands.JacquetLanglands Langlands.TraceFormula
open SigmaLiftCharacterIdentity (coefficients coefficients_conj continuous_coefficients)

variable {F : Type*} [Field F] {n : ℕ}

/-- `γ` is regular elliptic exactly when the monic polynomial with the coefficients of its
characteristic polynomial is separable and irreducible. -/
theorem isRegularElliptic_iff_coefficients (γ : GeneralLinear n F) :
    IsRegularElliptic γ ↔ (polynomialOfCoefficients (coefficients γ)).Separable ∧
      Irreducible (polynomialOfCoefficients (coefficients γ)) := by
  rw [polynomialOfCoefficients_coefficients]
  rfl

/-- `δ` is σ-elliptic exactly when the monic polynomial with coefficients
`normCoefficients h δ` is separable and irreducible. -/
theorem isSigmaElliptic_iff_normCoefficients {E : Type*} [CommRing E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) (δ : GeneralLinear n E) :
    IsSigmaElliptic σ l δ ↔ (polynomialOfCoefficients (normCoefficients h δ)).Separable ∧
      Irreducible (polynomialOfCoefficients (normCoefficients h δ)) := by
  constructor
  · rintro ⟨γ, ha, hγ⟩
    rw [normCoefficients_eq_of_associated h ha]
    exact (isRegularElliptic_iff_coefficients γ).mp hγ
  · rintro ⟨hs, hi⟩
    obtain ⟨γ, ha, -⟩ := (isSigmaRegular_iff_separable_normCoefficients h δ).mpr hs
    refine ⟨γ, ha, (isRegularElliptic_iff_coefficients γ).mpr ?_⟩
    rw [← normCoefficients_eq_of_associated h ha]
    exact ⟨hs, hi⟩

/-- A regular semisimple element that is not regular elliptic has a separable reducible
characteristic polynomial. -/
theorem isRegularSemisimple_and_not_isRegularElliptic_iff_coefficients (γ : GeneralLinear n F) :
    (IsRegularSemisimple γ ∧ ¬ IsRegularElliptic γ) ↔
      (polynomialOfCoefficients (coefficients γ)).Separable ∧
        ¬ Irreducible (polynomialOfCoefficients (coefficients γ)) := by
  rw [isRegularElliptic_iff_coefficients, isRegularSemisimple_iff_separable_coefficients]
  tauto

/-- A σ-regular element that is not σ-elliptic has separable reducible norm polynomial. -/
theorem isSigmaRegular_and_not_isSigmaElliptic_iff_normCoefficients {E : Type*} [CommRing E]
    [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) (δ : GeneralLinear n E) :
    (IsSigmaRegular σ l δ ∧ ¬ IsSigmaElliptic σ l δ) ↔
      (polynomialOfCoefficients (normCoefficients h δ)).Separable ∧
        ¬ Irreducible (polynomialOfCoefficients (normCoefficients h δ)) := by
  rw [isSigmaElliptic_iff_normCoefficients h, isSigmaRegular_iff_separable_normCoefficients h]
  tauto

/-- Regular ellipticity is invariant under conjugation. -/
theorem isRegularElliptic_conj_iff (x γ : GeneralLinear n F) :
    IsRegularElliptic (x⁻¹ * γ * x) ↔ IsRegularElliptic γ := by
  rw [isRegularElliptic_iff_coefficients, isRegularElliptic_iff_coefficients, coefficients_conj]

/-- σ-ellipticity is invariant under σ-conjugation. -/
theorem isSigmaElliptic_twistedConj_iff {E : Type*} [CommRing E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) (x δ : GeneralLinear n E) :
    IsSigmaElliptic σ l (x⁻¹ * δ * entrywiseAut σ n x) ↔ IsSigmaElliptic σ l δ := by
  rw [isSigmaElliptic_iff_normCoefficients h, isSigmaElliptic_iff_normCoefficients h]
  rw [show x⁻¹ * δ * entrywiseAut σ n x = twistedConj (entrywiseAut σ n) x δ from rfl,
    normCoefficients_twistedConj]

/-- If `δ` is associated with `γ`, then `δ` is σ-elliptic exactly when `γ` is regular
elliptic. -/
theorem isSigmaElliptic_iff_of_isNormAssociated {E : Type*} [CommRing E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) {δ : GeneralLinear n E}
    {γ : GeneralLinear n F} (ha : IsNormAssociated σ l δ γ) :
    IsSigmaElliptic σ l δ ↔ IsRegularElliptic γ := by
  rw [isSigmaElliptic_iff_normCoefficients h, isRegularElliptic_iff_coefficients,
    normCoefficients_eq_of_associated h ha]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]

/-- The regular semisimple elements that are not regular elliptic form an open subset of
`GL_n(F)`. -/
theorem isOpen_setOf_isRegularSemisimple_and_not_isRegularElliptic (n : ℕ) :
    IsOpen {γ : GeneralLinear n F | IsRegularSemisimple γ ∧ ¬ IsRegularElliptic γ} := by
  rw [show {γ : GeneralLinear n F | IsRegularSemisimple γ ∧ ¬ IsRegularElliptic γ} =
      coefficients ⁻¹' {b : Fin n → F | (polynomialOfCoefficients b).Separable ∧
        ¬ Irreducible (polynomialOfCoefficients b)} from
    Set.ext isRegularSemisimple_and_not_isRegularElliptic_iff_coefficients]
  exact (isOpen_separable_not_irreducible_polynomialOfCoefficients n).preimage
    continuous_coefficients

variable {E : Type*} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l : ℕ}

/-- The σ-elliptic set is open in `GL_n(E)`. -/
theorem isOpen_setOf_isSigmaElliptic (h : IsCyclicAlgebra σ l) (n : ℕ) :
    IsOpen {δ : GeneralLinear n E | IsSigmaElliptic σ l δ} := by
  rw [show {δ : GeneralLinear n E | IsSigmaElliptic σ l δ} = normCoefficients h ⁻¹'
      {b : Fin n → F | (polynomialOfCoefficients b).Separable ∧
        Irreducible (polynomialOfCoefficients b)} from
    Set.ext (isSigmaElliptic_iff_normCoefficients h)]
  exact (isOpen_separable_irreducible_polynomialOfCoefficients n).preimage
    (continuous_normCoefficients h)

/-- The σ-regular elements that are not σ-elliptic form an open subset of `GL_n(E)`. -/
theorem isOpen_setOf_isSigmaRegular_and_not_isSigmaElliptic (h : IsCyclicAlgebra σ l) (n : ℕ) :
    IsOpen {δ : GeneralLinear n E | IsSigmaRegular σ l δ ∧ ¬ IsSigmaElliptic σ l δ} := by
  rw [show {δ : GeneralLinear n E | IsSigmaRegular σ l δ ∧ ¬ IsSigmaElliptic σ l δ} =
      normCoefficients h ⁻¹' {b : Fin n → F | (polynomialOfCoefficients b).Separable ∧
        ¬ Irreducible (polynomialOfCoefficients b)} from
    Set.ext (isSigmaRegular_and_not_isSigmaElliptic_iff_normCoefficients h)]
  exact (isOpen_separable_not_irreducible_polynomialOfCoefficients n).preimage
    (continuous_normCoefficients h)

end GeneralLinear

end Langlands.BaseChange

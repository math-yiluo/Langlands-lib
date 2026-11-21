import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.JacquetLanglands.LocalCharacter

/-! # Isolation from a finite list of ordinary and twisted rational classes -/

noncomputable section

namespace Langlands.TraceFormula

open BaseChange JacquetLanglands
open HarmonicAnalysis.Distribution (charpoly_eq_of_coeff_eq)
open BaseChange.SigmaLiftCharacterIdentity (coefficients coefficients_conj continuous_coefficients)

universe u v w

section Algebra

variable {K : Type u} [Field K] {F : Type v} [Field F] {n : ℕ}

private theorem rationalConj_of_mappedCoefficients_eq (ι : K →+* F)
    {γ q : GeneralLinear n K} (hγ : IsRegularSemisimple γ)
    (h : coefficients (Matrix.GeneralLinearGroup.map ι q) =
      coefficients (Matrix.GeneralLinearGroup.map ι γ)) :
    ∃ y : GeneralLinear n K, y⁻¹ * q * y = γ := by
  have hchar : q.val.charpoly = γ.val.charpoly := by
    apply charpoly_eq_of_coeff_eq
    intro i
    apply ι.injective
    have hi := congrFun h i
    change (q.val.map ι).charpoly.coeff i = (γ.val.map ι).charpoly.coeff i at hi
    simpa only [Matrix.charpoly_map, Polynomial.coeff_map] using hi
  obtain ⟨y, hy⟩ := exists_matrix_conj_of_charpoly_eq_of_separable γ.val q.val hγ hchar
  have hy' : y * γ * y⁻¹ = q := Units.ext hy
  refine ⟨y, ?_⟩
  rw [← hy']
  group

variable {L : Type w} [Field L] [Algebra K L]

/-- Associated base matrices in the same rational conjugacy class determine a
single rational twisted conjugacy class upstairs. -/
theorem rationalTwistedConj_of_normAssociated_conj
    {σ : L ≃ₐ[K] L} {l : ℕ} (hσ : IsCyclicAlgebra σ l)
    {δ' δ : GeneralLinear n L} {γ' γ : GeneralLinear n K}
    (hδ' : IsNormAssociated σ l δ' γ') (hδ : IsNormAssociated σ l δ γ)
    {y : GeneralLinear n K} (hy : y⁻¹ * γ' * y = γ) :
    ∃ x : GeneralLinear n L, x⁻¹ * δ' * entrywiseAut σ n x = δ := by
  obtain ⟨a, ha⟩ := hδ'
  obtain ⟨b, hb⟩ := hδ
  let z := baseChange K L n y
  have hz : z⁻¹ * baseChange K L n γ' * z = baseChange K L n γ := by
    simp only [z, ← map_inv, ← map_mul, hy]
  refine (cyclicNormLemma K L σ l n hσ).2.2 δ' δ ⟨a * z * b⁻¹, ?_⟩
  calc
    (a * z * b⁻¹)⁻¹ * cyclicNorm σ l δ' * (a * z * b⁻¹) =
        b * (z⁻¹ * (a⁻¹ * cyclicNorm σ l δ' * a) * z) * b⁻¹ := by group
    _ = b * (b⁻¹ * cyclicNorm σ l δ * b) * b⁻¹ := by rw [ha, hz, hb]
    _ = cyclicNorm σ l δ := by group

end Algebra

section Neighbourhood

variable {K : Type u} [Field K] {F : Type v} [Field F] [TopologicalSpace F]
  [IsTopologicalRing F] [T2Space F] {n : ℕ}
  [LocallyCompactSpace (GeneralLinear n F)] [TotallyDisconnectedSpace (GeneralLinear n F)]

/-- A compact open neighbourhood of a regular rational matrix can exclude
the local orbits of all rational classes in a prescribed finite list except
the class of that matrix. -/
theorem exists_rationalRegularOrbitCutoff (ι : K →+* F)
    (R : Finset (GeneralLinear n K)) (γ : GeneralLinear n K) (hγ : IsRegularSemisimple γ)
    {V : Set (GeneralLinear n F)} (hV : IsOpen V) (hγV : Matrix.GeneralLinearGroup.map ι γ ∈ V) :
    ∃ U : Set (GeneralLinear n F), IsCompact U ∧ IsClopen U ∧
      Matrix.GeneralLinearGroup.map ι γ ∈ U ∧ U ⊆ V ∧
      ∀ q ∈ R, (∃ x : GeneralLinear n F, x⁻¹ * Matrix.GeneralLinearGroup.map ι q * x ∈ U) →
        ∃ y : GeneralLinear n K, y⁻¹ * q * y = γ := by
  let a := Matrix.GeneralLinearGroup.map (n := Fin n) ι
  let bad := (coefficients ∘ a) '' (R : Set (GeneralLinear n K)) \ {coefficients (a γ)}
  have hbad : bad.Finite := (R.finite_toSet.image _).sdiff
  have hW : IsOpen (V ∩ coefficients ⁻¹' badᶜ) :=
    hV.inter (hbad.isClosed.isOpen_compl.preimage continuous_coefficients)
  have hmem : a γ ∈ V ∩ coefficients ⁻¹' badᶜ := by
    refine ⟨hγV, ?_⟩
    simp [bad]
  obtain ⟨U, hUcompact, hUclopen, hγU, hUW⟩ := exists_isCompact_isClopen_subset hW hmem
  refine ⟨U, hUcompact, hUclopen, hγU, hUW.trans Set.inter_subset_left, ?_⟩
  rintro q hq ⟨x, hx⟩
  apply rationalConj_of_mappedCoefficients_eq ι hγ
  by_contra hne
  have hx' : coefficients (x⁻¹ * a q * x) ∉ bad := (hUW hx).2
  rw [coefficients_conj] at hx'
  exact hx' ⟨⟨q, hq, rfl⟩, hne⟩

end Neighbourhood

/-- A single compact open cutoff excludes all competing ordinary rational
classes and all competing twisted rational classes from finite lists, using
the base matrices associated with the twisted classes. -/
def RationalRegularOrbitCutoffStatement : Prop :=
  ∀ (K : Type u) [Field K] (L : Type w) [Field L] [Algebra K L]
    (F : Type v) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    (n : ℕ) [LocallyCompactSpace (GeneralLinear n F)]
      [TotallyDisconnectedSpace (GeneralLinear n F)]
    (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (ι : K →+* F) (R : Finset (GeneralLinear n K)) (T : Finset (GeneralLinear n L))
      (γ : GeneralLinear n K) (δ : GeneralLinear n L)
      (a : GeneralLinear n L → GeneralLinear n K),
      IsRegularSemisimple γ → IsNormAssociated σ l δ γ →
      (∀ t ∈ T, IsNormAssociated σ l t (a t)) →
      ∀ V : Set (GeneralLinear n F), IsOpen V → Matrix.GeneralLinearGroup.map ι γ ∈ V →
      ∃ U : Set (GeneralLinear n F), IsCompact U ∧ IsClopen U ∧
        Matrix.GeneralLinearGroup.map ι γ ∈ U ∧ U ⊆ V ∧
        (∀ q ∈ R, (∃ x : GeneralLinear n F, x⁻¹ * Matrix.GeneralLinearGroup.map ι q * x ∈ U) →
          ∃ y : GeneralLinear n K, y⁻¹ * q * y = γ) ∧
        (∀ t ∈ T, (∃ x : GeneralLinear n F, x⁻¹ * Matrix.GeneralLinearGroup.map ι (a t) * x ∈ U) →
          ∃ y : GeneralLinear n L, y⁻¹ * t * entrywiseAut σ n y = δ)

theorem rationalRegularOrbitCutoff : RationalRegularOrbitCutoffStatement.{u, v, w} := by
  classical
  intro K _ L _ _ F _ _ _ _ n _ _ σ l hσ ι R T γ δ a hγ hδ hT V hV hγV
  obtain ⟨U, hUcompact, hUclopen, hγU, hUV, hU⟩ :=
    exists_rationalRegularOrbitCutoff ι (R ∪ T.image a) γ hγ hV hγV
  refine ⟨U, hUcompact, hUclopen, hγU, hUV,
    fun q hq hx ↦ hU q (Finset.mem_union_left _ hq) hx, ?_⟩
  intro t ht hx
  obtain ⟨y, hy⟩ := hU (a t) (Finset.mem_union_right _ (Finset.mem_image_of_mem a ht)) hx
  exact rationalTwistedConj_of_normAssociated_conj hσ (hT t ht) hδ hy

end Langlands.TraceFormula

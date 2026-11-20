import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelFixedSpan
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelMonomialBound
import Langlands.Representation.Plancherel.UnitaryRegularOperatorExpansion

/-! # Level seminorms for sections related by a regular compact operator -/

noncomputable section

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uG' uV uV' uI uI' uJ uJ'

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (H : OpenSubgroup G)

variable {G' : Type uG'} [Group G'] [TopologicalSpace G'] [LocallyCompactSpace G']
  [NonarchimedeanGroup G'] {P' M' U' : Subgroup G'}
  (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set G'))
  (hP' : IsClosed (P' : Set G')) (K' : OpenSubgroup G') (hK' : IsCompact (K' : Set G'))
  (hPK' : ∀ g : G', ∃ p : P', ∃ k : K', g = (p : G') * (k : G'))
  {I' : Type uI'} (ν' : I' → (M' →* ℝ≥0ˣ))
  (π' : IrreducibleAdmissibleRep.{0, uG', uV'} (k := ℂ) (G := M'))
  (hν' : ∀ i, Continuous (ν' i)) (hr' : Continuous h'.projection)
  {J' : Type uJ'} [Fintype J'] [DecidableEq J'] (e' : unitaryUnramifiedCharacters ν' ≃* (J' → Circle))

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "Picture'" => ProductInducedCompactPicture h' K' π'.obj
set_option hygiene false in
local notation "UpperLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "seminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "InputIndex" => List J × Module.Dual ℂ Picture
set_option hygiene false in
local notation "LowerSections" => productInducedSmoothOrbitSections ν' π' e' h' hU' K' hP' hK' hν' hr' hPK'
set_option hygiene false in
local notation "LowerLevel[" H' "]" => OrbitSectionLevel ν' π' e' h' hU' K' hP' hK' hν' hr' hPK' H'
set_option hygiene false in
local notation "includeLower[" H' "]" => OrbitSectionLevel.toSections ν' π' e' h' hU' K' hP' hK' hν' hr' hPK' H'
set_option hygiene false in
local notation "lowerNorms[" H' "]" => OrbitSectionLevel.seminormFamily ν' π' e' h' hU' K' hP' hK' hν' hr' hPK' H'
set_option hygiene false in
local notation "OutputIndex" => List J' × Module.Dual ℂ Picture'
set_option hygiene false in
local notation "R" => productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
set_option hygiene false in
local notation "R'" => productInducedSmoothOrbitCompactRestriction h' hU' ν' π' K' hP' hK' hν' hr' hPK' e'

variable (a : J → J' → ℤ) (d : unramifiedRegularFunctions ν)
  (A : unramifiedCharacters ν → Picture →ₗ[ℂ] Picture') (Ψ : UpperLevel → LowerSections)

/-- The compact formula for a family of lower sections on one upper level.
A regular operator acts in the upper coordinates after the monomial pullback. -/
def HasRegularOrbitSectionTransfer : Prop :=
  ∀ q w, R' (Ψ q) w = unitaryRegularOperator ν e d A (finiteTorusMonomial a w)
    (R (includeLevel q) (finiteTorusMonomial a w))

set_option maxHeartbeats 1600000 in
/-- Under the compact formula, denominator regularity and polynomiality
supply a common lower section level and finite derivative bounds. -/
theorem exists_regularOrbitSectionTransfer_finsetSup_bound
    (hHK : H ≤ K) (hcofinal : CompactOpenCofinal M)
    (he : HasLaurentUnitaryCoordinates ν e)
    (hd : ∀ z : unitaryUnramifiedCharacters ν, d.val ⟨z.val, z.property.1⟩ ≠ 0)
    (hA : UnramifiedOperatorFamily.IsPolynomialOperatorOn Set.univ (fun z => A z.val))
    (hΨ : HasRegularOrbitSectionTransfer h hU hP K hK hPK ν π hν hr e H
      h' hU' hP' K' hK' hPK' ν' π' hν' hr' e' a d A Ψ) :
    ∃ (H' : OpenSubgroup G'), H' ≤ K' ∧
      ∃ T : UpperLevel → LowerLevel[H'], (∀ q, includeLower[H'] (T q) = Ψ q) ∧
        ∀ t : Finset OutputIndex, ∃ s : Finset InputIndex, ∃ c : ℝ≥0,
          ∀ q, (t.sup lowerNorms[H']) (T q) ≤ (c : ℝ) * (s.sup seminorms) q := by
  classical
  let Fixed := orbitSectionFixedCoefficients h K π H
  let := finiteDimensional_orbitSectionFixedCoefficients h K π hK hcofinal H hHK
  let basis := Module.finBasis ℂ Fixed
  let restrictFixed := orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK
  obtain ⟨N, c, v, ℓ, _, hexpansion⟩ := exists_unitaryRegularOperator_expansion ν e he d
    (fun z => hd (e.symm z)) A hA basis
  let B := (i : Fin (Module.finrank ℂ Fixed)) × Fin (N i)
  let vectors (b : B) : Picture' := v b.1 b.2
  have hformula (q : UpperLevel) (w : J' → Circle) : R' (Ψ q) w = ∑ b : B,
      (c b.1 b.2).val (finiteTorusMonomial a w) •
        ℓ b.1 ((restrictFixed q (finiteTorusMonomial a w)).val) • vectors b := by
    rw [Fintype.sum_sigma]
    exact (hΨ q w).trans (hexpansion (restrictFixed q (finiteTorusMonomial a w)) (finiteTorusMonomial a w))
  obtain ⟨H', hH'K, hspan⟩ := exists_span_le_orbitSectionFixedCoefficients h' K' π'
    (Finset.univ : Finset B) vectors
  have hfixed (q : UpperLevel) (w : J' → Circle) :
      R' (Ψ q) w ∈ orbitSectionFixedCoefficients h' K' π' H' := by
    apply hspan
    rw [hformula q w]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨b, Finset.mem_univ b, rfl⟩))
  let T (q : UpperLevel) : LowerLevel[H'] :=
    orbitSectionLevelOfFixedRestriction h' K' π' hU' hP' hK' hPK'
      ν' hν' hr' e' H' hH'K (Ψ q) (hfixed q)
  have hT (q : UpperLevel) : includeLower[H'] (T q) = Ψ q := rfl
  have hseminorm (x : OutputIndex) :
      ∃ s : Finset InputIndex, ∃ C : ℝ≥0, ∀ q,
        lowerNorms[H'] x (T q) ≤ (C : ℝ) * (s.sup seminorms) q := by
    let f (q : UpperLevel) := orbitSectionCoefficient ν' π' e' h' hU' K' hP' hK'
      hν' hr' hPK' x.2 (includeLower[H'] (T q))
    let w (b : B) := (x.2 (vectors b)) • c b.1 b.2
    have hf (q : UpperLevel) (z : J' → Circle) : (f q).val z = ∑ b ∈ (Finset.univ : Finset B),
        (w b).val (finiteTorusMonomial a z) * (orbitSectionCoefficient ν π e h hU K
          hP hK hν hr hPK (ℓ b.1) (includeLevel q)).val (finiteTorusMonomial a z) := by
      change x.2 (R' (includeLower[H'] (T q)) z) = _
      rw [hT, hformula q z, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, map_smul]
      change (c b.1 b.2).val _ * (ℓ b.1 ((restrictFixed q _).val) * x.2 (vectors b)) =
        (x.2 (vectors b) * (c b.1 b.2).val _) * ℓ b.1 ((restrictFixed q _).val)
      ring
    exact exists_orbitSectionLevel_monomialSeminorm_bound h hU hP K hK hPK
      ν π hν hr e H a Finset.univ w (fun b => ℓ b.1) f hf x.1
  refine ⟨H', hH'K, T, hT, fun t => ?_⟩
  choose s C hC using hseminorm
  let support := t.biUnion s
  let total := ∑ x ∈ t, C x
  refine ⟨support, total, fun q => ?_⟩
  apply Seminorm.finset_sup_apply_le (mul_nonneg total.coe_nonneg (apply_nonneg _ _))
  intro x hx
  have hs : s x ⊆ support := fun _ hy => Finset.mem_biUnion.mpr ⟨x, hx, hy⟩
  have hsup := Finset.sup_mono (f := seminorms) hs
  have hCtotal : C x ≤ total := Finset.single_le_sum (fun _ _ => zero_le) hx
  exact (hC x q).trans (mul_le_mul (by exact_mod_cast hCtotal) (hsup q)
    (apply_nonneg _ _) total.coe_nonneg)

end Langlands.HarishChandraSchwartz

import Langlands.Global.AdelicWeakConstantTermRestriction
import Langlands.Global.AdelicStandardConstantTerm

/-! # Weak constant-term transitivity from nested exponent decompositions -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- On the positive split component of `P`, the half moduli of two nested standard parabolics
`Q ≤ P` agree. The extra determinant factor for `Q` comes from the radical inside `M_P`, and
the split component of `P` is central in `M_P`. -/
def StandardNestedHalfModulusCompatibilityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (Q P : StandardIndex F G fam.i fam.ν), Q ≤ P →
    ∀ (a : fam.positiveSplitComponent P) (b : fam.positiveSplitComponent Q),
      map F (fam.P Q) G (fam.p Q) b = map F (fam.P P) G (fam.p P) a →
        fam.halfModulus Q b = fam.halfModulus P a

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Functions" => (AdelicGroupPoints F G → ℂ)

variable (J : StandardIndex F G fam.i fam.ν)

/-- Regroup a finite sum of exponent decompositions by their normalized label. On the unitary
labels the regrouped sum is the sum of the original weak parts. -/
theorem exists_automorphicExponentDecomposition_sum {I : Type*}
    (s : Finset I) (f : I → Functions)
    (t : I → Finset (ComplexCharacterParameter F (fam.P J)))
    (c : I → ComplexCharacterParameter F (fam.P J) → Functions)
    (hc : ∀ i ∈ s, fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (f i) (t i) (c i)) :
    ∃ u e, fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (∑ i ∈ s, f i) u e ∧
      fam.unitaryExponentSum J u e = ∑ i ∈ s, fam.unitaryExponentSum J (t i) (c i) := by
  classical
  let u := s.biUnion t
  let e (lam : ComplexCharacterParameter F (fam.P J)) := ∑ i ∈ s, if lam ∈ t i then c i lam else 0
  have hu (i : I) (hi : i ∈ s) : t i ⊆ u := Finset.subset_biUnion_of_mem t hi
  refine ⟨u, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [e]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => by
      rw [(hc i hi).sum_eq, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hu i hi)]
  · intro lam _
    apply (automorphicFunctionsOn _ _ _ _ _).sum_mem
    intro i hi
    change fam.IsAutomorphicOn hsmooth Kinf rho J (if lam ∈ t i then c i lam else 0)
    by_cases h : lam ∈ t i
    · simpa only [ite_eq_left h] using (hc i hi).automorphic lam h
    · simpa only [ite_eq_right h] using fam.isAutomorphicOn_zero hsmooth Kinf rho J
  · intro lam _
    apply (fam.hasExponent_iff J lam _).mpr
    apply fam.hasUnnormalizedExponent_sum J
    intro i hi
    by_cases h : lam ∈ t i
    · simpa only [ite_eq_left h] using (fam.hasExponent_iff J lam _).mp ((hc i hi).exponent lam h)
    · simpa only [ite_eq_right h] using fam.hasUnnormalizedExponent_zero J
        (lam + halfModulusParameter F (fam.P J))
  · unfold unitaryExponentSum
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_mem]
    congr 1
    ext lam
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hu i hi h.1, h.2⟩, h.1⟩⟩

variable {Q P : StandardIndex F G fam.i fam.ν}

variable (hQP : Q ≤ P)

include hQP in
private theorem constantTerm_sum_of_automorphicOn {I : Type*}
    (s : Finset I) (f : I → Functions)
    (hf : ∀ i ∈ s, fam.IsAutomorphicOn hsmooth Kinf rho P (f i)) :
    fam.constantTerm Q (∑ i ∈ s, f i) = ∑ i ∈ s, fam.constantTerm Q (f i) := by
  funext g
  simp only [constantTerm, subgroupConstantTerm, Finset.sum_apply]
  exact integral_finsetSum s fun i hi =>
    fam.integrable_constantTermIntegrand_of_le P Q hQP (hf i hi).2.1.1 (hf i hi).1 g

include hQP in
/-- The weak term along `Q` is the weak `Q` term of the weak term along `P`, given a
`Q`-decomposition for each component of the `P` constant term and the nested modulus
comparison. This proves the algebraic implication in Delorme's Lemma 3.8 (iii). -/
theorem isWeakConstantTerm_of_nested_decompositions
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    {Φ ψ χ : Functions}
    (hc : Continuous Φ) (hi : IsLeftInvariantUnder F G (rationalSubgroup F G) Φ)
    {s : Finset (ComplexCharacterParameter F (fam.P P))}
    {c : ComplexCharacterParameter F (fam.P P) → Functions}
    (hs : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho P (fam.constantTerm P Φ) s c)
    (hψ : ψ = fam.unitaryExponentSum P s c)
    (hχ : fam.IsWeakConstantTerm hsmooth Kinf rho Q Φ χ)
    (hDec : ∀ lam ∈ s, ∃ t e,
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q (c lam)) t e) :
    fam.IsWeakConstantTerm hsmooth Kinf rho Q ψ χ := by
  classical
  have hchoice (lam : ComplexCharacterParameter F (fam.P P)) : ∃ t e, lam ∈ s →
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q (c lam)) t e := by
    by_cases h : lam ∈ s
    · obtain ⟨t, e, he⟩ := hDec lam h
      exact ⟨t, e, fun _ => he⟩
    · exact ⟨∅, 0, fun hh => (h hh).elim⟩
  choose t e hte using hchoice
  have hnon (lam : ComplexCharacterParameter F (fam.P P)) (hlam : lam ∈ s)
      (hne : parameterRealPart F (fam.P P) lam ≠ 0) : fam.unitaryExponentSum Q (t lam) (e lam) = 0 := by
    have hrad : fam.IsRadicalInvariant P (c lam) := by
      intro u g
      obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp u.property
      exact (hs.automorphic lam hlam).1 _ (Subgroup.mem_sup_left ⟨v, hv⟩) g
    have hint : fam.HasIntegrableConstantTerm Q (c lam) := by
      intro g
      exact fam.integrable_constantTermIntegrand_of_le P Q hQP (hs.automorphic lam hlam).2.1.1
        (hs.automorphic lam hlam).1 g
    exact fam.unitaryExponentSum_constantTerm_eq_zero_of_nonunitary hQP (hs.exponent lam hlam)
      hrad hint (hte lam hlam).sum_eq (hte lam hlam).exponent (hδ F G fam Q P hQP) hne
  let w := s.filter fun lam => parameterRealPart F (fam.P P) lam = 0
  have hw : w ⊆ s := Finset.filter_subset _ _
  have hctAll := fam.constantTerm_sum_of_automorphicOn hsmooth Kinf rho hQP s c hs.automorphic
  have hctWeak := fam.constantTerm_sum_of_automorphicOn hsmooth Kinf rho hQP w c
    (fun lam h => hs.automorphic lam (hw h))
  have hcompose : fam.constantTerm Q (fam.constantTerm P Φ) = fam.constantTerm Q Φ := by
    let v : ContinuousRationalFunctions F G := ⟨⟨Φ, fun a g => hi _ ⟨a, rfl⟩ g⟩, hc⟩
    exact fam.constantTerm_constantTerm_of_le hQP v
  rw [← hs.sum_eq, hcompose] at hctAll
  rw [← show ψ = ∑ lam ∈ w, c lam from hψ] at hctWeak
  obtain ⟨sAll, eAll, hAll, hAllW⟩ := fam.exists_automorphicExponentDecomposition_sum
    hsmooth Kinf rho Q s (fun lam => fam.constantTerm Q (c lam)) t e hte
  obtain ⟨sWeak, eWeak, hWeak, hWeakW⟩ := fam.exists_automorphicExponentDecomposition_sum
    hsmooth Kinf rho Q w (fun lam => fam.constantTerm Q (c lam)) t e (fun lam h => hte lam (hw h))
  rw [← hctAll] at hAll
  rw [← hctWeak] at hWeak
  have hOrig : fam.IsWeakConstantTerm hsmooth Kinf rho Q Φ (fam.unitaryExponentSum Q sAll eAll) :=
    ⟨sAll, eAll, hAll, rfl⟩
  refine ⟨sWeak, eWeak, hWeak, ?_⟩
  rw [hWeakW, show χ = fam.unitaryExponentSum Q sAll eAll from hχ.unique hOrig, hAllW]
  symm
  exact Finset.sum_subset hw fun lam hlam hnot => hnon lam hlam
    (fun heq => hnot (Finset.mem_filter.mpr ⟨hlam, heq⟩))

end StandardParabolicFamily
end Langlands.Global

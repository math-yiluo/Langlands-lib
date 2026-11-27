import Langlands.Global.AdelicCuspidalTestAlgebra
import Langlands.Global.AdelicEisensteinFarRegionTerms

/-! # Cuspidal expansions of a far-region Eisenstein comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "Y" => (AdelicGroupPoints F G → ℂ)

local instance farRegionExpansionSplitCommGroup (J : StandardIndex F G fam.i fam.ν) :
    CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.2 b.2)

section Padding

variable {J : StandardIndex F G fam.i fam.ν}

private theorem isAutomorphicOn_pad {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y}
    (hc : ∀ ν ∈ s, fam.IsAutomorphicOn hsmooth Kinf rho J (c ν))
    (ν : ComplexCharacterParameter F (fam.P J)) :
    fam.IsAutomorphicOn hsmooth Kinf rho J (open Classical in if ν ∈ s then c ν else 0) := by
  classical
  split_ifs with h
  · exact hc ν h
  · exact fam.isAutomorphicOn_zero hsmooth Kinf rho J

private theorem isCuspidalAlong_pad {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y} (hc : ∀ ν ∈ s, fam.IsCuspidalAlong J (c ν))
    (ν : ComplexCharacterParameter F (fam.P J)) :
    fam.IsCuspidalAlong J (open Classical in if ν ∈ s then c ν else 0) := by
  classical
  split_ifs with h
  · exact hc ν h
  · exact fam.isCuspidalAlong_zero J

private theorem hasUnnormalizedExponent_pad {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y}
    (hc : ∀ ν ∈ s, fam.HasUnnormalizedExponent J ν (c ν))
    (ν : ComplexCharacterParameter F (fam.P J)) :
    fam.HasUnnormalizedExponent J ν (open Classical in if ν ∈ s then c ν else 0) := by
  classical
  split_ifs with h
  · exact hc ν h
  · exact fam.hasUnnormalizedExponent_zero J ν

open Classical in
/-- The difference of two exponent decompositions, padded to the union of their labels. -/
theorem isExponentDecomposition_sub {f h : Y}
    {s t : Finset (ComplexCharacterParameter F (fam.P J))}
    {c e : ComplexCharacterParameter F (fam.P J) → Y}
    (hf : fam.IsExponentDecomposition hsmooth Kinf rho J f s c)
    (hh : fam.IsExponentDecomposition hsmooth Kinf rho J h t e) :
    fam.IsExponentDecomposition hsmooth Kinf rho J (f - h) (s ∪ t)
      (fun ν => (if ν ∈ s then c ν else 0) - (if ν ∈ t then e ν else 0)) where
  sum_eq := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr Finset.subset_union_left,
      Finset.inter_eq_right.mpr Finset.subset_union_right, ← hf.sum_eq, ← hh.sum_eq]
  automorphic ν _ :=
    (automorphicFunctionsOn (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J))
      Kinf rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)).sub_mem
      (isAutomorphicOn_pad fam rho hsmooth Kinf hf.automorphic ν)
      (isAutomorphicOn_pad fam rho hsmooth Kinf hh.automorphic ν)
  cuspidal ν _ :=
    fam.isCuspidalAlong_sub hsmooth Kinf rho J
      (isAutomorphicOn_pad fam rho hsmooth Kinf hf.automorphic ν)
      (isAutomorphicOn_pad fam rho hsmooth Kinf hh.automorphic ν)
      (isCuspidalAlong_pad fam hf.cuspidal ν) (isCuspidalAlong_pad fam hh.cuspidal ν)
  exponent ν _ :=
    fam.hasUnnormalizedExponent_sub J (hasUnnormalizedExponent_pad fam hf.exponent ν)
      (hasUnnormalizedExponent_pad fam hh.exponent ν)

end Padding

/-- The scalar test of a constant term is the sum of the tests of the components of an
exponent decomposition of its cuspidal projection. -/
theorem leviPairing_constantTerm_eq_sum_of_projection {J : StandardIndex F G fam.i fam.ν}
    {f fc : Y} {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y} {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (hproj : fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J f) fc)
    (hdec : fam.IsExponentDecomposition hsmooth Kinf rho J fc s c)
    (ht : fam.IsLeviCuspForm Kinf rho J test)
    (hdom : ∀ ν ∈ s, c ν ∈ fam.leviPairingDomain J test) :
    (fun g => fam.leviPairing J (fam.constantTerm J f) g test) =
      ∑ ν ∈ s, fun g => fam.leviPairing J (c ν) g test := by
  funext g
  rw [(hproj.2.2 test ht g).2.2, hdec.sum_eq, fam.leviPairing_finset_sum J s c hdom g,
    Finset.sum_apply]

/-- **Support of the `P`-side bracket at a continued parameter.** If every joint generalized
eigendecomposition of the bracket has vanishing components outside `S`, then the bracket,
expanded through the cuspidal projections of `C_J E` and of the constant terms of the
inducing forms, is supported in `S`. -/
theorem pBracket_isJointlySupportedIn {J Q : StandardIndex F G fam.i fam.ν}
    [IsClosedImmersion (fam.p Q).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hKQ : IsIwasawaCompact (fam.p Q) K) {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (ht : fam.IsLeviCuspForm Kinf rho J test)
    (hdom : ∀ f, fam.IsAutomorphicOn hsmooth Kinf rho J f → f ∈ fam.leviPairingDomain J test)
    {EP fc : Y} {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y}
    (hproj : fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J EP) fc)
    (hdec : fam.IsExponentDecomposition hsmooth Kinf rho J fc s c)
    {k : ℕ} (ψ : Fin k → Y) (hψ : ∀ i, fam.IsAutomorphicOn hsmooth Kinf rho Q (ψ i))
    (hψdata : J ≤ Q → ∀ i, ∃ (ψc : Y) (sψ : Finset (ComplexCharacterParameter F (fam.P J)))
      (cψ : ComplexCharacterParameter F (fam.P J) → Y),
      fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J (ψ i)) ψc ∧
        fam.IsExponentDecomposition hsmooth Kinf rho J ψc sψ cψ)
    (a : Fin k → ℂ) (mu : ComplexCharacterParameter F (fam.P Q))
    {S : Set (fam.positiveSplitComponent J → ℂ)}
    (hvan : ∀ (sv : Finset (fam.positiveSplitComponent J → ℂ)) (v : _ → Y),
      (∀ δ ∈ sv, v δ ∈ jointGenEigenspace (fam.splitComponentRepresentation J) δ) →
      ∑ δ ∈ sv, v δ = (fun g => fam.leviPairing J (fam.constantTerm J EP) g test -
        fam.leviPairing J (fam.parabolicConstantTerm Q J
          (hKQ.parameterTwist (∑ i, a i • ψ i) mu)) g test) →
      ∀ δ ∈ sv, δ ∉ S → v δ = 0) :
    IsJointlySupportedIn (fam.splitComponentRepresentation J) S
      (fun g => fam.leviPairing J (fam.constantTerm J EP) g test -
        fam.leviPairing J (fam.parabolicConstantTerm Q J
          (hKQ.parameterTwist (∑ i, a i • ψ i) mu)) g test) := by
  classical
  let χ (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) : ℂ :=
    parameterPower F (fam.P J) ν b.val
  have hP := fam.leviPairing_constantTerm_eq_sum_of_projection rho hsmooth Kinf hproj hdec ht
    (fun ν hν => hdom _ (hdec.automorphic ν hν))
  have hPmem : ∀ ν ∈ s, (fun g => fam.leviPairing J (c ν) g test) ∈
      jointGenEigenspace (fam.splitComponentRepresentation J) (χ ν) := fun ν hν =>
    fam.leviPairing_mem_jointGenEigenspace J (hdom _ (hdec.automorphic ν hν)) (hdec.exponent ν hν)
  by_cases hJQ : J ≤ Q
  · choose ψc sψ cψ hψp hψd using hψdata hJQ
    have hint : J ≤ Q → ∀ i, fam.constantTerm J (ψ i) ∈ fam.leviPairingDomain J test :=
      fun _ i g => ((hψp i).2.2 test ht g).1
    have href : (fun g => fam.leviPairing J (fam.parabolicConstantTerm Q J
        (hKQ.parameterTwist (∑ i, a i • ψ i) mu)) g test) =
        ∑ x ∈ Finset.univ.sigma sψ, a x.1 • (fun g => fam.leviPairing J
          (hKQ.parameterTwist (cψ x.1 x.2) mu) g test) := by
      funext g
      rw [fam.leviPairing_parabolicConstantTerm_twist_sum_smul Q J rho hsmooth Kinf hKQ mu ψ hψ a
        test hint g, Finset.sum_apply, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hψt := congrFun (fam.leviPairing_constantTerm_eq_sum_of_projection rho hsmooth Kinf
        (hψp i) (hψd i) ht (fun ν hν => hdom _ ((hψd i).automorphic ν hν))) g
      simp only [Finset.sum_apply] at hψt
      simp only [parabolicConstantTerm, hJQ, ↓reduceIte,
        fam.leviPairing_constantTerm_parameterTwist Q J hKQ hJQ, hψt, Finset.sum_mul,
        Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [fam.leviPairing_parameterTwist_of_le hJQ hKQ]
    refine isJointlySupportedIn_of_fiberVanishing_sub _ hvan s (Finset.univ.sigma sψ)
      (fun ν => fun g => fam.leviPairing J (c ν) g test)
      (fun x => a x.1 • fun g => fam.leviPairing J (hKQ.parameterTwist (cψ x.1 x.2) mu) g test)
      χ (fun x => χ (x.2 + parameterRestrict (fam.nestedParabolicHom hJQ) mu)) hPmem ?_ ?_
    · intro x hx
      obtain ⟨-, hν⟩ := Finset.mem_sigma.mp hx
      refine Submodule.smul_mem _ _ ?_
      exact fam.leviPairing_mem_jointGenEigenspace J
        (fam.parameterTwist_mem_leviPairingDomain hJQ hKQ mu
          (hdom _ ((hψd x.1).automorphic x.2 hν)))
        (fam.hasUnnormalizedExponent_parameterTwist_of_le hJQ hKQ mu ((hψd x.1).exponent x.2 hν))
    · rw [← href, ← hP]
      rfl
  · have hzero : (fun g => fam.leviPairing J (fam.parabolicConstantTerm Q J
        (hKQ.parameterTwist (∑ i, a i • ψ i) mu)) g test) = 0 := by
      funext g
      simp only [parabolicConstantTerm, hJQ, ↓reduceIte, Pi.zero_apply]
      exact congrFun (map_zero (fam.leviPairingLinear J test)) g
    refine isJointlySupportedIn_of_fiberVanishing _ hvan s
      (fun ν => fun g => fam.leviPairing J (c ν) g test) χ hPmem ?_
    rw [← hP]
    funext g
    have := congrFun hzero g
    simp only [Pi.zero_apply] at this
    simp only [this, sub_zero]

/-- **Expansion at one far parameter.** Two global automorphic forms whose cuspidal
projections along `J` have exponent decompositions, and whose tested constant terms differ
from a common reference by terms supported in `ΛP`, respectively `ΛQ`, have cuspidal
projections differing by components with exponents in `ΛP ∪ ΛQ`. -/
theorem exists_expansion_of_supported {J : StandardIndex F G fam.i fam.ν}
    (hdetect : ∀ f, fam.IsAutomorphicOn hsmooth Kinf rho J f → fam.IsCuspidalAlong J f →
      (∀ test, fam.IsLeviCuspForm Kinf rho J test → ∀ g, fam.leviPairing J f g test = 0) →
      f = 0)
    (hdom : ∀ f, fam.IsAutomorphicOn hsmooth Kinf rho J f →
      ∀ test, fam.IsLeviCuspForm Kinf rho J test → f ∈ fam.leviPairingDomain J test)
    {EP EQ left right : Y} (hl : fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J EP) left)
    (hr : fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J EQ) right)
    {s t : Finset (ComplexCharacterParameter F (fam.P J))}
    {c e : ComplexCharacterParameter F (fam.P J) → Y}
    (hdl : fam.IsExponentDecomposition hsmooth Kinf rho J left s c)
    (hdr : fam.IsExponentDecomposition hsmooth Kinf rho J right t e)
    (ref : (AdelicGroupPoints F (fam.M J) → ℂ) → Y)
    (ΛP ΛQ : Set (ComplexCharacterParameter F (fam.P J)))
    (hPsupp : ∀ test, fam.IsLeviCuspForm Kinf rho J test →
      IsJointlySupportedIn (fam.splitComponentRepresentation J)
        ((fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
          parameterPower F (fam.P J) ν b.val) '' ΛP)
        (fun g => fam.leviPairing J (fam.constantTerm J EP) g test - ref test g))
    (hQsupp : ∀ test, fam.IsLeviCuspForm Kinf rho J test →
      IsJointlySupportedIn (fam.splitComponentRepresentation J)
        ((fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
          parameterPower F (fam.P J) ν b.val) '' ΛQ)
        (fun g => fam.leviPairing J (fam.constantTerm J EQ) g test - ref test g))
    (Good : ComplexCharacterParameter F (fam.P J) → Prop) (hgood : ∀ ν ∈ ΛP ∪ ΛQ, Good ν) :
    ∃ (u : Finset (ComplexCharacterParameter F (fam.P J)))
      (b : ComplexCharacterParameter F (fam.P J) → Y),
      left = right + ∑ ν ∈ u, b ν ∧
        ∀ ν ∈ u, fam.HasUnnormalizedExponent J ν (b ν) ∧ Good ν := by
  classical
  have hdec := fam.isExponentDecomposition_sub rho hsmooth Kinf hdl hdr
  set c' : ComplexCharacterParameter F (fam.P J) → Y :=
    fun ν => (if ν ∈ s then c ν else 0) - (if ν ∈ t then e ν else 0) with hc'
  have hsum : ∀ test, fam.IsLeviCuspForm Kinf rho J test →
      IsJointlySupportedIn (fam.splitComponentRepresentation J)
        ((fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
          parameterPower F (fam.P J) ν b.val) '' (ΛP ∪ ΛQ))
        (fun g => fam.leviPairing J (left - right) g test) := by
    intro test ht
    have heq : (fun g => fam.leviPairing J (left - right) g test) =
        (fun g => fam.leviPairing J (fam.constantTerm J EP) g test - ref test g) -
          (fun g => fam.leviPairing J (fam.constantTerm J EQ) g test - ref test g) := by
      funext g
      have hlin := congrFun (map_sub (fam.leviPairingLinear J test)
        ⟨left, fun g => (hl.2.2 test ht g).2.1⟩ ⟨right, fun g => (hr.2.2 test ht g).2.1⟩) g
      change fam.leviPairing J (left - right) g test =
        fam.leviPairing J left g test - fam.leviPairing J right g test at hlin
      rw [hlin, ← (hl.2.2 test ht g).2.2, ← (hr.2.2 test ht g).2.2]
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact ((hPsupp test ht).mono (image_mono subset_union_left)).sub
      ((hQsupp test ht).mono (image_mono subset_union_right))
  have hz := fam.exponentDecomposition_eq_zero_of_tests J rho hsmooth Kinf hdetect
    (fun f hf test ht => hdom f hf test ht) hdec (ΛP ∪ ΛQ) hsum
  refine ⟨(s ∪ t).filter (· ∈ ΛP ∪ ΛQ), c', ?_, fun ν hν => ?_⟩
  · have hfilt : ∑ ν ∈ (s ∪ t).filter (· ∈ ΛP ∪ ΛQ), c' ν = ∑ ν ∈ s ∪ t, c' ν := by
      refine Finset.sum_filter_of_ne fun ν hν hne => ?_
      by_contra hΛ
      exact hne (hz ν hν hΛ)
    rw [hfilt, ← hdec.sum_eq]
    abel
  · obtain ⟨hνst, hΛ⟩ := Finset.mem_filter.mp hν
    exact ⟨hdec.exponent ν hνst, hgood ν hΛ⟩

end Langlands.Global.StandardParabolicFamily

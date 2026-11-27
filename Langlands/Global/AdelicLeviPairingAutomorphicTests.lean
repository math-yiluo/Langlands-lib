import Langlands.Global.AdelicLeviConstantTermPairing
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicCuspidalProjectionDecompositionStatement
import Langlands.Global.AdelicEisensteinPositiveParametersProof
import Langlands.Global.AdelicJointExponentSupport

/-! # Norm-one Levi tests of automorphic functions on a standard parabolic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Y" => (AdelicGroupPoints F G → ℂ)
local notation "ι" => AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)
local notation "Γ" => rationalNormOneSubgroup F (fam.M J)
local notation "μJ" => normOneRationalQuotientHaarMeasure F (fam.M J)

/-- For a function invariant under the rational Levi and a rationally invariant test,
the pairing integrand can be evaluated at any representative of a norm-one class. -/
theorem leviPairingIntegrand_eq_of_mk {f : Y}
    (hf : ∀ x ∈ rationalImage F (fam.l J ≫ fam.p J), ∀ g, f (x * g) = f g)
    {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (htest : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) test)
    (g : AdelicGroupPoints F G) {q : NormOneRationalQuotient F (fam.M J)}
    {x : normOneSubgroup F (fam.M J)} (hx : LeftCosetSpace.mk Γ x = q) :
    fam.leviPairingIntegrand J f g test q = f (ι x.val * g) * starRingEnd ℂ (test x.val) := by
  let b (y : normOneSubgroup F (fam.M J)) := f (ι y.val * g) * starRingEnd ℂ (test y.val)
  have hb (a : Γ) (y : normOneSubgroup F (fam.M J)) : b (a.val * y) = b y := by
    obtain ⟨r, hr⟩ := a.property
    have hr' : rational F (fam.M J) r = a.val.val := congrArg Subtype.val hr
    have hmem : ι (rational F (fam.M J) r) ∈ rationalImage F (fam.l J ≫ fam.p J) := ⟨r, rfl⟩
    change f (ι (a.val.val * y.val) * g) * starRingEnd ℂ (test (a.val.val * y.val)) = _
    rw [map_mul, mul_assoc, ← hr', hf _ hmem, htest (rational F (fam.M J) r) ⟨r, rfl⟩ y.val]
  let B := LeftCosetSpace.lift Γ b hb
  change b (Quotient.out q) = b x
  calc
    b (Quotient.out q) = B q := congrArg B (Quotient.out_eq q)
    _ = b x := congrArg B hx.symm

variable {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

/-- Functions automorphic on `U_J(𝔸) M_J(F) \ G(𝔸)` are invariant under the rational Levi. -/
theorem leviRational_invariant_of_isAutomorphicOn {f : Y}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho J f) :
    ∀ x ∈ rationalImage F (fam.l J ≫ fam.p J), ∀ g, f (x * g) = f g :=
  fun x hx g => hf.1 x (Subgroup.mem_sup_right hx) g

/-- A continuous function of moderate growth that is invariant under the rational Levi has
absolutely convergent norm-one Levi pairings against a continuous rationally invariant test
that admits integrable weighted majorants at every growth exponent. -/
theorem mem_leviPairingDomain_of_moderateGrowth {f : Y}
    (hinv : ∀ x ∈ rationalImage F (fam.l J ≫ fam.p J), ∀ g, f (x * g) = f g)
    (hfc : Continuous f) (hgrowth : HasModerateGrowthFunction F G rho f)
    {test : AdelicGroupPoints F (fam.M J) → ℂ} (htc : Continuous test)
    (hti : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) test)
    (hmaj : ∀ g (R : ℝ), fam.HasLeviPairingMajorant J test g rho R) :
    f ∈ fam.leviPairingDomain J test := by
  intro g
  obtain ⟨C, hC, r, hgrowth⟩ := hgrowth
  obtain ⟨b, hb, hdom⟩ := hmaj g r
  have hcont : Continuous (fam.leviPairingIntegrand J f g test) := by
    rw [LeftCosetSpace.continuous_iff Γ]
    have heq : fam.leviPairingIntegrand J f g test ∘ LeftCosetSpace.mk Γ =
        fun x : normOneSubgroup F (fam.M J) => f (ι x.val * g) * starRingEnd ℂ (test x.val) :=
      funext fun _ => fam.leviPairingIntegrand_eq_of_mk J hinv hti g rfl
    rw [heq]
    exact (hfc.comp (((ι).continuous.comp continuous_subtype_val).mul_const g)).mul
      (htc.comp continuous_subtype_val).star
  refine (hb.const_mul C).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [hdom] with q hq
  obtain ⟨x, hx, hxb⟩ := hq
  rw [fam.leviPairingIntegrand_eq_of_mk J hinv hti g hx, norm_mul, Complex.norm_conj]
  calc
    ‖f (ι x.val * g)‖ * ‖test x.val‖ ≤
        (C * RepresentationGrowth.adelicSourceNorm F G rho (ι x.val * g) ^ r) * ‖test x.val‖ :=
      mul_le_mul_of_nonneg_right (hgrowth _) (norm_nonneg _)
    _ = C * (RepresentationGrowth.adelicSourceNorm F G rho (ι x.val * g) ^ r * ‖test x.val‖) :=
      mul_assoc _ _ _
    _ ≤ C * b q := mul_le_mul_of_nonneg_left hxb hC.le

/-- An automorphic function on a standard parabolic quotient has absolutely convergent
norm-one Levi pairings against a continuous rationally invariant test that admits
integrable weighted majorants at every growth exponent. -/
theorem mem_leviPairingDomain_of_isAutomorphicOn_of_majorant {f : Y}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho J f) {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (htc : Continuous test)
    (hti : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) test)
    (hmaj : ∀ g (R : ℝ), fam.HasLeviPairingMajorant J test g rho R) :
    f ∈ fam.leviPairingDomain J test :=
  fam.mem_leviPairingDomain_of_moderateGrowth J rho
    (fam.leviRational_invariant_of_isAutomorphicOn J rho hsmooth Kinf hf) hf.2.1.1 hf.2.2.2.2
    htc hti hmaj

local instance leviTestSplitCommGroup : CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.2 b.2)

/-- The scalar test function `g ↦ (f(· g), test)` of a function with an unnormalized
exponent lies in the corresponding joint generalized eigenspace. -/
theorem leviPairing_mem_jointGenEigenspace {f : Y} {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (hf : f ∈ fam.leviPairingDomain J test) {lam : ComplexCharacterParameter F (fam.P J)}
    (hexp : fam.HasUnnormalizedExponent J lam f) :
    (fun g => fam.leviPairing J f g test) ∈ jointGenEigenspace (fam.splitComponentRepresentation J)
      (fun b : fam.positiveSplitComponent J => parameterPower F (fam.P J) lam b.val) :=
  fam.leviPairingLinear_mem_jointGenEigenspace J test ⟨f, hf⟩
    (fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J hexp)

/-- Pairing against a fixed test distributes over a finite sum of functions in the
pairing domain. -/
theorem leviPairing_finset_sum {κ : Type*} (t : Finset κ) {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (f : κ → Y) (hf : ∀ i ∈ t, f i ∈ fam.leviPairingDomain J test) (g : AdelicGroupPoints F G) :
    fam.leviPairing J (∑ i ∈ t, f i) g test = ∑ i ∈ t, fam.leviPairing J (f i) g test := by
  have hsum : fam.leviPairingIntegrand J (∑ i ∈ t, f i) g test =
      ∑ i ∈ t, fam.leviPairingIntegrand J (f i) g test := by
    funext q
    simp only [leviPairingIntegrand, Finset.sum_apply, Finset.sum_mul]
  unfold leviPairing
  rw [hsum]
  simp only [Finset.sum_apply]
  exact integral_finsetSum t fun i hi => hf i hi g

/-- A cuspidal automorphic function on a standard parabolic quotient whose norm-one
Levi pairings against all Levi cusp forms vanish is zero. Both the function and zero
are cuspidal projections of its constant term, which is the function itself. -/
theorem eq_zero_of_leviPairings_eq_zero (hProj : CuspidalProjectionDecompositionStatement.{u})
    {K : Subgroup (AdelicGroupPoints F G)} (hKmax : IsMaximalCompactSubgroup F G K)
    (hK0 : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J')
      (K.comap (map F (fam.M J') G (fam.l J' ≫ fam.p J')).toMonoidHom))
    (hrho : IsClosedSubgroup rho) {f : Y}
    (hf : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J f)
    (hcusp : fam.IsCuspidalAlong J f)
    (hint : ∀ test, fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
      f ∈ fam.leviPairingDomain J test)
    (hzero : ∀ test, fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
      ∀ g, fam.leviPairing J f g test = 0) : f = 0 := by
  obtain ⟨ψ, -, huniq, -⟩ := hProj F G fam K hKmax hK0 hKlevi rho hsmooth hrho J J le_rfl f hf
  have hself := fam.constantTerm_eq_self_of_automorphicOn J hf
  have hz (test : AdelicGroupPoints F (fam.M J) → ℂ) (g : AdelicGroupPoints F G) :
      fam.leviPairingIntegrand J 0 g test = 0 := by
    funext q
    simp only [leviPairingIntegrand, Pi.zero_apply, zero_mul]
  have h1 : fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      (fam.constantTerm J f) f := by
    rw [hself]
    exact ⟨hf, hcusp, fun test ht g => ⟨hint test ht g, hint test ht g, rfl⟩⟩
  have h0 : fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      (fam.constantTerm J f) 0 := by
    rw [hself]
    refine ⟨fam.isAutomorphicOn_zero hsmooth _ rho J, fam.isCuspidalAlong_zero J,
      fun test ht g => ⟨hint test ht g, ?_, ?_⟩⟩
    · rw [hz test g]
      exact integrable_zero _ _ _
    · rw [hzero test ht g]
      unfold leviPairing
      rw [hz test g]
      simp
  exact (huniq f h1).trans (huniq 0 h0).symm

/-- The characters `b ↦ b^λ` of the positive split component determine `λ`. -/
theorem injective_splitComponentCharacter :
    Function.Injective (fun (ν : ComplexCharacterParameter F (fam.P J))
      (b : fam.positiveSplitComponent J) => parameterPower F (fam.P J) ν b.val) :=
  (eisensteinPositiveParameters F G (fam.P J) (fam.M J) (fam.A J) (fam.p J) (fam.l J)
    (fam.a J) ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩).2

/-- Exponent filtering: in an exponent decomposition of a cuspidal automorphic function,
a component vanishes when its exponent lies outside a set `Λ` such that every scalar test
of the function is a finite sum of joint generalized eigenvectors with exponents in `Λ`. -/
theorem exponentDecomposition_eq_zero_of_tests
    (hdetect : ∀ f, fam.IsAutomorphicOn hsmooth Kinf rho J f → fam.IsCuspidalAlong J f →
      (∀ test, fam.IsLeviCuspForm Kinf rho J test → ∀ g, fam.leviPairing J f g test = 0) →
      f = 0)
    (hdom : ∀ f, fam.IsAutomorphicOn hsmooth Kinf rho J f →
      ∀ test, fam.IsLeviCuspForm Kinf rho J test → f ∈ fam.leviPairingDomain J test)
    {h : Y} {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y}
    (hdec : fam.IsExponentDecomposition hsmooth Kinf rho J h s c)
    (Λ : Set (ComplexCharacterParameter F (fam.P J)))
    (hsum : ∀ test, fam.IsLeviCuspForm Kinf rho J test →
      IsJointlySupportedIn (fam.splitComponentRepresentation J)
        ((fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
          parameterPower F (fam.P J) ν b.val) '' Λ)
        (fun g => fam.leviPairing J h g test)) :
    ∀ lam ∈ s, lam ∉ Λ → c lam = 0 := by
  classical
  intro lam hlam hne
  apply hdetect (c lam) (hdec.automorphic lam hlam) (hdec.cuspidal lam hlam)
  intro test ht
  let χ (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) : ℂ :=
    parameterPower F (fam.P J) ν b.val
  have hχ : Function.Injective χ := fam.injective_splitComponentCharacter J
  let T (ν : ComplexCharacterParameter F (fam.P J)) : Y := fun g => fam.leviPairing J (c ν) g test
  have hT (ν) (hν : ν ∈ s) : T ν ∈ jointGenEigenspace (fam.splitComponentRepresentation J) (χ ν) :=
    fam.leviPairing_mem_jointGenEigenspace J (hdom _ (hdec.automorphic ν hν) test ht)
      (hdec.exponent ν hν)
  have htot : (fun g => fam.leviPairing J h g test) = ∑ ν ∈ s, T ν := by
    funext g
    rw [hdec.sum_eq, fam.leviPairing_finset_sum J s c
      (fun ν hν => hdom _ (hdec.automorphic ν hν) test ht) g]
    simp only [Finset.sum_apply, T]
  have hS := hsum test ht
  rw [htot] at hS
  have hχΛ : χ lam ∉ χ '' Λ := by
    rintro ⟨ν, hν, hνl⟩
    exact hne (hχ hνl ▸ hν)
  have hfib := fiber_sum_eq_zero_of_isJointlySupportedIn _ s T χ hT hS hχΛ
  have hfilter : s.filter (fun ν => χ ν = χ lam) = {lam} := by
    ext ν
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hχ h.2, fun h => by subst h; exact ⟨hlam, rfl⟩⟩
  rw [hfilter, Finset.sum_singleton] at hfib
  intro g
  simpa only [T, Pi.zero_apply] using congrFun hfib g

end Langlands.Global.StandardParabolicFamily

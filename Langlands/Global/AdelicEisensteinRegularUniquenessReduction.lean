import Langlands.Global.AdelicEisensteinRegularUniquenessStatement
import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionStatement
import Langlands.Global.AdelicEisensteinRegularAutomorphyStatement
import Langlands.Global.AdelicLeadingCuspidalInjectivityStatement
import Langlands.Global.AdelicCuspidalProjectionDecompositionStatement
import Langlands.Global.AdelicParameterTwistAutomorphyStatement
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicStandardTopAutomorphy
import Langlands.Global.AdelicEisensteinWeylSeparation
import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicEisensteinPositiveParametersProof
import Langlands.GroupScheme.Rational.LanglandsInvariantForm

/-! # Uniqueness of convergent Eisenstein series from five premises -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj BigOperators TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν
local notation "Y" => (AdelicGroupPoints F G → ℂ)

/-! ### Levi pairings of finite sums and differences -/

section Pairing

variable (J : StandardIndex F G fam.i fam.ν)

/-- The Levi pairing integrand is additive in the function. -/
theorem leviPairingIntegrand_add_fun (f h : Y) (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingIntegrand J (f + h) g test =
      fam.leviPairingIntegrand J f g test + fam.leviPairingIntegrand J h g test := by
  funext q
  simp only [leviPairingIntegrand, Pi.add_apply, add_mul]

/-- The Levi pairing integrand is subtractive in the function. -/
theorem leviPairingIntegrand_sub_fun (f h : Y) (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingIntegrand J (f - h) g test =
      fam.leviPairingIntegrand J f g test - fam.leviPairingIntegrand J h g test := by
  funext q
  simp only [leviPairingIntegrand, Pi.sub_apply, sub_mul]

/-- The Levi pairing integrand of a finite sum is the sum of the integrands. -/
theorem leviPairingIntegrand_sum_fun {Ix : Type*} (s : Finset Ix) (f : Ix → Y)
    (g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingIntegrand J (∑ i ∈ s, f i) g test =
      ∑ i ∈ s, fam.leviPairingIntegrand J (f i) g test := by
  funext q
  simp only [leviPairingIntegrand, Finset.sum_apply, Finset.sum_mul]

/-- Levi pairings add for absolutely convergent integrands. -/
theorem leviPairing_add_of_integrable {f h : Y} {g : AdelicGroupPoints F G}
    {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (hf : Integrable (fam.leviPairingIntegrand J f g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J)))
    (hh : Integrable (fam.leviPairingIntegrand J h g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J))) :
    fam.leviPairing J (f + h) g test = fam.leviPairing J f g test + fam.leviPairing J h g test := by
  unfold leviPairing
  rw [fam.leviPairingIntegrand_add_fun J]
  exact integral_add hf hh

/-- Levi pairings subtract for absolutely convergent integrands. -/
theorem leviPairing_sub_of_integrable {f h : Y} {g : AdelicGroupPoints F G}
    {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (hf : Integrable (fam.leviPairingIntegrand J f g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J)))
    (hh : Integrable (fam.leviPairingIntegrand J h g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J))) :
    fam.leviPairing J (f - h) g test = fam.leviPairing J f g test - fam.leviPairing J h g test := by
  unfold leviPairing
  rw [fam.leviPairingIntegrand_sub_fun J]
  exact integral_sub hf hh

/-- The Levi pairing of a finite sum with absolutely convergent integrands is the sum of the
pairings. -/
theorem leviPairing_sum_of_integrable {Ix : Type*} (s : Finset Ix) (f : Ix → Y)
    {g : AdelicGroupPoints F G}
    {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (hf : ∀ i ∈ s, Integrable (fam.leviPairingIntegrand J (f i) g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J))) :
    fam.leviPairing J (∑ i ∈ s, f i) g test = ∑ i ∈ s, fam.leviPairing J (f i) g test := by
  unfold leviPairing
  rw [fam.leviPairingIntegrand_sum_fun J]
  simpa only [Finset.sum_apply] using integral_finsetSum s hf

end Pairing

/-! ### Sums of cuspidal projections -/

section Projection

variable {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

/-- Automorphy on a standard parabolic quotient is closed under addition. -/
theorem isAutomorphicOn_add_of_isAutomorphicOn (P : Index) {f h : Y}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho P f)
    (hh : fam.IsAutomorphicOn hsmooth Kinf rho P h) :
    fam.IsAutomorphicOn hsmooth Kinf rho P (f + h) :=
  (automorphicFunctionsOn (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P))
    Kinf rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)).add_mem hf hh

/-- Automorphy on a standard parabolic quotient is closed under subtraction. -/
theorem isAutomorphicOn_sub_of_isAutomorphicOn (P : Index) {f h : Y}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho P f)
    (hh : fam.IsAutomorphicOn hsmooth Kinf rho P h) :
    fam.IsAutomorphicOn hsmooth Kinf rho P (f - h) :=
  (automorphicFunctionsOn (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P))
    Kinf rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)).sub_mem hf hh

/-- The sum of two cuspidal automorphic functions on a standard parabolic quotient is cuspidal. -/
theorem isCuspidalAlong_add_of_isAutomorphicOn (P : Index) {f h : Y}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho P f)
    (hh : fam.IsAutomorphicOn hsmooth Kinf rho P h)
    (hfC : fam.IsCuspidalAlong P f) (hhC : fam.IsCuspidalAlong P h) :
    fam.IsCuspidalAlong P (f + h) := by
  intro Q hQ
  let L := fam.constantTermLinear P Q hsmooth Kinf rho hQ.le
  calc
    fam.constantTerm Q (f + h) = L (⟨f, hf⟩ + ⟨h, hh⟩) := rfl
    _ = L ⟨f, hf⟩ + L ⟨h, hh⟩ := map_add _ _ _
    _ = 0 := by
      change fam.constantTerm Q f + fam.constantTerm Q h = 0
      rw [hfC Q hQ, hhC Q hQ, add_zero]

/-- Cuspidal projections add: a projection of `f` plus a projection of `h` is a projection of
`f + h`. -/
theorem isCuspidalProjection_add (P : Index) {f h fc hc : Y}
    (hf : fam.IsCuspidalProjection hsmooth Kinf rho P f fc)
    (hh : fam.IsCuspidalProjection hsmooth Kinf rho P h hc) :
    fam.IsCuspidalProjection hsmooth Kinf rho P (f + h) (fc + hc) := by
  refine ⟨fam.isAutomorphicOn_add_of_isAutomorphicOn hsmooth Kinf rho P hf.1 hh.1,
    fam.isCuspidalAlong_add_of_isAutomorphicOn hsmooth Kinf rho P hf.1 hh.1 hf.2.1 hh.2.1, ?_⟩
  intro ψ hψ g
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf.2.2 ψ hψ g
  obtain ⟨hh₁, hh₂, hh₃⟩ := hh.2.2 ψ hψ g
  refine ⟨?_, ?_, ?_⟩
  · rw [fam.leviPairingIntegrand_add_fun P]
    exact hf₁.add hh₁
  · rw [fam.leviPairingIntegrand_add_fun P]
    exact hf₂.add hh₂
  · rw [fam.leviPairing_add_of_integrable P hf₁ hh₁, fam.leviPairing_add_of_integrable P hf₂ hh₂,
      hf₃, hh₃]

/-- Zero is a cuspidal projection of zero. -/
theorem isCuspidalProjection_zero (P : Index) :
    fam.IsCuspidalProjection hsmooth Kinf rho P 0 0 := by
  refine ⟨fam.isAutomorphicOn_zero hsmooth Kinf rho P, fam.isCuspidalAlong_zero P, ?_⟩
  intro ψ _ g
  have hz : fam.leviPairingIntegrand P 0 g ψ = 0 := by
    funext q
    simp [leviPairingIntegrand]
  exact ⟨hz ▸ integrable_zero _ _ _, hz ▸ integrable_zero _ _ _, rfl⟩

end Projection

/-! ### Localization of exponents in a cusp test -/

section Localization

variable (J : StandardIndex F G fam.i fam.ν)

attribute [local instance] positiveSplitComponentCommGroup

/-- **Localization of exponents in a cusp test.** Let finitely many functions `d μ` (`μ ∈ t`)
with unnormalized exponents `μ`, and finitely many terms with unnormalized exponents `lab k`,
have absolutely convergent pairings with `test`, and suppose that at every point the pairings of
the `d μ` add up to those of the terms. Then every `d μ` whose exponent is none of the `lab k`
has vanishing pairings with `test`. -/
theorem leviPairing_eq_zero_of_sum_leviPairing_eq (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (t : Finset (ComplexCharacterParameter F (fam.P J)))
    (d : ComplexCharacterParameter F (fam.P J) → Y)
    (hd : ∀ mu ∈ t, d mu ∈ fam.leviPairingDomain J test ∧
      fam.HasUnnormalizedExponent J mu (d mu))
    {m : ℕ} (lab : Fin m → ComplexCharacterParameter F (fam.P J)) (terms : Fin m → Y)
    (hterms : ∀ k, terms k ∈ fam.leviPairingDomain J test ∧
      fam.HasUnnormalizedExponent J (lab k) (terms k))
    (hsum : ∀ g, ∑ mu ∈ t, fam.leviPairing J (d mu) g test =
      ∑ k, fam.leviPairing J (terms k) g test)
    {mu : ComplexCharacterParameter F (fam.P J)} (hmu : mu ∈ t) (hne : ∀ k, mu ≠ lab k)
    (g : AdelicGroupPoints F G) :
    fam.leviPairing J (d mu) g test = 0 := by
  classical
  let L := fam.leviPairingLinear J test
  let E : ComplexCharacterParameter F (fam.P J) → Submodule ℂ Y := fun nu =>
    jointGenEigenspace (fam.splitComponentRepresentation J)
      (fun b : fam.positiveSplitComponent J => parameterPower F (fam.P J) nu b.val)
  let p : ComplexCharacterParameter F (fam.P J) → Y := fun nu =>
    if h : nu ∈ t then L ⟨d nu, (hd nu h).1⟩ else 0
  let q : Fin m → Y := fun k => L ⟨terms k, (hterms k).1⟩
  have hp : ∀ nu, p nu ∈ E nu := by
    intro nu
    by_cases h : nu ∈ t
    · simp only [p, dite_eq_left h]
      exact fam.leviPairingLinear_mem_jointGenEigenspace J test _
        (fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hd nu h).2)
    · simp only [p, dite_eq_right h]
      exact (E nu).zero_mem
  have hq : ∀ k, q k ∈ E (lab k) := fun k =>
    fam.leviPairingLinear_mem_jointGenEigenspace J test _
      (fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hterms k).2)
  let support := t ∪ Finset.univ.image lab
  let x : ComplexCharacterParameter F (fam.P J) → Y := fun nu =>
    p nu - ∑ k ∈ Finset.univ.filter (fun k => lab k = nu), q k
  have hx : ∀ nu ∈ support, x nu ∈ E nu := by
    intro nu _
    refine (E nu).sub_mem (hp nu) ((E nu).sum_mem fun k hk => ?_)
    rw [← (Finset.mem_filter.mp hk).2]
    exact hq k
  have hp_sum : ∑ nu ∈ support, p nu = ∑ nu ∈ t, p nu := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro nu _ hnt
    simp only [p, dite_eq_right hnt]
  have hq_sum : ∑ nu ∈ support, ∑ k ∈ Finset.univ.filter (fun k => lab k = nu), q k =
      ∑ k, q k :=
    Finset.sum_fiberwise_of_maps_to (fun k _ =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem lab (Finset.mem_univ k))) q
  have hxsum : ∑ nu ∈ support, x nu = 0 := by
    simp only [x, Finset.sum_sub_distrib, hp_sum, hq_sum, sub_eq_zero]
    funext g'
    simp only [Finset.sum_apply]
    calc ∑ nu ∈ t, p nu g' = ∑ nu ∈ t, fam.leviPairing J (d nu) g' test :=
          Finset.sum_congr rfl fun nu hnu => by simp only [p, dite_eq_left hnu]; rfl
      _ = ∑ k, fam.leviPairing J (terms k) g' test := hsum g'
      _ = ∑ k, q k g' := rfl
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    (fam.iSupIndep_unnormalizedCharacterEigenspace J) support x hx hxsum mu
      (Finset.mem_union_left _ hmu)
  have hempty : Finset.univ.filter (fun k => lab k = mu) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k _ hk
    exact hne k hk.symm
  simp only [x, hempty, Finset.sum_empty, sub_zero, p, dite_eq_left hmu] at hzero
  exact congrFun hzero g

end Localization

/-! ### Detection by cusp tests, from the cuspidal projection statement -/

section Detection

variable (hproj : CuspidalProjectionDecompositionStatement.{u})
  (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
  (hKmin : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
  (hKlevi : ∀ J : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J)
    (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hrho : IsClosedSubgroup rho)

include hproj hKmax hKmin hKlevi hrho in
/-- An automorphic function on `U_J(𝔸) M_J(F) \ G(𝔸)` has absolutely convergent pairings with
every Levi cusp form at every point. -/
theorem integrable_leviPairingIntegrand_of_isAutomorphicOn (J : Index) {f : Y}
    (hf : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J f)
    {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (htest : fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test)
    (g : AdelicGroupPoints F G) :
    Integrable (fam.leviPairingIntegrand J f g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J)) := by
  obtain ⟨ψ, hψ, -, -⟩ := hproj F G fam K hKmax hKmin hKlevi rho hsmooth hrho J J le_rfl f hf
  have h := (hψ.2.2 test htest g).1
  rwa [fam.constantTerm_eq_self_of_automorphicOn J hf] at h

include hproj hKmax hKmin hKlevi hrho in
/-- A cuspidal automorphic function on `U_J(𝔸) M_J(F) \ G(𝔸)` whose pairings with all Levi cusp
forms vanish is zero: it and `0` are both cuspidal projections of its own constant term. -/
theorem eq_zero_of_isCuspidalAlong_of_forall_leviPairing_eq_zero (J : Index) {f : Y}
    (hf : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J f)
    (hfC : fam.IsCuspidalAlong J f)
    (hz : ∀ test : AdelicGroupPoints F (fam.M J) → ℂ,
      fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
        ∀ g, fam.leviPairing J f g test = 0) :
    f = 0 := by
  obtain ⟨ψ, hψ, huniq, -⟩ := hproj F G fam K hKmax hKmin hKlevi rho hsmooth hrho J J le_rfl f hf
  have hct := fam.constantTerm_eq_self_of_automorphicOn J hf
  rw [hct] at hψ huniq
  have hzero : ∀ (test : AdelicGroupPoints F (fam.M J) → ℂ) (g : AdelicGroupPoints F G),
      fam.leviPairingIntegrand J 0 g test = 0 := by
    intro test g
    funext q
    simp [leviPairingIntegrand]
  have h₁ : f = ψ := huniq f ⟨hf, hfC, fun test htest g =>
    ⟨(hψ.2.2 test htest g).1, (hψ.2.2 test htest g).1, rfl⟩⟩
  have h₀ : (0 : Y) = ψ := huniq 0 ⟨fam.isAutomorphicOn_zero hsmooth _ rho J,
    fam.isCuspidalAlong_zero J, fun test htest g =>
      ⟨(hψ.2.2 test htest g).1, (hzero test g).symm ▸ integrable_zero _ _ _, by
        rw [hz test htest g]
        unfold leviPairing
        rw [hzero test g]
        simp⟩⟩
  rw [h₁, ← h₀]

end Detection

/-! ### Competing labels are not leading at regular parameters -/

section Nonleading

open Langlands.Plancherel RealTorusSpace Langlands.Aubert.General.RationalPointFamily

/-- For a finite set of shifts, at sufficiently regular parameters of the inducing parabolic
`P_I`, no exponent whose real part is a shifted nonidentity Weyl translate of `Re λ`, for a Weyl
element keeping the simple roots of `I` positive, is leading. This is the identity-Weyl case of
`EisensteinNonleadingWeylTermsStatement`, proved from the ambient chamber separation. -/
theorem exists_regular_forall_not_isLeadingExponent (I : Index)
    [Fintype (relativeWeylGroup fam.i)] [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (S : Set (Vstar fam.T)) (hS : S.Finite) :
    let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
      ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
    let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
    let hT := fam.maximalSplit.isSplitSubtorus.1
    ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
      ∀ w : relativeWeylGroup fam.i, w ≠ 1 →
        (∀ α ∈ I.val, schemeWeylCharacterAction fam.i w α ∈
          positiveRelativeRoots fam.i fam.ν) →
        ∀ (J : Index) (exponent : ComplexCharacterParameter F (fam.P J)), ∀ shift ∈ S,
          fam.chamberEmbedding J (parameterRealPart F (fam.P J) exponent) =
            relativeWeylRealCharacterAction fam.i w
              (fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam)) + shift →
          ¬ fam.IsLeadingExponent J exponent := by
  intro r hA hT
  obtain ⟨R, hR⟩ := r.exists_regular_bound_for_ambient_chamber_separation hA hT
    fam.connectedReductive hS
  refine ⟨R, fun lam hreg w hw hpos J exponent shift hshift heq hleading => ?_⟩
  let lifted := weylCharacterRestrictionLift hA hT (fam.f I) fam.i
    (realParameterRestriction (fam.a I ≫ fam.l I) (parameterRealPart F (fam.P I) lam))
  have hLift : fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam) = lifted :=
    eisensteinAmbientParameterLift F G (fam.P I) (fam.M I) (fam.A I)
      (fam.p I) (fam.l I) (fam.a I) r hA hT (fam.torus I)
      fam.connectedReductive (fam.torus_comp I) (parameterRealPart F (fam.P I) lam)
  obtain ⟨β, hβ, hneg⟩ := hR lam hreg w hw hpos shift hshift
  change relativeWeylInvariantForm fam.i hT
    (relativeWeylRealCharacterAction fam.i w lifted + shift) ((1 : ℝ) ⊗ₜ[ℤ] β) < 0 at hneg
  rw [← hLift, ← heq] at hneg
  let B := relativeWeylInvariantForm fam.i hT
  have hB : IsWeylInvariantInnerProduct fam.i B :=
    ⟨relativeWeylInvariantForm_symm fam.i hT,
      fun _ => relativeWeylInvariantForm_pos fam.i hT,
      relativeWeylInvariantForm_invariant fam.i hT⟩
  let root : relativeRoots fam.i := ⟨β, hβ.1.1⟩
  have hNonneg := (fam.coroots.coroot_nonneg_iff fam.i B hB root _).mp (hleading root hβ)
  exact (not_lt_of_ge hNonneg) hneg

/-- The real part of a competing label, embedded in `𝔞₀^*`, is the Weyl translate of the
embedded real part of the parameter, shifted by the embedded real part of the offset. -/
theorem _root_.Langlands.Global.CompetingWeylExponents.chamberEmbedding_label
    {I J : Index} {selected : relativeWeylGroup fam.i}
    (data : CompetingWeylExponents fam I J selected) (k : Fin data.size)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    fam.chamberEmbedding J (parameterRealPart F (fam.P J) (data.label k lam)) =
      relativeWeylRealCharacterAction fam.i (data.weyl k)
          (fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam)) +
        fam.chamberEmbedding J (parameterRealPart F (fam.P J) (data.offset k)) := by
  rw [CompetingWeylExponents.label, map_add, map_add, data.ambient k lam]

end Nonleading

/-! ### Comparison of the cuspidal components of a solution and of the Eisenstein series -/

section Comparison

variable (hproj : CuspidalProjectionDecompositionStatement.{u})
  (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
  (hKmin : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
  (hKlevi : ∀ J : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J)
    (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hrho : IsClosedSubgroup rho)

include hproj hKmax hKmin hKlevi hrho in
/-- Along one standard `J`: let `v` and `E` be automorphic on `G(F) \ G(𝔸)` and `X` a function
with a cuspidal projection `ψφ` along `J` and an exponent decomposition of it. Suppose that the
cuspidal projection of `C_J v - X` has an exponent decomposition supported on the labels `lab₁`,
and that the cusp tests of `C_J E - X` are those of finitely many terms with exponents `lab₂`.
If no label is leading, then the cuspidal projections of `C_J v` and `C_J E` differ by finitely
many terms with nonleading exponents. -/
theorem exists_nonleading_difference_of_cuspidal_conditions (J : Index) {v E X : Y}
    (hv : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top v)
    (hE : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top E)
    {ψφ : Y} (hψφ : fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      X ψφ)
    {sφ : Finset (ComplexCharacterParameter F (fam.P J))}
    {cφ : ComplexCharacterParameter F (fam.P J) → Y}
    (hdecφ : fam.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      ψφ sφ cφ)
    {vc : Y} {s : Finset (ComplexCharacterParameter F (fam.P J))}
    {c : ComplexCharacterParameter F (fam.P J) → Y}
    (hvc : fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      (fam.constantTerm J v - X) vc)
    (hdec : fam.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      vc s c)
    {m₁ : ℕ} (lab₁ : Fin m₁ → ComplexCharacterParameter F (fam.P J))
    (hsupp : ∀ mu ∈ s, c mu ≠ 0 → ∃ k, mu = lab₁ k)
    {m₂ : ℕ} (lab₂ : Fin m₂ → ComplexCharacterParameter F (fam.P J)) (terms : Fin m₂ → Y)
    (hterms : ∀ k, fam.HasUnnormalizedExponent J (lab₂ k) (terms k))
    (htest : ∀ test : AdelicGroupPoints F (fam.M J) → ℂ,
      fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
      ∀ g : AdelicGroupPoints F G,
        (∀ k, Integrable (fam.leviPairingIntegrand J (terms k) g test)
          (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
        fam.leviPairing J (fam.constantTerm J E) g test - fam.leviPairing J X g test =
          ∑ k, fam.leviPairing J (terms k) g test)
    (hlead₁ : ∀ k, ¬ fam.IsLeadingExponent J (lab₁ k))
    (hlead₂ : ∀ k, ¬ fam.IsLeadingExponent J (lab₂ k)) :
    ∃ φc ψc : Y,
      fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
        (fam.constantTerm J v) φc ∧
      fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
        (fam.constantTerm J E) ψc ∧
      ∃ (s t u : Finset (ComplexCharacterParameter F (fam.P J)))
        (c b e : ComplexCharacterParameter F (fam.P J) → Y),
        fam.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J φc s c ∧
        fam.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J ψc t b ∧
        (∀ lam ∈ u, fam.HasUnnormalizedExponent J lam (e lam) ∧ ¬ fam.IsLeadingExponent J lam) ∧
        φc = ψc + ∑ lam ∈ u, e lam := by
  classical
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  obtain ⟨ψv, hψv, huniq, sv, cv, hdecv⟩ :=
    hproj F G fam K hKmax hKmin hKlevi rho hsmooth hrho fam.top J (fam.le_top J) v hv
  obtain ⟨ψE, hψE, -, sE, cE, hdecE⟩ :=
    hproj F G fam K hKmax hKmin hKlevi rho hsmooth hrho fam.top J (fam.le_top J) E hE
  -- the projection of `C_J v` is that of `X` plus that of `C_J v - X`
  have hv_eq : ψv = ψφ + vc := by
    have h := fam.isCuspidalProjection_add hsmooth Kinf rho J hψφ hvc
    rw [add_sub_cancel] at h
    exact (huniq _ h).symm
  -- padding finite families by zero
  let pad (A : Finset (ComplexCharacterParameter F (fam.P J)))
      (f : ComplexCharacterParameter F (fam.P J) → Y) (mu : ComplexCharacterParameter F (fam.P J)) :
      Y := if mu ∈ A then f mu else 0
  have hpad_sum : ∀ (A B : Finset (ComplexCharacterParameter F (fam.P J)))
      (f : ComplexCharacterParameter F (fam.P J) → Y), A ⊆ B →
      ∑ mu ∈ B, pad A f mu = ∑ mu ∈ A, f mu := by
    intro A B f hAB
    simp only [pad, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hAB]
  have hpad : ∀ (A : Finset (ComplexCharacterParameter F (fam.P J)))
      (f : ComplexCharacterParameter F (fam.P J) → Y)
      (Pr : ComplexCharacterParameter F (fam.P J) → Y → Prop),
      (∀ mu, Pr mu 0) → (∀ mu ∈ A, Pr mu (f mu)) → ∀ mu, Pr mu (pad A f mu) := by
    intro A f Pr h0 hf mu
    by_cases h : mu ∈ A
    · simp only [pad, h, ↓reduceIte]
      exact hf mu h
    · simp only [pad, h, ↓reduceIte]
      exact h0 mu
  -- the combined decomposition of `ψE - ψφ`
  let t := sE ∪ sφ
  let dd : ComplexCharacterParameter F (fam.P J) → Y := fun mu => pad sE cE mu - pad sφ cφ mu
  have hpadE := hpad sE cE (fun _ f => fam.IsAutomorphicOn hsmooth Kinf rho J f ∧
      fam.IsCuspidalAlong J f)
    (fun _ => ⟨fam.isAutomorphicOn_zero hsmooth Kinf rho J, fam.isCuspidalAlong_zero J⟩)
    (fun mu h => ⟨hdecE.automorphic mu h, hdecE.cuspidal mu h⟩)
  have hpadφ := hpad sφ cφ (fun _ f => fam.IsAutomorphicOn hsmooth Kinf rho J f ∧
      fam.IsCuspidalAlong J f)
    (fun _ => ⟨fam.isAutomorphicOn_zero hsmooth Kinf rho J, fam.isCuspidalAlong_zero J⟩)
    (fun mu h => ⟨hdecφ.automorphic mu h, hdecφ.cuspidal mu h⟩)
  have hdd_aut : ∀ mu, fam.IsAutomorphicOn hsmooth Kinf rho J (dd mu) := fun mu =>
    fam.isAutomorphicOn_sub_of_isAutomorphicOn hsmooth Kinf rho J (hpadE mu).1 (hpadφ mu).1
  have hdd_cusp : ∀ mu, fam.IsCuspidalAlong J (dd mu) := fun mu =>
    fam.isCuspidalAlong_sub hsmooth Kinf rho J (hpadE mu).1 (hpadφ mu).1 (hpadE mu).2
      (hpadφ mu).2
  have hdd_exp : ∀ mu, fam.HasUnnormalizedExponent J mu (dd mu) := fun mu =>
    fam.hasUnnormalizedExponent_sub J
      (hpad sE cE (fun mu f => fam.HasUnnormalizedExponent J mu f)
        (fun mu => fam.hasUnnormalizedExponent_zero J mu) hdecE.exponent mu)
      (hpad sφ cφ (fun mu f => fam.HasUnnormalizedExponent J mu f)
        (fun mu => fam.hasUnnormalizedExponent_zero J mu) hdecφ.exponent mu)
  have hdd_sum : ψE - ψφ = ∑ mu ∈ t, dd mu := by
    rw [Finset.sum_sub_distrib, hpad_sum sE t cE Finset.subset_union_left,
      hpad_sum sφ t cφ Finset.subset_union_right, ← hdecE.sum_eq, ← hdecφ.sum_eq]
  -- the components of `ψE - ψφ` off the labels `lab₂` vanish
  have hdd_zero : ∀ mu ∈ t, (∀ k, mu ≠ lab₂ k) → dd mu = 0 := by
    intro mu hmu hne
    apply fam.eq_zero_of_isCuspidalAlong_of_forall_leviPairing_eq_zero hproj K hKmax hKmin
      hKlevi rho hsmooth hrho J (hdd_aut mu) (hdd_cusp mu)
    intro test htest' g
    have hint : ∀ f : Y, fam.IsAutomorphicOn hsmooth Kinf rho J f → ∀ g,
        Integrable (fam.leviPairingIntegrand J f g test)
          (normOneRationalQuotientHaarMeasure F (fam.M J)) := fun f hf g =>
      fam.integrable_leviPairingIntegrand_of_isAutomorphicOn hproj K hKmax hKmin hKlevi rho
        hsmooth hrho J hf htest' g
    refine fam.leviPairing_eq_zero_of_sum_leviPairing_eq J test t dd
      (fun nu _ => ⟨fun g => hint _ (hdd_aut nu) g, hdd_exp nu⟩) lab₂ terms
      (fun k => ⟨fun g => (htest test htest' g).1 k, hterms k⟩) ?_ hmu hne g
    intro g'
    obtain ⟨-, hEi, hEeq⟩ := hψE.2.2 test htest' g'
    obtain ⟨-, hφi, hφeq⟩ := hψφ.2.2 test htest' g'
    rw [← fam.leviPairing_sum_of_integrable J t dd (fun nu _ => hint _ (hdd_aut nu) g'),
      ← hdd_sum, fam.leviPairing_sub_of_integrable J hEi hφi, ← hEeq, ← hφeq]
    exact (htest test htest' g').2
  -- assembly
  let t₂ := t.filter (fun mu => ∃ k, mu = lab₂ k)
  have hdd_filter : ∑ mu ∈ t₂, dd mu = ψE - ψφ := by
    rw [hdd_sum]
    apply Finset.sum_filter_of_ne
    intro mu hmu hne
    by_contra hk
    exact hne (hdd_zero mu hmu fun k h => hk ⟨k, h⟩)
  let s₁ := s.filter (fun mu => c mu ≠ 0)
  have hc_filter : ∑ mu ∈ s₁, c mu = vc := by
    rw [hdec.sum_eq]
    exact Finset.sum_filter_ne_zero s
  let u := s₁ ∪ t₂
  let e : ComplexCharacterParameter F (fam.P J) → Y := fun mu => pad s₁ c mu - pad t₂ dd mu
  refine ⟨ψv, ψE, hψv, hψE, sv, sE, u, cv, cE, e, hdecv, hdecE, ?_, ?_⟩
  · intro mu hmu
    refine ⟨fam.hasUnnormalizedExponent_sub J
      (hpad s₁ c (fun mu f => fam.HasUnnormalizedExponent J mu f)
        (fun mu => fam.hasUnnormalizedExponent_zero J mu)
        (fun mu h => hdec.exponent mu (Finset.mem_filter.mp h).1) mu)
      (hpad t₂ dd (fun mu f => fam.HasUnnormalizedExponent J mu f)
        (fun mu => fam.hasUnnormalizedExponent_zero J mu) (fun mu _ => hdd_exp mu) mu), ?_⟩
    rcases Finset.mem_union.mp hmu with h | h
    · obtain ⟨k, hk⟩ := hsupp mu (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2
      rw [hk]
      exact hlead₁ k
    · obtain ⟨k, hk⟩ := (Finset.mem_filter.mp h).2
      rw [hk]
      exact hlead₂ k
  · have hu_sum : ∑ mu ∈ u, e mu = vc - (ψE - ψφ) := by
      rw [Finset.sum_sub_distrib, hpad_sum s₁ u c Finset.subset_union_left,
        hpad_sum t₂ u dd Finset.subset_union_right, hc_filter, hdd_filter]
    rw [hu_sum, hv_eq]
    abel

end Comparison

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

/-- Bernstein–Lapid (6.22) for finite families, `EisensteinRegularUniquenessStatement`, follows from
five propositions: Theorem 6.3 (`LeadingCuspidalInjectivityStatement`), the cuspidal projections of
constant terms (`CuspidalProjectionDecompositionStatement`), Corollary 6.10 for finite families
(`EisensteinUniformCuspidalExpansionStatement`), automorphy of twists
(`ParameterTwistAutomorphyStatement`) and automorphy of convergent Eisenstein series
(`EisensteinRegularAutomorphyStatement`). -/
def EisensteinRegularUniquenessReductionStatement : Prop :=
  LeadingCuspidalInjectivityStatement.{u} →
  CuspidalProjectionDecompositionStatement.{u} →
  EisensteinUniformCuspidalExpansionStatement.{u} →
  ParameterTwistAutomorphyStatement.{u} →
  EisensteinRegularAutomorphyStatement.{u} →
  EisensteinRegularUniquenessStatement.{u}

/-- The implication `EisensteinRegularUniquenessReductionStatement`. -/
theorem eisensteinRegularUniqueness_of : EisensteinRegularUniquenessReductionStatement.{u} := by
  intro hinj hproj hexp htwist haut F _ _ G _ _ _ fam I _ _ _ K hK hKmax hKmin hKlevi N d rho
    hsmooth hrho Kinf hcalc r hA hT n phi hphi data
  classical
  have : Finite (StandardIndex F G fam.i fam.ν) :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i
      fam.ν).finite_subsets.to_subtype
  let : Fintype (StandardIndex F G fam.i fam.ν) := Fintype.ofFinite _
  -- Corollary 6.10: competing data and thresholds along every standard `J`
  choose Rexp dataE nE hE using fun J : StandardIndex F G fam.i fam.ν =>
    hexp F G fam I K hK hKmax hKmin hKlevi rho hsmooth hrho n phi hphi J
  -- automorphy thresholds of the Eisenstein series of the `φ i`
  choose Raut hRaut using fun i : Fin n =>
    haut F G fam I K hK hKmax hKmin hKlevi rho hsmooth hrho (phi i) (hphi i)
  -- the finitely many shifts of the competing labels
  let S : Set (RealTorusSpace.Vstar fam.T) :=
    (⋃ J : StandardIndex F G fam.i fam.ν, Set.range fun k : Fin (data J).size =>
      fam.chamberEmbedding J (parameterRealPart F (fam.P J) ((data J).offset k))) ∪
    (⋃ J : StandardIndex F G fam.i fam.ν, Set.range fun k : Fin (dataE J).size =>
      fam.chamberEmbedding J (parameterRealPart F (fam.P J) ((dataE J).offset k)))
  have hS : S.Finite :=
    (Set.finite_iUnion fun _ => Set.finite_range _).union
      (Set.finite_iUnion fun _ => Set.finite_range _)
  obtain ⟨Rsep, hsep⟩ := fam.exists_regular_forall_not_isLeadingExponent I S hS
  refine ⟨max Rsep ((∑ i, |Raut i|) + ∑ J, |Rexp J|), ?_⟩
  intro lam hreg a v hv H
  have hmono : ∀ R' : ℝ, R' ≤ max Rsep ((∑ i, |Raut i|) + ∑ J, |Rexp J|) →
      r.IsRegularParameter hA hT R' lam :=
    fun R' hR' α hα => lt_of_le_of_lt hR' (hreg α hα)
  have hregSep : r.IsRegularParameter hA hT Rsep lam := hmono Rsep (le_max_left _ _)
  have hregAut : ∀ i, r.IsRegularParameter hA hT (Raut i) lam := fun i =>
    hmono _ ((le_abs_self _).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (Raut j)) (Finset.mem_univ i)).trans
        ((le_add_of_nonneg_right (Finset.sum_nonneg fun J _ => abs_nonneg (Rexp J))).trans
          (le_max_right _ _))))
  have hregExp : ∀ J, r.IsRegularParameter hA hT (Rexp J) lam := fun J =>
    hmono _ ((le_abs_self _).trans
      ((Finset.single_le_sum (fun J' _ => abs_nonneg (Rexp J')) (Finset.mem_univ J)).trans
        ((le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => abs_nonneg (Raut i))).trans
          (le_max_right _ _))))
  -- the Eisenstein series and the twist of the combination
  set E : AdelicGroupPoints F G → ℂ := fun g => ∑ i, a i * hK.eisensteinSeries (phi i) lam g
    with hEdef
  set twist : AdelicGroupPoints F G → ℂ := fun g => ∑ i, a i * hK.parameterTwist (phi i) lam g
    with hφdef
  have hEaut : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho E := by
    have hsum : E = ∑ i, a i • hK.eisensteinSeries (phi i) lam := by
      funext g
      simp only [E, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem (automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth hcalc)
      fun i _ => Submodule.smul_mem _ _ (hRaut i lam (hregAut i))
  have hφaut : fam.IsAutomorphicOn hsmooth Kinf rho I twist := by
    have hsum : twist = ∑ i, a i • hK.parameterTwist (phi i) lam := by
      funext g
      simp only [twist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem (automorphicFunctionsOn
        (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) Kinf rho hsmooth hcalc)
      fun i _ => Submodule.smul_mem _ _
        (htwist F G fam I K hK hKmax hKmin hKlevi rho hsmooth hrho (phi i) (hphi i) lam)
  have hvtop : fam.IsAutomorphicOn hsmooth Kinf rho fam.top v :=
    (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf v).mpr hv
  have hEtop : fam.IsAutomorphicOn hsmooth Kinf rho fam.top E :=
    (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf E).mpr hEaut
  -- along every standard `J`, the cuspidal components differ by nonleading terms
  have hJ : ∀ J : StandardIndex F G fam.i fam.ν,
      ∃ φc ψc : AdelicGroupPoints F G → ℂ,
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J v) φc ∧
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J E) ψc ∧
        ∃ (s t u : Finset (ComplexCharacterParameter F (fam.P J)))
          (c b e : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
          fam.IsExponentDecomposition hsmooth Kinf rho J φc s c ∧
          fam.IsExponentDecomposition hsmooth Kinf rho J ψc t b ∧
          (∀ lam ∈ u, fam.HasUnnormalizedExponent J lam (e lam) ∧
            ¬ fam.IsLeadingExponent J lam) ∧
          φc = ψc + ∑ lam ∈ u, e lam := by
    intro J
    obtain ⟨ψφ, hψφ, sφ, cφ, hdecφ⟩ : ∃ ψφ : AdelicGroupPoints F G → ℂ,
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.parabolicConstantTerm I J twist) ψφ ∧
        ∃ (sφ : Finset (ComplexCharacterParameter F (fam.P J)))
          (cφ : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
          fam.IsExponentDecomposition hsmooth Kinf rho J ψφ sφ cφ := by
      by_cases hJI : J ≤ I
      · obtain ⟨ψ, hψ, -, s', c', hdec'⟩ :=
          hproj F G fam K hKmax hKmin hKlevi rho hsmooth hrho I J hJI twist hφaut
        have hct : fam.parabolicConstantTerm I J twist = fam.constantTerm J twist := by
          simp [StandardParabolicFamily.parabolicConstantTerm, hJI]
        exact ⟨ψ, hct ▸ hψ, s', c', hdec'⟩
      · have hct : fam.parabolicConstantTerm I J twist = 0 := by
          simp [StandardParabolicFamily.parabolicConstantTerm, hJI]
        refine ⟨0, hct ▸ fam.isCuspidalProjection_zero hsmooth Kinf rho J, ∅, fun _ => 0,
          ⟨by simp, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩⟩
    obtain ⟨vc, s, c, hvc, hdec, hsupp⟩ := H J
    obtain ⟨terms, hpoly, htests⟩ := hE J lam (hregExp J) a
    have hshift₁ : ∀ k : Fin (data J).size,
        fam.chamberEmbedding J (parameterRealPart F (fam.P J) ((data J).offset k)) ∈ S :=
      fun k => Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨J, Set.mem_range_self k⟩)
    have hshift₂ : ∀ k : Fin (dataE J).size,
        fam.chamberEmbedding J (parameterRealPart F (fam.P J) ((dataE J).offset k)) ∈ S :=
      fun k => Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨J, Set.mem_range_self k⟩)
    exact fam.exists_nonleading_difference_of_cuspidal_conditions hproj K hKmax hKmin hKlevi rho
      hsmooth hrho J hvtop hEtop hψφ hdecφ hvc hdec (fun k => (data J).label k lam) hsupp
      (fun k => (dataE J).label k lam) terms (fun k => ⟨nE J, hpoly k⟩) htests
      (fun k => hsep lam hregSep ((data J).weyl k) ((data J).competing k) ((data J).positive k)
        J _ _ (hshift₁ k) (CompetingWeylExponents.chamberEmbedding_label fam (data J) k lam))
      (fun k => hsep lam hregSep ((dataE J).weyl k) ((dataE J).competing k)
        ((dataE J).positive k) J _ _ (hshift₂ k)
        (CompetingWeylExponents.chamberEmbedding_label fam (dataE J) k lam))
  obtain ⟨L, hLv, hLE⟩ :=
    fam.exists_common_leadingComponents_of_nonleading_differences hsmooth Kinf rho v E hJ
  exact hinj F G fam K hKmax hKmin hKlevi rho hsmooth hrho v E L hv hEaut hLv hLE

end Langlands.Global

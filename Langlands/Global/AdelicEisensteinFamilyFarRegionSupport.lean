import Langlands.Global.AdelicParabolicConstantTermTests
import Langlands.Global.AdelicStandardIntertwiningRegularity
import Langlands.Global.AdelicStandardTopAutomorphy
import Langlands.Analysis.Meromorphic.LocalScalarMeromorphy
import Langlands.Analysis.Meromorphic.ExponentSupport
import Langlands.Global.AdelicEisensteinInducingPairingContinuation
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Global.AdelicExponentPolynomials

/-! # Continued exponent support for finite families of inducing data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarishChandraSchwartz Langlands.Analysis.Meromorphic
  Langlands.Aubert.General.RationalPointFamily

namespace CompetingWeylExponents

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {I J : StandardIndex F G fam.i fam.ν}
  {selected : relativeWeylGroup fam.i}

/-- The concatenation of finitely many lists of competing Weyl exponents. -/
def sigma {p : ℕ} (data : Fin p → CompetingWeylExponents fam I J selected) :
    CompetingWeylExponents fam I J selected where
  size := ∑ v, (data v).size
  weyl j := (data (finSigmaFinEquiv.symm j).1).weyl (finSigmaFinEquiv.symm j).2
  linear j := (data (finSigmaFinEquiv.symm j).1).linear (finSigmaFinEquiv.symm j).2
  offset j := (data (finSigmaFinEquiv.symm j).1).offset (finSigmaFinEquiv.symm j).2
  competing _ := (data _).competing _
  positive _ := (data _).positive _
  ambient _ := (data _).ambient _

theorem sigma_label {p : ℕ} (data : Fin p → CompetingWeylExponents fam I J selected)
    (v : Fin p) (k : Fin (data v).size) (lam : ComplexCharacterParameter F (fam.P I)) :
    (sigma data).label (finSigmaFinEquiv ⟨v, k⟩) lam = (data v).label k lam := by
  have h : ∀ y : (i : Fin p) × Fin (data i).size, y = ⟨v, k⟩ →
      (data y.1).label y.2 lam = (data v).label k lam := by
    rintro _ rfl
    rfl
  exact h _ (Equiv.symm_apply_apply _ _)

end CompetingWeylExponents

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Y" => (AdelicGroupPoints F G → ℂ)

local instance familySupportSplitCommGroup (J : StandardIndex F G fam.i fam.ν) :
    CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.2 b.2)

/-- The norm-one Levi test of the constant term of a finite combination of automorphic forms
on `G(F) \ G(𝔸)` is the corresponding combination of the tests. -/
theorem leviPairing_constantTerm_sum_of_automorphic (J : StandardIndex F G fam.i fam.ν)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {p : ℕ} (f : Fin p → Y)
    (hf : ∀ v, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (f v))
    (c : Fin p → ℂ) {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (ht : fam.IsLeviCuspForm Kinf rho J test)
    (hmaj : ∀ g (R : ℝ), fam.HasLeviPairingMajorant J test g rho R) (g : AdelicGroupPoints F G) :
    fam.leviPairing J (fam.constantTerm J (∑ v, c v • f v)) g test =
      ∑ v, c v * fam.leviPairing J (fam.constantTerm J (f v)) g test := by
  have htop : ∀ v, fam.IsAutomorphicOn hsmooth Kinf rho fam.top (f v) :=
    fun v => (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf _).mpr (hf v)
  refine fam.leviPairing_constantTerm_sum_smul fam.top J rho hsmooth Kinf (fam.le_top J) f htop c
    test (fun v => ?_) g
  exact fam.constantTerm_mem_leviPairingDomain_of_le rho hN (fam.le_top J) (htop v).1
    (htop v).2.1.1 (htop v).2.2.2.2 ht.1.2.1.1 ht.1.1 hmaj

/-- Pairing against a fixed test distributes over a finite linear combination of functions in
the pairing domain. -/
theorem leviPairing_sum_smul (J : StandardIndex F G fam.i fam.ν) {κ : Type*} (t : Finset κ)
    {test : AdelicGroupPoints F (fam.M J) → ℂ} (c : κ → ℂ) (f : κ → Y)
    (hf : ∀ i ∈ t, f i ∈ fam.leviPairingDomain J test) (g : AdelicGroupPoints F G) :
    fam.leviPairing J (∑ i ∈ t, c i • f i) g test = ∑ i ∈ t, c i * fam.leviPairing J (f i) g test := by
  rw [fam.leviPairing_finset_sum J t _ (fun i hi => Submodule.smul_mem _ _ (hf i hi)) g]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : fam.leviPairingIntegrand J (c i • f i) g test =
      c i • fam.leviPairingIntegrand J (f i) g test := by
    funext q
    simp only [leviPairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
  unfold leviPairing
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem meromorphicOn_of_differentiable'' {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {D : Set (Fin n → ℂ)} (ho : IsOpen D) (hd : Dense D) (hf : Differentiable ℂ f) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D := by
  have h1 : DifferentiableOn ℂ (fun _ : Fin n → ℂ => (1 : ℂ)) univ := differentiableOn_const 1
  refine ⟨ho, hd, isHolomorphicOn_iff_differentiableOn_scalar.mpr hf.differentiableOn,
    fun x => ⟨univ, isOpen_univ, isConnected_univ, mem_univ x, fun _ => 1, f,
      h1.mdifferentiableOn, ⟨x, mem_univ x, one_ne_zero⟩,
      isHolomorphicOn_iff_differentiableOn_scalar.mpr hf.differentiableOn, ?_⟩⟩
  exact fun _ _ => one_smul _ _

variable (I Q J : StandardIndex F G fam.i fam.ν)
  [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
  [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
  [IsClosedImmersion (fam.p Q).hom.hom.left]

/-- **Continued exponent support for a finite family.** Let `Ev v` continue the `P_I`-series
of `φ v` with meromorphic tests on `U`, and let `b v` be meromorphic coefficients with
`∑ v, b v · M(w, λ)(φ v) = ∑ i, coeff i · ψ i` for regular `λ`. On the common domain, the test
of `C_J (∑ v, b v · Ev v)` minus the test of the nested constant term of the twisted inducing
expression has no joint generalized eigencomponent outside the concatenated competing Weyl
labels of the convergent expansions (6.20) of the `φ v`. -/
theorem exists_competingWeylExponents_continued_support_family
    (hExp : ConvergentCuspidalTestExpansionStatement.{u})
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I) (proj : fam.P Q ⟶ fam.M Q)
    (hproj : fam.l Q ≫ proj = 𝟙 (fam.M Q))
    (hc : IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c)
    (hIQ : ∀ α ∈ I.val, schemeWeylCharacterAction fam.i
      (QuotientGroup.mk n : relativeWeylGroup fam.i) α ∈ Q.val)
    (hQI : ∀ α ∈ Q.val, schemeWeylCharacterAction fam.i
      ((QuotientGroup.mk n : relativeWeylGroup fam.i)⁻¹) α ∈ I.val)
    {K : Subgroup (AdelicGroupPoints F G)} (hKI : IsIwasawaCompact (fam.p I) K)
    (hKQ : IsIwasawaCompact (fam.p Q) K) (hKmax : IsMaximalCompactSubgroup F G K)
    (hK0 : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J')
      (K.comap (map F (fam.M J') G (fam.l J' ≫ fam.p J')).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hMaj : ∀ ψ : AdelicGroupPoints F (fam.M J) → ℂ,
      fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ →
        ∀ g (R : ℝ), fam.HasLeviPairingMajorant J ψ g rho R)
    {p : ℕ} (φ : Fin p → Y)
    (hφ : ∀ v, fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I (φ v))
    {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I))
    (Ev : Fin p → (Fin m → ℂ) → Y) (U : Set (Fin m → ℂ)) (hU : IsOpen U) (hUd : Dense U)
    (hEvaut : ∀ v, ∀ z ∈ U, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho (Ev v z))
    (hEvtest : ∀ v (test : AdelicGroupPoints F (fam.M J) → ℂ),
      fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test → ∀ g,
        IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ)
          (fun z => fam.leviPairing J (fam.constantTerm J (Ev v z)) g test) U)
    (hEvser : ∃ R₀ : ℝ, ∀ v z, (fam.standardPresentation I).IsRegularParameter
      (fam.isSplitTorus_splitComponent I) fam.isSplitTorus_torus R₀ (e z) →
        Ev v z = hKI.eisensteinSeries (φ v) (e z))
    (b : Fin p → (Fin m → ℂ) → ℂ) (Db : Set (Fin m → ℂ)) (hDbo : IsOpen Db) (hDbd : Dense Db)
    (hb : ∀ v, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (b v) Db)
    {k : ℕ} (ψ : Fin k → AdelicGroupPoints F G → ℂ)
    (hψ : ∀ i, fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q (ψ i))
    (hψproj : J ≤ Q → ∀ i, ∃ c', fam.IsCuspidalProjection hsmooth
      (K.comap (ofInfinite F G).toMonoidHom) rho J (fam.constantTerm J (ψ i)) c')
    (coeff : Fin k → (Fin m → ℂ) → ℂ) (Dc : Set (Fin m → ℂ)) (hDco : IsOpen Dc)
    (hDcd : Dense Dc) (hcoeff : ∀ i, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (coeff i) Dc)
    (hint : ∃ R₁ : ℝ, ∀ z, (fam.standardPresentation I).IsRegularParameter
      (fam.isSplitTorus_splitComponent I) fam.isSplitTorus_torus R₁ (e z) → ∀ g,
        ∑ v, b v z * hKI.intertwiningOperator hKQ (fam.iU I) (fam.l I) (fam.iU Q) c proj n.val
          (φ v) (e z) g = ∑ i, coeff i z * ψ i g) :
    ∃ data : CompetingWeylExponents fam I J (QuotientGroup.mk n),
      ∀ test : AdelicGroupPoints F (fam.M J) → ℂ,
        fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
        ∀ z ∈ U ∩ Db ∩ Dc, ∀ (sv : Finset (fam.positiveSplitComponent J → ℂ))
          (v : (fam.positiveSplitComponent J → ℂ) → AdelicGroupPoints F G → ℂ),
          (∀ δ ∈ sv, v δ ∈ jointGenEigenspace (fam.splitComponentRepresentation J) δ) →
          (∑ δ ∈ sv, v δ) = (fun g =>
            fam.leviPairing J (fam.constantTerm J (∑ w, b w z • Ev w z)) g test -
              fam.leviPairing J (fam.parabolicConstantTerm Q J (hKQ.parameterTwist
                (∑ i, coeff i z • ψ i) (weylParameter (fam.l I) c proj (e z)))) g test) →
          ∀ δ ∈ sv, (∀ j, δ ≠ fun b : fam.positiveSplitComponent J =>
            parameterPower F (fam.P J) (data.label j (e z)) b.val) → v δ = 0 := by
  classical
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let r := fam.standardPresentation I
  let hA := fam.isSplitTorus_splitComponent I
  let hT := fam.isSplitTorus_torus
  have hExpv := fun v => hExp F G fam I Q n c hc hIQ hQI K hKI hKmax hK0 hKlevi rho hsmooth
    hrho (φ v) (hφ v) J
  choose Rv datav hdatav using hExpv
  have hIntv := fun v => fam.exists_intertwiningIntegral_regular I Q hN n c proj hproj hc hKI hKQ
    hKmax rho hrho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth) (φ v) (hφ v)
  choose Riv hIntv using hIntv
  obtain ⟨R₀, hR₀⟩ := hEvser
  obtain ⟨R₁, hR₁⟩ := hint
  let data := CompetingWeylExponents.sigma datav
  refine ⟨data, fun test ht => ?_⟩
  let D := U ∩ Db ∩ Dc
  have hDo : IsOpen D := (hU.inter hDbo).inter hDco
  have hDd : Dense D := (hUd.inter_of_isOpen_right hDbd hDbo).inter_of_isOpen_right hDcd hDco
  let S₀ : ℝ := ∑ v, |Rv v| + ∑ v, |Riv v|
  let Rall : ℝ := max S₀ (max R₀ R₁)
  have hRv : ∀ v, Rv v ≤ Rall := fun v =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun v _ => abs_nonneg (Rv v))
      (Finset.mem_univ v)).trans ((le_add_of_nonneg_right
        (Finset.sum_nonneg fun v _ => abs_nonneg (Riv v))).trans (le_max_left _ _)))
  have hRiv : ∀ v, Riv v ≤ Rall := fun v =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun v _ => abs_nonneg (Riv v))
      (Finset.mem_univ v)).trans ((le_add_of_nonneg_left
        (Finset.sum_nonneg fun v _ => abs_nonneg (Rv v))).trans (le_max_left _ _)))
  have hR₀le : R₀ ≤ Rall := (le_max_left _ _).trans (le_max_right _ _)
  have hR₁le : R₁ ≤ Rall := (le_max_right _ _).trans (le_max_right _ _)
  let W := {z | r.IsRegularParameter hA hT Rall (e z)} ∩ D
  have hWo : IsOpen W := (r.isOpen_regularParameter_inCoordinates hA hT Rall e).inter hDo
  have hWne : W.Nonempty :=
    hDd.inter_open_nonempty _ (r.isOpen_regularParameter_inCoordinates hA hT Rall e)
      (r.nonempty_regularParameter_inCoordinates hA hT Rall e)
  let χ (j : Fin data.size) (z : Fin m → ℂ) (b : fam.positiveSplitComponent J) : ℂ :=
    parameterPower F (fam.P J) (data.label j (e z)) b.val
  let ref (z : Fin m → ℂ) : Y := fun g =>
    fam.leviPairing J (fam.parabolicConstantTerm Q J (hKQ.parameterTwist
      (∑ i, coeff i z • ψ i) (weylParameter (fam.l I) c proj (e z)))) g test
  let Φ (z : Fin m → ℂ) : Y := fun g =>
    fam.leviPairing J (fam.constantTerm J (∑ w, b w z • Ev w z)) g test - ref z g
  have hlin : ∀ z ∈ U, ∀ g, fam.leviPairing J (fam.constantTerm J (∑ w, b w z • Ev w z)) g test =
      ∑ w, b w z * fam.leviPairing J (fam.constantTerm J (Ev w z)) g test :=
    fun z hz g => fam.leviPairing_constantTerm_sum_of_automorphic J rho hN hsmooth hcalc Kinf
      (fun w => Ev w z) (fun w => hEvaut w z hz) (fun w => b w z) ht (hMaj test ht) g
  have hΦ : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun z => Φ z g) D := by
    intro g
    have h1 : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ)
        (∑ w, (b w * fun z => fam.leviPairing J (fam.constantTerm J (Ev w z)) g test)) D :=
      IsMeromorphicOn.sum Finset.univ hDo hDd fun w _ =>
        ((hb w).mul (hEvtest w test ht g)).restrict_domain hDo hDd
          (fun z hz => ⟨hz.1.2, hz.1.1⟩)
    have h2 := eisensteinInducingPairingContinuation F G fam Q J hKQ rho hsmooth Kinf
      ((weylParameter (fam.l I) c proj).comp e.toLinearMap) Dc ψ coeff hDco hDcd hψ hψproj
      hcoeff test ht g
    have h2' := h2.neg.restrict_domain hDo hDd inter_subset_right
    have h3 := h1.add h2'
    rw [inter_self] at h3
    refine h3.congr_domain fun z hz => ?_
    change fam.leviPairing J (fam.constantTerm J (∑ w, b w z • Ev w z)) g test - ref z g =
      (∑ w, (b w * fun z => fam.leviPairing J (fam.constantTerm J (Ev w z)) g test)) z +
        -ref z g
    rw [hlin z hz.1.1, sub_eq_add_neg]
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hχ : ∀ j b, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun z => χ j z b) D := by
    intro j b
    refine meromorphicOn_of_differentiable'' hDo hDd ?_
    have := differentiable_parameterPower_affine (F := F) (G := fam.P J)
      ((data.linear j).comp e.toLinearMap) (data.offset j) b.val
    simpa only [χ, CompetingWeylExponents.label, LinearMap.comp_apply,
      LinearEquiv.coe_coe] using this
  have hseed : ∀ z ∈ W, ∃ vv : Fin data.size → AdelicGroupPoints F G → ℂ,
      (∀ j, vv j ∈ jointGenEigenspace (fam.splitComponentRepresentation J) (χ j z)) ∧
        Φ z = ∑ j, vv j := by
    rintro z ⟨hzr, hzD⟩
    have hzv : ∀ v, r.IsRegularParameter hA hT (Rv v) (e z) :=
      fun v α hα => (hRv v).trans_lt (hzr α hα)
    have hziv : ∀ v, r.IsRegularParameter hA hT (Riv v) (e z) :=
      fun v α hα => (hRiv v).trans_lt (hzr α hα)
    have hz0 : r.IsRegularParameter hA hT R₀ (e z) := fun α hα => hR₀le.trans_lt (hzr α hα)
    have hz1 : r.IsRegularParameter hA hT R₁ (e z) := fun α hα => hR₁le.trans_lt (hzr α hα)
    have hterms := fun v => hdatav v (e z) (hzv v)
    choose terms hexp htests using hterms
    let vv (j : Fin data.size) : Y := b (finSigmaFinEquiv.symm j).1 z •
      fun g => fam.leviPairing J (terms (finSigmaFinEquiv.symm j).1
        (finSigmaFinEquiv.symm j).2) g test
    refine ⟨vv, fun j => ?_, ?_⟩
    · refine Submodule.smul_mem _ _ ?_
      exact fam.leviPairing_mem_jointGenEigenspace J
        (fun g => (htests (finSigmaFinEquiv.symm j).1 test ht g).1 (finSigmaFinEquiv.symm j).2)
        (hexp (finSigmaFinEquiv.symm j).1 (finSigmaFinEquiv.symm j).2)
    · -- the inducing expression is the combination of the intertwining integrals
      let Iw (w : Fin p) : Y :=
        hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val (φ w) (e z)
      have htw : hKQ.parameterTwist (∑ i, coeff i z • ψ i) (weylParameter (fam.l I) c proj (e z)) =
          ∑ w, b w z • Iw w := by
        funext g'
        simp only [Iw, fam.intertwiningIntegral_eq_parameterTwist hKI hKQ c proj n.val _ (e z),
          IsIwasawaCompact.parameterTwist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← hR₁ z hz1 g', Finset.sum_mul]
        exact Finset.sum_congr rfl fun w _ => by ring
      have hCw : ∀ w, fam.parabolicConstantTerm Q J (Iw w) ∈ fam.leviPairingDomain J test := by
        intro w
        by_cases hJQ : J ≤ Q
        · simp only [parabolicConstantTerm, hJQ, ↓reduceIte]
          obtain ⟨hinv, hcont, hgrowth⟩ := hIntv w (e z) (hziv w)
          exact fam.constantTerm_mem_leviPairingDomain_of_le rho hN hJQ hinv hcont hgrowth
            ht.1.2.1.1 ht.1.1 (hMaj test ht)
        · simp only [parabolicConstantTerm, hJQ, ↓reduceIte]
          exact Submodule.zero_mem _
      have hsumC : fam.parabolicConstantTerm Q J (∑ w, b w z • Iw w) =
          ∑ w, b w z • fam.parabolicConstantTerm Q J (Iw w) := by
        by_cases hJQ : J ≤ Q
        · simp only [parabolicConstantTerm, hJQ, ↓reduceIte]
          exact fam.constantTerm_finset_sum_of_le hJQ Finset.univ (fun w => b w z) Iw
            (fun w _ => (hIntv w (e z) (hziv w)).2.1) (fun w _ => (hIntv w (e z) (hziv w)).1)
        · simp only [parabolicConstantTerm, hJQ, ↓reduceIte, smul_zero, Finset.sum_const_zero]
      have href : ∀ g, ref z g =
          ∑ w, b w z * fam.leviPairing J (fam.parabolicConstantTerm Q J (Iw w)) g test := by
        intro g
        change fam.leviPairing J (fam.parabolicConstantTerm Q J (hKQ.parameterTwist
          (∑ i, coeff i z • ψ i) (weylParameter (fam.l I) c proj (e z)))) g test = _
        rw [htw, hsumC]
        exact fam.leviPairing_sum_smul J Finset.univ _ _ (fun w _ => hCw w) g
      funext g
      have hsplit : Φ z g = ∑ w, b w z * ∑ kk, fam.leviPairing J (terms w kk) g test := by
        change fam.leviPairing J (fam.constantTerm J (∑ w, b w z • Ev w z)) g test - ref z g = _
        rw [hlin z hzD.1.1, href g, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← mul_sub, ← (htests w test ht g).2, hR₀ w z hz0]
      rw [hsplit]
      have hre : (∑ j : Fin data.size, vv j g) =
          ∑ x : (w : Fin p) × Fin (datav w).size,
            b x.1 z * fam.leviPairing J (terms x.1 x.2) g test :=
        finSigmaFinEquiv.symm.sum_comp
          (fun x : (w : Fin p) × Fin (datav w).size =>
            b x.1 z * fam.leviPairing J (terms x.1 x.2) g test)
      rw [Finset.sum_apply, hre, Fintype.sum_sigma]
      exact Finset.sum_congr rfl fun w _ => Finset.mul_sum _ _ _
  exact meromorphicExponentSupport m (fam.positiveSplitComponent J) (AdelicGroupPoints F G) D W
    (fam.splitComponentRepresentation J) (fun b x => map F (fam.P J) G (fam.p J) b.val * x)
    (fun _ _ _ => rfl) data.size χ Φ hDo hDd hWo hWne hΦ hχ hseed

end StandardParabolicFamily

end Langlands.Global

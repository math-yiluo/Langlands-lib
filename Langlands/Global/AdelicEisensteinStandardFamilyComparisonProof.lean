import Langlands.Global.AdelicEisensteinFarRegionExpansion
import Langlands.Global.AdelicEisensteinFamilyFarRegionSupport
import Langlands.Global.AdelicEisensteinContinuationTests
import Langlands.Global.AdelicLeadingCuspidalInjectivityStatement
import Langlands.Global.AdelicEisensteinNonleadingWeylTermsProof
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicEisensteinStandardFamilyComparisonReductionStatement
import Langlands.Global.AdelicEisensteinStandardRegularComparisonStatement
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding

/-! # Proof of the regular-patch Eisenstein comparison for finite families of inducing data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set TensorProduct
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

namespace StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarishChandraSchwartz Langlands.Analysis.Meromorphic
  Langlands.Aubert.General.RationalPointFamily RealTorusSpace

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Y" => (AdelicGroupPoints F G → ℂ)

local instance familyComparisonSplitCommGroup (J : StandardIndex F G fam.i fam.ν) :
    CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.2 b.2)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem isOpen_dense_iInter_const' {X : Type*} [TopologicalSpace X] {k : ℕ} {S : Set X}
    (hS : 0 < k → IsOpen S ∧ Dense S) : IsOpen (⋂ _ : Fin k, S) ∧ Dense (⋂ _ : Fin k, S) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [iInter_of_empty, isOpen_univ, dense_univ, and_self]
  · let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    rw [iInter_const]
    exact hS hk

variable (I Q : StandardIndex F G fam.i fam.ν)
  [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
  [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
  [IsClosedImmersion (fam.p Q).hom.hom.left]
  [Mono (CommGroupScheme.groupHom (fam.f Q)).hom.hom.left]

/-- **Far-region comparison for finite families** (Bernstein–Lapid §8.6, first step of the
proof of Theorem 2.3 (4)). For standard parabolics `P_I`, `P_Q` of one family with a Weyl
element `w ∈ W(P_I, P_Q)` sending the simple roots of `I` to those of `Q`, a compact in good
position, finitely many inducing forms `φ v` with meromorphic coefficients `b v`, and a
meromorphic `EP` equal to `∑ v, b v λ · E(φ v, λ)` for regular `λ`, the function `EP` agrees
with the convergent `P_Q`-series of the continued intertwining datum on a nonempty open patch
where `wλ` is as regular as required. The inputs are Bernstein–Lapid Theorem 2.3 (1),
Theorem 6.3, (6.20), the cuspidal projections of §6.2 and the integrable majorants of Levi
cusp forms. -/
theorem standardFamilyComparison_of_inputs
    (hCont : EisensteinMeromorphicContinuationStatement.{u})
    (hInj : LeadingCuspidalInjectivityStatement.{u})
    (hExp : ConvergentCuspidalTestExpansionStatement.{u})
    (hProj : CuspidalProjectionDecompositionStatement.{u})
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
    (hMaj : ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F (fam.M J) → ℂ),
      fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ →
        ∀ g (R : ℝ), fam.HasLeviPairingMajorant J ψ g rho R)
    {p : ℕ} (φ : Fin p → AdelicGroupPoints F G → ℂ)
    (b : Fin p → ComplexCharacterParameter F (fam.P I) → ℂ)
    (Db : Set (ComplexCharacterParameter F (fam.P I)))
    (hφ : ∀ v, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I))
      (K.comap (ofInfinite F G).toMonoidHom) rho (φ v))
    (hb : ∀ v, IsMeromorphicInCoordinatesOn (b v) Db)
    (EP : ComplexCharacterParameter F (fam.P I) → AdelicGroupPoints F G → ℂ)
    (DP : Set (ComplexCharacterParameter F (fam.P I)))
    (hEP : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP)
    (hEPser : ∃ R : ℝ, ∀ lam, (fam.standardPresentation I).IsRegularParameter
      (fam.isSplitTorus_splitComponent I) fam.isSplitTorus_torus R lam → ∀ g,
        EP lam g = ∑ v, b v lam * hKI.eisensteinSeries (φ v) lam g)
    {k : ℕ} (ψ : Fin k → AdelicGroupPoints F G → ℂ)
    (coeff : Fin k → ComplexCharacterParameter F (fam.P I) → ℂ)
    (D : Set (ComplexCharacterParameter F (fam.P I)))
    (hψ : ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q))
      (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i))
    (hcoeff : ∀ i, IsMeromorphicInCoordinatesOn (coeff i) D)
    (hint : ∃ R : ℝ, ∀ lam, (fam.standardPresentation I).IsRegularParameter
      (fam.isSplitTorus_splitComponent I) fam.isSplitTorus_torus R lam → ∀ g,
        ∑ v, b v lam *
            hKI.intertwiningOperator hKQ (fam.iU I) (fam.l I) (fam.iU Q) c proj n.val (φ v) lam g =
          ∑ i, coeff i lam * ψ i g)
    (R : ℝ) :
    ∃ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I))
      (O : Set (Fin m → ℂ)), IsOpen O ∧ O.Nonempty ∧
      ∀ x ∈ O, (fam.standardPresentation Q).IsRegularParameter
          (fam.isSplitTorus_splitComponent Q) fam.isSplitTorus_torus R
          (weylParameter (fam.l I) c proj (e x)) ∧
        ∀ g : AdelicGroupPoints F G, EP (e x) g =
          ∑ i, coeff i (e x) * hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj (e x)) g := by
  classical
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let rI := fam.standardPresentation I
  let rQ := fam.standardPresentation Q
  let hAI := fam.isSplitTorus_splitComponent I
  let hAQ := fam.isSplitTorus_splitComponent Q
  let hT := fam.isSplitTorus_torus
  have : Finite (StandardIndex F G fam.i fam.ν) :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i
      fam.ν).finite_subsets.to_subtype
  let : Fintype (StandardIndex F G fam.i fam.ν) := Fintype.ofFinite _
  -- linear coordinates and the Weyl parameter equivalence
  let : FiniteDimensional ℂ (ComplexCharacterParameter F (fam.P I)) := (hEP 1).1
  let m := Module.finrank ℂ (ComplexCharacterParameter F (fam.P I))
  let e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I) :=
    (Module.finBasis ℂ (ComplexCharacterParameter F (fam.P I))).equivFun.symm
  have hcI : IsIso c := hc.isIso
  obtain ⟨wE, hwE⟩ := exists_weylParameter_linearEquiv (fam.l I) (fam.l Q)
    (fam.isCompatible I).levi (fam.isCompatible Q).levi c proj hproj
  let eQ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P Q) := e.trans wE
  have heQ : ∀ z, eQ z = weylParameter (fam.l I) c proj (e z) := fun z => by
    change wE (e z) = _
    rw [← hwE]
    rfl
  -- the continuations of the `P`-series of the inducing forms and their tests
  have hPcont := fun v => hCont F G (fam.P I) (fam.M I) (fam.U I) (fam.A I) (fam.p I)
    (fam.iU I) (fam.l I) (fam.a I) rI hAI hT fam.connectedReductive (fam.isUnipotentRadical I)
    K hKI rho hN hrho hsmooth hcalc (φ v) hKmax (hφ v)
  choose Ev hEvser hEvloc using hPcont
  choose R₀s hR₀s using hEvser
  have hPU := fun v => fam.exists_openDense_continuation_tests rho hN hrho hsmooth hcalc Kinf
    (fun z => Ev v (e z)) hMaj (hEvloc v m e)
  choose Uv hUvo hUvd hUvmer hUvaut hUvtest using hPU
  let U : Set (Fin m → ℂ) := ⋂ v, Uv v
  have hUo : IsOpen U := isOpen_iInter_of_finite hUvo
  have hUd : Dense U := dense_iInter_of_isOpen hUvo hUvd
  -- the coefficient domains
  let Dc : Set (Fin m → ℂ) := ⋂ _ : Fin k, e ⁻¹' D
  have hDc : IsOpen Dc ∧ Dense Dc := isOpen_dense_iInter_const' fun hk =>
    ⟨((hcoeff ⟨0, hk⟩).2 m e).1, ((hcoeff ⟨0, hk⟩).2 m e).2.1⟩
  have hcoeffz : ∀ i, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun z => coeff i (e z)) Dc :=
    fun i => ((hcoeff i).2 m e).restrict_domain hDc.1 hDc.2 (iInter_subset (fun _ => e ⁻¹' D) i)
  let Dbz : Set (Fin m → ℂ) := ⋂ _ : Fin p, e ⁻¹' Db
  have hDbz : IsOpen Dbz ∧ Dense Dbz := isOpen_dense_iInter_const' fun hp =>
    ⟨((hb ⟨0, hp⟩).2 m e).1, ((hb ⟨0, hp⟩).2 m e).2.1⟩
  have hbz : ∀ v, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun z => b v (e z)) Dbz :=
    fun v => ((hb v).2 m e).restrict_domain hDbz.1 hDbz.2 (iInter_subset (fun _ => e ⁻¹' Db) v)
  -- the combined continuation
  let E' (lam : ComplexCharacterParameter F (fam.P I)) : Y := ∑ v, b v lam • Ev v lam
  have hE'mer : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun z => E' (e z) g) (U ∩ Dbz) := by
    intro g
    have h := IsMeromorphicOn.sum Finset.univ (hUo.inter hDbz.1)
      (hUd.inter_of_isOpen_right hDbz.2 hDbz.1) fun v _ =>
        ((hbz v).mul (hUvmer v g)).restrict_domain (hUo.inter hDbz.1)
          (hUd.inter_of_isOpen_right hDbz.2 hDbz.1)
          (fun z hz => ⟨hz.2, mem_iInter.mp hz.1 v⟩)
    refine h.congr_domain fun z _ => ?_
    simp only [E', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  have hE'aut : ∀ z ∈ U, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho
      (E' (e z)) := fun z hz =>
    Submodule.sum_mem (automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth hcalc)
      fun v _ => Submodule.smul_mem _ _ (hUvaut v z (mem_iInter.mp hz v))
  obtain ⟨Rp, hRp⟩ := hEPser
  let R₀ : ℝ := ∑ v, |R₀s v|
  have hR₀le : ∀ v, R₀s v ≤ R₀ := fun v =>
    (le_abs_self _).trans (Finset.single_le_sum (fun v _ => abs_nonneg (R₀s v)) (Finset.mem_univ v))
  have hEPeq : ∀ z ∈ e ⁻¹' DP ∩ (U ∩ Dbz), EP (e z) = E' (e z) := by
    intro z hz
    funext g
    have heq := ((hEP g).2 m e).eqOn_of_eqOn_open (hE'mer g)
      (rI.isOpen_regularParameter_inCoordinates hAI hT (max Rp R₀) e)
      (rI.nonempty_regularParameter_inCoordinates hAI hT (max Rp R₀) e)
      (fun t ht => by
        have h1 : rI.IsRegularParameter hAI hT Rp (e t) :=
          fun α hα => (le_max_left _ _).trans_lt (ht.1 α hα)
        have h2 : ∀ v, rI.IsRegularParameter hAI hT (R₀s v) (e t) :=
          fun v α hα => ((hR₀le v).trans (le_max_right _ _)).trans_lt (ht.1 α hα)
        change EP (e t) g = E' (e t) g
        rw [hRp (e t) h1 g]
        simp only [E', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun v _ => by rw [hR₀s v (e t) (h2 v)])
    exact heq hz
  -- continuations of the `Q`-series
  have hQcont := fun i => hCont F G (fam.P Q) (fam.M Q) (fam.U Q) (fam.A Q) (fam.p Q)
    (fam.iU Q) (fam.l Q) (fam.a Q) rQ hAQ hT fam.connectedReductive (fam.isUnipotentRadical Q)
    K hKQ rho hN hrho hsmooth hcalc (ψ i) hKmax (hψ i)
  choose EQc hEQser hEQloc using hQcont
  choose RQs hRQs using hEQser
  have hQU := fun i => fam.exists_openDense_continuation_tests rho hN hrho hsmooth hcalc Kinf
    (fun z => EQc i (eQ z)) hMaj (hEQloc i m eQ)
  choose UQ hUQo hUQd _hUQmer hUQaut _hUQtest using hQU
  -- cuspidal projections of the inducing forms
  have hψaut : ∀ i, fam.IsAutomorphicOn hsmooth Kinf rho Q (ψ i) := hψ
  have hψproj := fun (J : StandardIndex F G fam.i fam.ν) (hJQ : J ≤ Q) (i : Fin k) =>
    hProj F G fam K hKmax hK0 hKlevi rho hsmooth hrho Q J hJQ (ψ i) (hψaut i)
  have hψdata : ∀ (J : StandardIndex F G fam.i fam.ν), J ≤ Q → ∀ i, ∃ (ψc : Y)
      (sψ : Finset (ComplexCharacterParameter F (fam.P J)))
      (cψ : ComplexCharacterParameter F (fam.P J) → Y),
      fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J (ψ i)) ψc ∧
        fam.IsExponentDecomposition hsmooth Kinf rho J ψc sψ cψ := by
    intro J hJQ i
    obtain ⟨ψc, hp, -, sψ, cψ, hd⟩ := hψproj J hJQ i
    exact ⟨ψc, sψ, cψ, hp, hd⟩
  -- test domains and cusp detection
  have hdom : ∀ (J : StandardIndex F G fam.i fam.ν) test,
      fam.IsLeviCuspForm Kinf rho J test →
        ∀ f, fam.IsAutomorphicOn hsmooth Kinf rho J f → f ∈ fam.leviPairingDomain J test :=
    fun J test ht f hf =>
      fam.mem_leviPairingDomain_of_isAutomorphicOn_of_majorant J rho hsmooth Kinf hf
        ht.1.2.1.1 ht.1.1 (hMaj J test ht)
  have hdetect : ∀ (J : StandardIndex F G fam.i fam.ν) f,
      fam.IsAutomorphicOn hsmooth Kinf rho J f → fam.IsCuspidalAlong J f →
      (∀ test, fam.IsLeviCuspForm Kinf rho J test → ∀ g, fam.leviPairing J f g test = 0) →
      f = 0 :=
    fun J f hf hcusp hzero => fam.eq_zero_of_leviPairings_eq_zero J rho hsmooth hProj hKmax hK0
      hKlevi hrho hf hcusp (fun test ht => hdom J test ht f hf) hzero
  -- the competing exponent data
  have hPdata := fun (J : StandardIndex F G fam.i fam.ν) =>
    fam.exists_competingWeylExponents_continued_support_family I Q J hExp n c proj hproj hc hIQ
      hQI hKI hKQ hKmax hK0 hKlevi rho hN hrho hsmooth hcalc (hMaj J) φ hφ e
      (fun v z => Ev v (e z)) U hUo hUd (fun v z hz => hUvaut v z (mem_iInter.mp hz v))
      (fun v test ht g => (hUvtest v J test ht g).restrict_domain hUo hUd (iInter_subset _ v))
      ⟨R₀, fun v z hz => hR₀s v (e z) fun α hα => (hR₀le v).trans_lt (hz α hα)⟩
      (fun v z => b v (e z)) Dbz hDbz.1 hDbz.2 hbz ψ hψaut
      (fun hJQ i => by obtain ⟨c', hc', -⟩ := hψproj J hJQ i; exact ⟨c', hc'⟩)
      (fun i z => coeff i (e z)) Dc hDc.1 hDc.2 hcoeffz
      (by obtain ⟨R₁, h⟩ := hint; exact ⟨R₁, fun z hz g => h (e z) hz g⟩)
  choose dataP hdataP using hPdata
  have hQdata := fun (J : StandardIndex F G fam.i fam.ν) =>
    fam.exists_identityWeyl_support Q J hExp hKQ hKmax hK0 hKlevi rho hsmooth hrho ψ hψaut
      (fun hJQ i test ht g => by
        obtain ⟨ψc, hp, -⟩ := hψproj J hJQ i
        exact (hp.2.2 test ht g).1)
  choose RQJ dataQ hdataQ using hQdata
  -- the finite set of exponent shifts
  let S : Set (Vstar fam.T) := ⋃ J : StandardIndex F G fam.i fam.ν,
    ((Set.range fun j => fam.chamberEmbedding J (parameterRealPart F (fam.P J)
      ((dataP J).offset j))) ∪ ⋃ i : Fin k, Set.range fun j =>
        fam.chamberEmbedding J (parameterRealPart F (fam.P J) ((dataQ J i).offset j)))
  have hS : S.Finite := Set.finite_iUnion fun J =>
    (Set.finite_range _).union (Set.finite_iUnion fun _ => Set.finite_range _)
  -- the comparison region
  let RQall : ℝ := ∑ J, |RQJ J| + ∑ i, |RQs i|
  have hRQJle : ∀ J, RQJ J ≤ RQall := fun J =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun J _ => abs_nonneg (RQJ J))
      (Finset.mem_univ J)).trans (le_add_of_nonneg_right
        (Finset.sum_nonneg fun i _ => abs_nonneg (RQs i))))
  have hRQsle : ∀ i, RQs i ≤ RQall := fun i =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (RQs i))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left
        (Finset.sum_nonneg fun J _ => abs_nonneg (RQJ J))))
  let O₀ : Set (Fin m → ℂ) := U ∩ Dbz ∩ Dc ∩ (⋂ i, UQ i) ∩
    {z | rQ.IsRegularParameter hAQ hT RQall (eQ z)}
  let EQ (lam : ComplexCharacterParameter F (fam.P I)) : Y :=
    ∑ i, coeff i lam • hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj lam)
  have hser : ∀ z ∈ O₀, ∀ i, EQc i (eQ z) =
      hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj (e z)) := by
    intro z hz i
    rw [← heQ]
    exact hRQs i (eQ z) fun α hα => (hRQsle i).trans_lt (hz.2 α hα)
  have hEsaut : ∀ z ∈ O₀, ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      Kinf rho (hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj (e z))) := by
    intro z hz i
    rw [← hser z hz i]
    exact hUQaut i z (mem_iInter.mp hz.1.2 i)
  have hAut : ∀ lam ∈ e '' O₀,
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (E' lam) ∧
        IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (EQ lam) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hE'aut z hz.1.1.1.1, ?_⟩
    exact Submodule.sum_mem (automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth hcalc)
      fun i _ => Submodule.smul_mem _ _ (hEsaut z hz i)
  have hExpansion : ∀ lam ∈ e '' O₀, ∀ J : StandardIndex F G fam.i fam.ν,
      ∃ left right : Y,
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J (E' lam)) left ∧
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J (EQ lam)) right ∧
        ∃ (s t u : Finset (ComplexCharacterParameter F (fam.P J)))
            (f g b : ComplexCharacterParameter F (fam.P J) → Y),
          fam.IsExponentDecomposition hsmooth Kinf rho J left s f ∧
          fam.IsExponentDecomposition hsmooth Kinf rho J right t g ∧
          left = right + ∑ exponent ∈ u, b exponent ∧
          ∀ exponent ∈ u, fam.HasUnnormalizedExponent J exponent (b exponent) ∧
            ∃ v : relativeWeylGroup fam.i, v ≠ QuotientGroup.mk n ∧
              (∀ α ∈ I.val, schemeWeylCharacterAction fam.i v α ∈
                positiveRelativeRoots fam.i fam.ν) ∧
              ∃ shift ∈ S, fam.chamberEmbedding J (parameterRealPart F (fam.P J) exponent) =
                relativeWeylRealCharacterAction fam.i v
                  (fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam)) + shift := by
    rintro _ ⟨z, hz, rfl⟩ J
    have hE'top : fam.IsAutomorphicOn hsmooth Kinf rho fam.top (E' (e z)) :=
      (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf _).mpr (hE'aut z hz.1.1.1.1)
    have hEQtop : fam.IsAutomorphicOn hsmooth Kinf rho fam.top (EQ (e z)) :=
      (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf _).mpr
        (hAut (e z) ⟨z, hz, rfl⟩).2
    have hEstop : ∀ i, fam.IsAutomorphicOn hsmooth Kinf rho fam.top
        (hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj (e z))) :=
      fun i => (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf _).mpr (hEsaut z hz i)
    obtain ⟨left, hl, -, sP, cP, hdl⟩ := hProj F G fam K hKmax hK0 hKlevi rho hsmooth hrho
      fam.top J (fam.le_top J) (E' (e z)) hE'top
    obtain ⟨right, hr, -, sQ, cQ, hdr⟩ := hProj F G fam K hKmax hK0 hKlevi rho hsmooth hrho
      fam.top J (fam.le_top J) (EQ (e z)) hEQtop
    let mu := weylParameter (fam.l I) c proj (e z)
    let ΛP : Set (ComplexCharacterParameter F (fam.P J)) :=
      Set.range fun j => (dataP J).label j (e z)
    let ΛQ : Set (ComplexCharacterParameter F (fam.P J)) :=
      {ν | ∃ i j, ν = (dataQ J i).label j mu}
    let ref (test : AdelicGroupPoints F (fam.M J) → ℂ) : Y := fun g =>
      fam.leviPairing J (fam.parabolicConstantTerm Q J
        (hKQ.parameterTwist (∑ i, coeff i (e z) • ψ i) mu)) g test
    have hPsupp : ∀ test, fam.IsLeviCuspForm Kinf rho J test →
        IsJointlySupportedIn (fam.splitComponentRepresentation J)
          ((fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
            parameterPower F (fam.P J) ν b.val) '' ΛP)
          (fun g => fam.leviPairing J (fam.constantTerm J (E' (e z))) g test - ref test g) := by
      intro test ht
      refine fam.pBracket_isJointlySupportedIn rho hsmooth Kinf hKQ ht (hdom J test ht) hl hdl
        ψ hψaut (hψdata J) (fun i => coeff i (e z)) mu ?_
      intro sv v hv hsum δ hδ hS
      exact hdataP J test ht z ⟨⟨hz.1.1.1.1, hz.1.1.1.2⟩, hz.1.1.2⟩ sv v hv hsum δ hδ
        (fun j hj => hS ⟨_, ⟨j, rfl⟩, hj.symm⟩)
    have hQsupp : ∀ test, fam.IsLeviCuspForm Kinf rho J test →
        IsJointlySupportedIn (fam.splitComponentRepresentation J)
          ((fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
            parameterPower F (fam.P J) ν b.val) '' ΛQ)
          (fun g => fam.leviPairing J (fam.constantTerm J (EQ (e z))) g test - ref test g) := by
      intro test ht
      have hreg : rQ.IsRegularParameter hAQ hT (RQJ J) mu := by
        intro α hα
        have h := hz.2 α hα
        rw [heQ] at h
        exact (hRQJle J).trans_lt h
      exact hdataQ J mu hreg hEstop (fun i test ht => by
          obtain ⟨ψc, hp, -⟩ := hProj F G fam K hKmax hK0 hKlevi rho hsmooth hrho fam.top J
            (fam.le_top J) _ (hEstop i)
          exact fun g => (hp.2.2 test ht g).1)
        (fun i => coeff i (e z)) test ht
    let Good (ν : ComplexCharacterParameter F (fam.P J)) : Prop :=
      ∃ v : relativeWeylGroup fam.i, v ≠ QuotientGroup.mk n ∧
        (∀ α ∈ I.val, schemeWeylCharacterAction fam.i v α ∈ positiveRelativeRoots fam.i fam.ν) ∧
        ∃ shift ∈ S, fam.chamberEmbedding J (parameterRealPart F (fam.P J) ν) =
          relativeWeylRealCharacterAction fam.i v
            (fam.chamberEmbedding I (parameterRealPart F (fam.P I) (e z))) + shift
    have hgood : ∀ ν ∈ ΛP ∪ ΛQ, Good ν := by
      rintro ν (⟨j, rfl⟩ | ⟨i, j, rfl⟩)
      · refine ⟨(dataP J).weyl j, (dataP J).competing j, (dataP J).positive j, _,
          mem_iUnion.mpr ⟨J, Or.inl ⟨j, rfl⟩⟩, ?_⟩
        dsimp only
        rw [show (dataP J).label j (e z) = (dataP J).linear j (e z) + (dataP J).offset j from rfl,
          map_add, map_add, (dataP J).ambient j (e z)]
      · have hpOver : Mono (fam.p I).hom.hom := by
          let := (fam.isCompatible I).parabolic.isClosedSubgroup.mono
          exact Over.mono_of_mono_left _
        let : Mono (fam.p I) := (Grp.forget _).mono_of_mono_map (f := fam.p I) hpOver
        have hTransport : fam.chamberEmbedding Q (parameterRealPart F (fam.P Q) mu) =
            relativeWeylRealCharacterAction fam.i (QuotientGroup.mk n)
              (fam.chamberEmbedding I (parameterRealPart F (fam.P I) (e z))) :=
          eisensteinAmbientWeylParameter F G (fam.P I) (fam.M I) (fam.P Q) (fam.M Q) fam.T fam.i
            (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) (fam.torus I) (fam.torus Q) proj n c
            (fam.torus_comp I) (fam.torus_comp Q) hproj hc (e z)
        refine ⟨(dataQ J i).weyl j * QuotientGroup.mk n, ?_, ?_, _,
          mem_iUnion.mpr ⟨J, Or.inr (mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩)⟩, ?_⟩
        · intro h
          exact (dataQ J i).competing j ((mul_eq_right.mp h).trans (QuotientGroup.mk_one _).symm)
        · intro α hα
          rw [map_mul, LinearEquiv.mul_apply]
          exact (dataQ J i).positive j _ (hIQ α hα)
        · rw [show (dataQ J i).label j mu = (dataQ J i).linear j mu + (dataQ J i).offset j from rfl,
            map_add, map_add, (dataQ J i).ambient j mu,
            hTransport, map_mul, LinearEquiv.mul_apply]
    obtain ⟨u, b, heq, hb⟩ := fam.exists_expansion_of_supported rho hsmooth Kinf (hdetect J)
      (fun f hf test ht => hdom J test ht f hf) hl hr hdl hdr ref ΛP ΛQ hPsupp hQsupp Good hgood
    exact ⟨left, right, hl, hr, sP, sQ, u, cP, cQ, b, hdl, hdr, heq, hb⟩
  have hinjective : ∀ (f g : Y) (L : StandardIndex F G fam.i fam.ν → Y),
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho f →
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho g →
      fam.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho f L →
      fam.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho g L → f = g :=
    fun f g L hf hg hLf hLg => hInj F G fam K hKmax hK0 hKlevi rho hsmooth hrho f g L hf hg hLf hLg
  obtain ⟨Rnl, hRnl⟩ := eq_of_weyl_cuspidal_expansions fam I Q hsmooth hcalc Kinf rho proj n c
    hproj hc hQI hinjective E' EQ (e '' O₀) S hS hAut hExpansion
  -- the final patch
  let Rf := max RQall (max R Rnl)
  let O : Set (Fin m → ℂ) := (U ∩ Dbz ∩ Dc ∩ (⋂ i, UQ i) ∩ e ⁻¹' DP) ∩
    {z | rQ.IsRegularParameter hAQ hT Rf (eQ z)}
  have hDPo : IsOpen (e ⁻¹' DP) := ((hEP 1).2 m e).1
  have hDPd : Dense (e ⁻¹' DP) := ((hEP 1).2 m e).2.1
  have hUQo' : IsOpen (⋂ i, UQ i) := isOpen_iInter_of_finite hUQo
  have hUQd' : Dense (⋂ i, UQ i) := dense_iInter_of_isOpen hUQo hUQd
  have hbaseo : IsOpen (U ∩ Dbz ∩ Dc ∩ (⋂ i, UQ i) ∩ e ⁻¹' DP) :=
    (((hUo.inter hDbz.1).inter hDc.1).inter hUQo').inter hDPo
  have hbased : Dense (U ∩ Dbz ∩ Dc ∩ (⋂ i, UQ i) ∩ e ⁻¹' DP) :=
    ((((hUd.inter_of_isOpen_right hDbz.2 hDbz.1).inter_of_isOpen_right hDc.2 hDc.1).inter_of_isOpen_right
      hUQd' hUQo').inter_of_isOpen_right hDPd hDPo)
  refine ⟨m, e, O, hbaseo.inter (rQ.isOpen_regularParameter_inCoordinates hAQ hT Rf eQ),
    hbased.inter_open_nonempty _ (rQ.isOpen_regularParameter_inCoordinates hAQ hT Rf eQ)
      (rQ.nonempty_regularParameter_inCoordinates hAQ hT Rf eQ) |>.mono fun z hz => ⟨hz.2, hz.1⟩,
    fun x hx => ?_⟩
  obtain ⟨⟨⟨⟨⟨hxU, hxDb⟩, hxDc⟩, hxUQ⟩, hxDP⟩, hxreg⟩ := hx
  have hreg' : ∀ R', R' ≤ Rf → rQ.IsRegularParameter hAQ hT R' (weylParameter (fam.l I) c proj (e x)) :=
    fun R' hR' α hα => by
      have h := hxreg α hα
      rw [heQ] at h
      exact hR'.trans_lt h
  refine ⟨hreg' R ((le_max_left _ _).trans (le_max_right _ _)), fun g => ?_⟩
  have hxO₀ : x ∈ O₀ := ⟨⟨⟨⟨hxU, hxDb⟩, hxDc⟩, hxUQ⟩, fun α hα => by
    have h := hxreg α hα
    exact (le_max_left _ _).trans_lt h⟩
  have hfin := hRnl (e x) ⟨x, hxO₀, rfl⟩ (hreg' Rnl ((le_max_right _ _).trans (le_max_right _ _)))
  rw [hEPeq x ⟨hxDP, hxU, hxDb⟩, hfin]
  simp only [EQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end StandardParabolicFamily

/-- The comparison on a regular patch for finite families, from its five inputs. A closed
embedding of size zero is replaced by a positive-size one with the same automorphic
functions. -/
theorem standardEisensteinFamilyComparisonReduction :
    StandardEisensteinFamilyComparisonReductionStatement.{u} := by
  intro hCont hInj hExp hProj hMaj F _ _ G _ _ _ fam I Q _ _ _ _ _ n c proj hproj hc hIQ hQI
    K hKI hKQ hKmax hK0 hKlevi N d rho hsmooth hcalc hrho _Kinf _rI _rQ _hAI _hAQ _hT p φ b Db
    hφ hb EP DP hEP hEPser k ψ coeff D hψ hcoeff hint R
  obtain ⟨N', rho', hN', hrho', htransfer⟩ :=
    Langlands.Automorphic.GroupSchemeFunctions.exists_positiveMatrixEmbedding_of_isClosedSubgroup
      rho hrho hsmooth hcalc
  exact fam.standardFamilyComparison_of_inputs I Q hCont hInj hExp hProj n c proj hproj hc hIQ
    hQI hKI hKQ hKmax hK0 hKlevi rho' hN' hrho' hsmooth hcalc
    (fun J ψ' hψ' g R' => hMaj F G fam K hKmax hK0 hKlevi rho' hrho' J ψ' hψ' g R')
    φ b Db (fun v => (htransfer _ _ (φ v)).mp (hφ v)) hb EP DP hEP hEPser ψ coeff D
    (fun i => (htransfer _ _ (ψ i)).mp (hψ i)) hcoeff hint R

open Langlands.Analysis.Meromorphic Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints Langlands.Aubert.General.RationalPointFamily in
/-- The comparison for one inducing form is the case of a family with one member and
coefficient `1`. -/
theorem standardEisensteinRegularComparison_of_family
    (h : StandardEisensteinFamilyComparisonStatement.{u}) :
    StandardEisensteinRegularComparisonStatement.{u} := by
  intro F _ _ G _ _ _ fam I Q _ _ _ _ _ n c proj hproj hc hIQ hQI K hKI hKQ hKmax hK0 hKlevi
    N d rho hsmooth hcalc hrho Kinf rI rQ hAI hAQ hT φ hφ EP DP hEP hEPser k ψ coeff D hψ
    hcoeff hint R
  have hone : IsMeromorphicInCoordinatesOn
      (fun _ : ComplexCharacterParameter F (fam.P I) => (1 : ℂ)) Set.univ :=
    ⟨(hEP 1).1, fun n e => by
      have h1 : DifferentiableOn ℂ (fun _ : Fin n → ℂ => (1 : ℂ)) Set.univ :=
        differentiableOn_const 1
      exact ⟨isOpen_univ, dense_univ, isHolomorphicOn_iff_differentiableOn_scalar.mpr h1,
        fun x => ⟨Set.univ, isOpen_univ, isConnected_univ, Set.mem_univ x, fun _ => 1,
          fun _ => 1, h1.mdifferentiableOn, ⟨x, Set.mem_univ x, one_ne_zero⟩,
          isHolomorphicOn_iff_differentiableOn_scalar.mpr h1, fun _ _ => one_smul _ _⟩⟩⟩
  obtain ⟨Rp, hRp⟩ := hEPser
  obtain ⟨Ri, hRi⟩ := hint
  exact h F G fam I Q n c proj hproj hc hIQ hQI K hKI hKQ hKmax hK0 hKlevi rho hsmooth hcalc hrho
    (p := 1) (fun _ => φ) (fun _ _ => 1) Set.univ (fun _ => hφ) (fun _ => hone) EP DP hEP
    ⟨Rp, fun lam hlam g => by simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
      hRp lam hlam]⟩ k ψ coeff D hψ hcoeff
    ⟨Ri, fun lam hlam g => by simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
      hRi lam hlam g]⟩ R

end Langlands.Global

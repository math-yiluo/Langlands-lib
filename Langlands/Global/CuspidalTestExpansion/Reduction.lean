import Langlands.Global.AdelicConvergentCuspidalTestExpansionReductionStatement
import Langlands.Global.EisensteinConstantTerm.Reduction
import Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingProof
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicStandardBruhatRepresentatives
import Langlands.Global.AdelicStandardBruhatPiece
import Langlands.Global.AdelicSelectedBruhatGeometry
import Langlands.Global.AdelicStandardBruhatParameter
import Langlands.Global.CuspidalTestExpansion.PieceExpansion
import Langlands.Global.CuspidalTestExpansion.ProperPiece
import Langlands.Global.CuspidalTestExpansion.FullPiece
import Langlands.Global.CuspidalTestExpansion.SelectedPiece
import Langlands.Global.AdelicWeightedLeviPairing
import Langlands.Global.AdelicEisensteinGlobalMajorant
import Langlands.Global.AdelicRootHyperplaneReduction
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicIntertwiningIdentity
import Langlands.Group.RelativeWeylMinimalityProof
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.Global.AdelicPositiveImageClosed

/-! # The convergent cuspidal test expansion from its analytic inputs

`Langlands.Global.convergentCuspidalTestExpansion_uniform_of_inputs` proves, from
`ConstantTermAutomorphyStatement`, `AutomorphicExponentDecompositionStatement` and
`LeviCuspFormRapidDecayStatement` (and the theorem `geometricLemmaUnfolding`), the scalar form
of Bernstein–Lapid (6.20) with a degree bound on the competing terms chosen before the parameter
and with integrable left-hand pairing integrands. `convergentCuspidalTestExpansion_of_inputs`
deduces `ConvergentCuspidalTestExpansionStatement`, and `convergentCuspidalTestExpansionReduction`
records this as a proof of `ConvergentCuspidalTestExpansionReductionStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily RealTorusSpace Langlands.Group.RelativeWeylIndexing
  Langlands.Automorphic.GroupSchemeFunctions

/-- The Levi pairing integrand of a finite sum is the sum of the integrands. -/
theorem StandardParabolicFamily.leviPairingIntegrand_finsetSum {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν) {β : Type*}
    (s : Finset β) (f : β → AdelicGroupPoints F G → ℂ) (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (g : AdelicGroupPoints F G) :
    fam.leviPairingIntegrand J (∑ i ∈ s, f i) g test =
      fun q => ∑ i ∈ s, fam.leviPairingIntegrand J (f i) g test q := by
  funext q
  simp only [StandardParabolicFamily.leviPairingIntegrand, Finset.sum_apply, Finset.sum_mul]

/-- Pairing with a Levi test is additive over finite sums of functions whose pairing integrands
are integrable. -/
theorem StandardParabolicFamily.leviPairing_finsetSum_of_integrable {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν) {β : Type*}
    (s : Finset β) (f : β → AdelicGroupPoints F G → ℂ) (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (g : AdelicGroupPoints F G)
    (hf : ∀ i ∈ s, Integrable (fam.leviPairingIntegrand J (f i) g test)
      (normOneRationalQuotientHaarMeasure F (fam.M J))) :
    fam.leviPairing J (∑ i ∈ s, f i) g test = ∑ i ∈ s, fam.leviPairing J (f i) g test := by
  unfold StandardParabolicFamily.leviPairing
  rw [fam.leviPairingIntegrand_finsetSum J s f test g]
  exact integral_finsetSum s hf

set_option maxHeartbeats 4000000 in
/-- Bernstein–Lapid (6.20) in the convergence region, in the form of
`ConvergentCuspidalTestExpansionStatement` with two additions: one bound `deg` on the polynomial
degree of all competing terms, chosen before the parameter `λ`, and the absolute integrability
of the pairing integrands of the two tested terms on the left. The integration identity of the
geometric lemma is the theorem `geometricLemmaUnfolding`. -/
theorem convergentCuspidalTestExpansion_uniform_of_inputs
    (hAut : ConstantTermAutomorphyStatement.{u})
    (hDec : AutomorphicExponentDecompositionStatement.{u})
    (hDecay : LeviCuspFormRapidDecayStatement.{u}) :
    ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I),
    IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c →
    let w : relativeWeylGroup fam.i := QuotientGroup.mk n
    (∀ alpha ∈ I.val, schemeWeylCharacterAction fam.i w alpha ∈ Q.val) →
    (∀ alpha ∈ Q.val, schemeWeylCharacterAction fam.i w⁻¹ alpha ∈ I.val) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν,
        IsMaximalCompactSubgroup F (fam.M J)
          (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom),
        IsClosedSubgroup rho →
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ phi : AdelicGroupPoints F G → ℂ, fam.IsAutomorphicOn hsmooth Kinf rho I phi →
          ∀ J : StandardIndex F G fam.i fam.ν,
            ∃ (R : ℝ) (data : CompetingWeylExponents fam I J w) (deg : ℕ),
              ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
                ∃ terms : Fin data.size → AdelicGroupPoints F G → ℂ,
                  (∀ k, fam.HasPolynomialOrbit J (data.label k lam) deg (terms k)) ∧
                  ∀ test : AdelicGroupPoints F (fam.M J) → ℂ, fam.IsLeviCuspForm Kinf rho J test →
                    ∀ g : AdelicGroupPoints F G,
                      Integrable (fam.leviPairingIntegrand J
                          (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
                      Integrable (fam.leviPairingIntegrand J (fam.parabolicConstantTerm Q J
                          (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q)
                            n.val phi lam)) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
                      (∀ k, Integrable (fam.leviPairingIntegrand J (terms k) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
                      fam.leviPairing J (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test -
                          fam.leviPairing J (fam.parabolicConstantTerm Q J
                            (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q)
                              n.val phi lam)) g test =
                        ∑ k, fam.leviPairing J (terms k) g test := by
  have hGLU : GeometricLemmaUnfoldingStatement.{u} := geometricLemmaUnfolding
  intro F _ _ G _ _ _ fam I Q _ _ _ n c hW w hwI hwQ K hK hKmax hK0 hKlevi N d rho hsmooth hrho
    Kinf r hA hT φ hφ J
  classical
  -- the Coxeter system of the relative Weyl group
  obtain ⟨-, hSfin, CM, cs, hcs⟩ := relativeWeylCoxeter F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic
  let PI := fam.simpleRootsOfIndex I
  let PJ := fam.simpleRootsOfIndex J
  have hPI : rootSet fam.i fam.ν PI = I.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex I)
  have hPJ : rootSet fam.i fam.ν PJ = J.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex J)
  obtain ⟨lift, hlift, hliftn, hreps⟩ :=
    fam.exists_standardBruhatRepresentatives cs PI PJ I J n hcs hPI hPJ
  let Wm := {v : relativeWeylGroup fam.i // IsMinimal cs PJ PI v}
  let Iv : Wm → StandardIndex F G fam.i fam.ν :=
    fun v => fam.indexOfSimpleRoots (intersectionSubset cs PJ PI v.val)
  let Jv : Wm → StandardIndex F G fam.i fam.ν :=
    fun v => fam.indexOfSimpleRoots (intersectionSubset cs PI PJ v.val⁻¹)
  have hpiece : ∀ v : Wm, Nonempty (StandardParabolicFamily.StandardBruhatPiece fam I J (Iv v) (Jv v)
      (lift v)) := by
    intro v
    have hv : (QuotientGroup.mk (lift v) : relativeWeylGroup fam.i) = v.val := hlift v
    have hmin : IsMinimal cs PJ PI (QuotientGroup.mk (lift v) : relativeWeylGroup fam.i) := by
      rw [hv]; exact v.property
    have h := fam.standardBruhatPiece (lift v) cs PI PJ hcs hmin
    rw [fam.indexOfSimpleRoots_simpleRootsOfIndex I, fam.indexOfSimpleRoots_simpleRootsOfIndex J]
      at h
    simp only [hv] at h
    exact h
  let piece := fun v : Wm => (hpiece v).some
  have instF : ∀ v : Wm,
      IsClosedImmersion ((piece v).source.inclusion ≫ fam.p I).hom.hom.left := fun v => by
    rw [(piece v).source.inclusion_comp]
    exact (fam.isCompatible (Iv v)).parabolic.isClosedSubgroup
  have instFU : ∀ v : Wm, IsClosedImmersion
      (fam.iU (Iv v) ≫ (piece v).source.inclusion ≫ fam.p I).hom.hom.left := fun v => by
    rw [(piece v).source.inclusion_comp]
    exact fam.closedU (Iv v)
  have instGV : ∀ v : Wm, IsClosedImmersion
      (fam.iU (Jv v) ≫ (piece v).target.inclusion ≫ fam.p J).hom.hom.left := fun v => by
    rw [(piece v).target.inclusion_comp]
    exact fam.closedU (Jv v)
  have hK0' : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K := by
    have h0 : fam.indexOfSimpleRoots ∅ = ⟨∅, Set.empty_subset _⟩ :=
      Subtype.ext (rootSet_empty fam.i fam.ν)
    rw [h0]
    exact hK0
  have hconst := eisensteinConstantTerm_of_convergence_of_unfolding eisensteinAbsoluteConvergence
    hGLU F G (fam.P I) (fam.M I) (fam.U I) (fam.P J) (fam.U J) (fam.A I) (fam.p I) (fam.iU I)
    (fam.l I) (fam.a I) r hA hT (fam.p J) (fam.iU J) Wm (fun v => (lift v).val)
    (fun v => fam.P (Iv v)) (fun v => fam.U (Iv v)) (fun v => fam.P (Jv v)) (fun v => fam.U (Jv v))
    (fun v => (piece v).source.inclusion) (fun v => fam.iU (Iv v))
    (fun v => (piece v).target.inclusion) (fun v => fam.iU (Jv v))
    fam.connectedReductive (fam.isUnipotentRadical I) (fam.isCompatible J).parabolic
    (fam.isUnipotentRadical J) hreps
    (fun v => by rw [(piece v).source.inclusion_comp]; exact (fam.isCompatible (Iv v)).parabolic)
    (fun v => fam.isUnipotentRadical (Iv v))
    (fun v => by rw [(piece v).target.inclusion_comp]; exact (fam.isCompatible (Jv v)).parabolic)
    (fun v => fam.isUnipotentRadical (Jv v)) (fun v => (piece v).geometry) K hK
    (fun v => ((piece v).iwasawa K hK0').1) rho hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth) φ hKmax hrho hφ
  obtain ⟨R₀, hR₀⟩ := hconst
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- rank zero: the adelic points are trivial, so is the relative Weyl group, there are no simple
    -- roots, and the Eisenstein series and the selected intertwining integral are both `φ_λ`
    subst hN0
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    have hratsub : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :=
      ⟨fun a b => ((rational_injective F G).comp
        (Langlands.GroupScheme.GaloisPointComparison.rationalCoeffEquiv F G).injective)
        (Subsingleton.elim _ _)⟩
    have hWsub : ∀ a b : relativeWeylGroup fam.i, a = b := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim x y]
    have hempty : IsEmpty (SimpleRoot fam.i fam.ν) := ⟨fun a => by
      have h := cs.length_simple a
      rw [hWsub (cs.simple a) 1, cs.length_one] at h
      exact zero_ne_one h⟩
    have hJQ : J ≤ Q := fun α hα => (hempty.false ⟨α, J.2 hα⟩).elim
    have hQI : Q = I := Subtype.ext (Set.ext fun α =>
      ⟨fun h => (hempty.false ⟨α, Q.2 h⟩).elim, fun h => (hempty.false ⟨α, I.2 h⟩).elim⟩)
    let data0 : CompetingWeylExponents fam I J w :=
      { size := 0
        weyl := Fin.elim0
        linear := Fin.elim0
        offset := Fin.elim0
        competing := fun k => Fin.elim0 k
        positive := fun k => Fin.elim0 k
        ambient := fun k => Fin.elim0 k }
    -- every pairing integrand is integrable: `M_J(𝔸)` and its norm-one quotient are points
    have hint0 : ∀ (f : AdelicGroupPoints F G → ℂ) (test : AdelicGroupPoints F (fam.M J) → ℂ)
        (g : AdelicGroupPoints F G), Integrable (fam.leviPairingIntegrand J f g test)
          (normOneRationalQuotientHaarMeasure F (fam.M J)) := by
      intro f test g
      have hcJ := fam.isCompatible J
      have hjc : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
        hcJ.levi.isClosedSubgroup.comp hcJ.parabolic.isClosedSubgroup
      have : IsClosedImmersion (fam.l J ≫ fam.p J).hom.hom.left := hjc
      have : IsAffine (fam.M J).X.left := isAffine_of_isAffineHom (fam.l J ≫ fam.p J).hom.hom.left
      have hMsub : Subsingleton (AdelicGroupPoints F (fam.M J)) :=
        ⟨fun a b => (isClosedEmbedding_map F (fam.M J) G (fam.l J ≫ fam.p J)).injective
          (Subsingleton.elim _ _)⟩
      have hQsub : Subsingleton (NormOneRationalQuotient F (fam.M J)) := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ a
        obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective _ b
        rw [Subsingleton.elim x y]⟩
      have hconst : fam.leviPairingIntegrand J f g test =
          fun _ => fam.leviPairingIntegrand J f g test (LeftCosetSpace.mk _ 1) :=
        funext fun q => congrArg _ (Subsingleton.elim q _)
      rw [hconst]
      exact integrable_const _
    refine ⟨R₀, data0, 0, fun lam _ => ⟨Fin.elim0, fun k => Fin.elim0 k, fun test _ g =>
      ⟨hint0 _ _ _, hint0 _ _ _, fun k => Fin.elim0 k, ?_⟩⟩⟩
    have hphiU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) (fam.iU I)) φ := by
      rintro _ ⟨y, rfl⟩ x
      exact hφ.1 _ (Subgroup.mem_sup_left ⟨y, rfl⟩) x
    have hEI : hK.eisensteinSeries φ lam =
        hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam := by
      funext y
      have hn1 : n.val = 1 := Subsingleton.elim _ _
      rw [hn1]
      subst hQI
      rw [hK.intertwiningIntegral_one_self (fam.iU Q) (fam.isUnipotentRadical Q) φ hphiU lam y]
      let c₀ : ParabolicRationalCosets F (fam.p Q) := Quotient.mk _ 1
      have hc (c : ParabolicRationalCosets F (fam.p Q)) : c = c₀ :=
        Quotient.inductionOn c fun x => congrArg _ (Subtype.ext (Subsingleton.elim _ _))
      unfold IsIwasawaCompact.eisensteinSeries
      rw [tsum_eq_single c₀ fun c hc' => absurd (hc c) hc']
      unfold IsIwasawaCompact.eisensteinTerm
      rw [Subsingleton.elim (((Quotient.out c₀ : rationalSubgroup F G) : AdelicGroupPoints F G) * y) y]
    rw [Finset.univ_eq_empty, Finset.sum_empty, sub_eq_zero]
    unfold StandardParabolicFamily.parabolicConstantTerm
    simp only [hJQ, ↓reduceIte]
    rw [hEI]
  have hφc : Continuous φ := hφ.2.1.1
  have hφinv := hφ.1
  have hφgrowth := hφ.2.2.2.2
  obtain ⟨R₁, hmaj⟩ := eisensteinGlobalMajorant F G (fam.P I) (fam.M I) (fam.U I) (fam.A I)
    (fam.p I) (fam.iU I) (fam.l I) (fam.a I) r hA hT fam.connectedReductive
    (fam.isUnipotentRadical I) hK rho hN hrho φ hφinv hφgrowth
  -- the simple roots of `Q` and the selected Weyl class
  let : Fintype (SimpleRoot fam.i fam.ν) := Fintype.ofFinite _
  let PQ := fam.simpleRootsOfIndex Q
  have hPQ : rootSet fam.i fam.ν PQ = Q.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex Q)
  let wW : relativeWeylGroup fam.i := QuotientGroup.mk n
  have hsel := selectedBruhatGeometry fam.i fam.ν cs hT hcs PI PQ wW
    (by rw [hPI, hPQ]; exact hwI) (by rw [hPQ, hPI]; exact hwQ)
  have hidx : ∀ A B : Finset (SimpleRoot fam.i fam.ν),
      fam.indexOfSimpleRoots A = fam.indexOfSimpleRoots B → A = B := fun A B h =>
    Finset.Subset.antisymm ((fam.indexOfSimpleRoots_le A B).mp h.le)
      ((fam.indexOfSimpleRoots_le B A).mp h.ge)
  have hJQiff : J ≤ Q ↔ PJ ⊆ PQ := by
    rw [← fam.indexOfSimpleRoots_le, fam.indexOfSimpleRoots_simpleRootsOfIndex,
      fam.indexOfSimpleRoots_simpleRootsOfIndex]
  have hJv_le : ∀ v : Wm, Jv v ≤ J := fun v => by
    have h := (fam.indexOfSimpleRoots_le _ _).mpr (intersectionSubset_subset cs PI PJ v.val⁻¹)
    rwa [fam.indexOfSimpleRoots_simpleRootsOfIndex] at h
  -- full-target pieces and their exponent data
  let FullV := {v : Wm // J = Jv v}
  have hFP := fun v : FullV => fam.fullPiece_expansion hAut hDec (piece v.1) v.2
    ((piece v.1).iwasawa K hK0').1 hKmax hK0 hKlevi rho hsmooth hrho φ hφ
  choose sv offv cv πv kv hπv hWv hTv using hFP
  let FullComp := {v : FullV // ¬ (J ≤ Q ∧ v.1.val = wW)}
  let Ix := Σ v : FullComp, {ν // ν ∈ sv v.1}
  let e := Fintype.equivFin Ix
  let data : CompetingWeylExponents fam I J wW :=
    { size := Fintype.card Ix
      weyl := fun k => (e.symm k).1.1.1.val
      linear := fun k => (weylParameter (fam.l (Iv (e.symm k).1.1.1)) (cv (e.symm k).1.1)
        (πv (e.symm k).1.1)).comp (parameterRestrict (piece (e.symm k).1.1.1).source.inclusion)
      offset := fun k => weylParameter (fam.l (Iv (e.symm k).1.1.1)) (cv (e.symm k).1.1)
        (πv (e.symm k).1.1) (e.symm k).2.val + offv (e.symm k).1.1
      competing := fun k h => by
        apply (e.symm k).1.2
        refine ⟨?_, h⟩
        have hmin : IsMinimal cs PJ PI wW := h ▸ (e.symm k).1.1.1.2
        have hJv := (e.symm k).1.1.2
        have h1 : intersectionSubset cs PI PJ wW⁻¹ = PJ := by
          apply hidx
          rw [fam.indexOfSimpleRoots_simpleRootsOfIndex, ← h]
          exact hJv.symm
        exact hJQiff.mpr ((hsel.2.1 PJ hmin).mp h1)
      positive := fun k alpha halpha => by
        have halpha' : alpha ∈ rootSet fam.i fam.ν PI := by rw [hPI]; exact halpha
        obtain ⟨a, ha, rfl⟩ := halpha'
        have hlen := ((minimalityLengthCriterion_proof cs PJ PI _).mp
          (e.symm k).1.1.1.2).2 a ha
        exact (hcs.2.2.1 _ a).mp hlen
      ambient := fun k lam => by
        have h := StandardParabolicFamily.standardBruhatParameter fam I (Iv (e.symm k).1.1.1) J
          (piece (e.symm k).1.1.1).source.inclusion (lift (e.symm k).1.1.1) (cv (e.symm k).1.1)
          (πv (e.symm k).1.1) (piece (e.symm k).1.1.1).source.inclusion_comp
          (hπv (e.symm k).1.1) (hWv (e.symm k).1.1) lam
        have hl : (QuotientGroup.mk (lift (e.symm k).1.1.1) : relativeWeylGroup fam.i) =
            (e.symm k).1.1.1.val := hlift _
        rw [hl] at h
        exact h }
  refine ⟨max R₀ R₁, data, Finset.univ.sup kv, fun lam hlam => ?_⟩
  obtain ⟨b, dd, hb, hb0, hdd, hbound⟩ :=
    hmaj lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_right R₀ R₁) hlam)
  have hR := hR₀ lam
    (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_left R₀ R₁) hlam)
  have hPP := fun v : Wm => fam.pieceIntegral_properties hGLU (piece v) hK
    ((piece v).iwasawa K hK0').1 rho hN hφc hφinv lam b dd hb hb0 hdd hbound
  have hT' := fun v : FullV => hTv v lam (hPP v.1).1
  choose Tv hTsum hTexp hTspan using hT'
  let Pint : Wm → AdelicGroupPoints F G → ℂ := fun v =>
    ((piece v).iwasawa K hK0').1.intertwiningIntegral (fam.iU (Iv v))
      (fam.iU (Jv v) ≫ (piece v).target.inclusion ≫ fam.p J) (lift v).val
      (subgroupConstantTerm F (fam.iU (Iv v) ≫ (piece v).source.inclusion ≫ fam.p I) φ)
      (parameterRestrict (piece v).source.inclusion lam)
  have hTsum' : ∀ v : FullV, Pint v.1 = ∑ ν ∈ sv v, Tv v ν := hTsum
  have hTspan' : ∀ v : FullV, ∀ ν ∈ sv v, Tv v ν ∈ fam.translateSpan J (Pint v.1) := hTspan
  refine ⟨fun k => Tv (e.symm k).1.1 (e.symm k).2.val, fun k => ?_, fun test htest g => ?_⟩
  · have h := hTexp (e.symm k).1.1 (e.symm k).2.val (e.symm k).2.property
    rw [map_add, add_comm (weylParameter _ _ _ _) (weylParameter _ _ _ _), add_assoc] at h
    exact StandardParabolicFamily.HasPolynomialOrbit.mono h (Finset.le_sup (Finset.mem_univ _))
  · obtain ⟨B, hB0, hBdecay⟩ := hDecay F G fam K hKmax hK0 hKlevi rho hN hrho J test htest dd hdd
    have htc : Continuous test := htest.1.2.1.1
    have hti : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) test := htest.1.1
    let S : Wm → AdelicGroupPoints F G → ℂ := fun v y =>
      ∑' c : RelativeRationalCosets F ((piece v).target.inclusion ≫ fam.p J) (fam.p J),
        Pint v ((c.out : AdelicGroupPoints F G) * y)
    have hCE : fam.constantTerm J (hK.eisensteinSeries φ lam) = ∑ v, S v := by
      funext y
      rw [Finset.sum_apply]
      exact (hR y).2.2
    -- pieces with full target
    have hdomFull : ∀ v : FullV, Pint v.1 ∈ fam.leviPairingDomain J test := by
      intro v g'
      obtain ⟨C, hC, hCb⟩ := (hPP v.1).2.2.2.1
      have hle : rationalImage F (fam.l J ≫ fam.p J) ≤
          rationalImage F ((piece v.1).target.inclusion ≫ fam.p J) := by
        refine (rationalImage_comp_le (fam.l J) (fam.p J)).trans
          (rationalImage_le_of_range_le _ _ ?_)
        rw [(piece v.1).target.inclusion_comp, ← v.2]
      exact StandardParabolicFamily.weightedLeviPairingIntegrability fam J rho hN (Pint v.1) (hPP v.1).2.2.1
        (fun z hz x => (hPP v.1).2.2.2.2 z (hle hz) x) C dd hC hdd hCb test htc hti
        ⟨B, hB0, hBdecay⟩ g'
    have hS_full : ∀ v : FullV, S v.1 = Pint v.1 := fun v => funext fun y =>
      fam.fullPiece_series (piece v.1).target v.2 (Pint v.1) (hPP v.1).2.2.2.2 y
    have hspan_dom : ∀ v : FullV,
        fam.translateSpan J (Pint v.1) ≤ fam.leviPairingDomain J test := by
      intro v
      apply Submodule.span_le.mpr
      rintro _ ⟨b', rfl⟩
      exact fam.splitComponent_mem_leviPairingDomain J test b' (hdomFull v)
    -- pieces with proper target
    have hΦc : Continuous (hK.parameterTwist φ lam) := hK.continuous_parameterTwist hφc lam
    have hΦP := (fam.parameterTwist_isLeftInvariant hK hφinv lam).2
    have hVn : (SubgroupFunctor.range (fam.iU J)).IsNormal := (fam.isUnipotentRadical J).1.isNormal
    have hcpt := fam.compactSpace_radicalRationalQuotient J
    obtain ⟨Cabs, hCabs0, hCabs⟩ := eisensteinBruhatAbsoluteBound (fam.p I) (fam.p J) (fam.iU J)
      (fun v : Wm => (lift v).val)
      (fun v => rationalImage F ((piece v).target.inclusion ≫ fam.p J)) rho hN hreps
      (fun v => (piece v).geometry.rationalImage_right) hVn hcpt (hK.parameterTwist φ lam) hΦc
      hΦP b dd hb hb0 hdd hbound
    have hAbs : ∀ v : Wm, ∀ y, ∑' c : RelativeRationalCosets F
        ((piece v).target.inclusion ≫ fam.p J) (fam.p J),
        ‖Pint v ((c.out : AdelicGroupPoints F G) * y)‖ₑ ≤
          ENNReal.ofReal (Cabs * RepresentationGrowth.adelicHeight F G rho y ^ dd) := by
      intro v y
      refine (ENNReal.tsum_le_tsum fun c => ?_).trans (hCabs y v)
      have h1 : Pint v ((c.out : AdelicGroupPoints F G) * y) =
          stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) (innerAdelicPoint F G (lift v).val)
            (hK.parameterTwist φ lam) ((c.out : AdelicGroupPoints F G) * y) := (hPP v).2.1 _
      rw [h1]
      exact enorm_integral_le_lintegral_enorm _
    have hCTinv : ∀ v : Wm, IsLeftInvariantUnder F G
        (parabolicUnipotentImage F (fam.p (Iv v)) (fam.iU (Iv v))) (fam.constantTerm (Iv v) φ) := by
      intro v
      have hIv : Iv v ≤ I := by
        have h := (fam.indexOfSimpleRoots_le _ _).mpr (intersectionSubset_subset cs PJ PI v.val)
        rwa [fam.indexOfSimpleRoots_simpleRootsOfIndex] at h
      have hA' := hAut F G fam Kinf rho hsmooth hrho I (Iv v) hIv φ hφ
      rintro _ ⟨y, rfl⟩ x
      exact hA'.1 _ (Subgroup.mem_sup_left ⟨y, rfl⟩) x
    have hProper : ∀ v : Wm, ¬ (J = Jv v) →
        Integrable (fam.leviPairingIntegrand J (S v) g test)
          (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
        fam.leviPairing J (S v) g test = 0 := by
      intro v hv
      have hlt : Jv v < J := lt_of_le_of_ne (hJv_le v) (Ne.symm hv)
      exact (piece v).target.properPiece_pairing hlt rho hN Kinf (Pint v) (hPP v).2.2.1
        (hPP v).2.2.2.2 (fun u hu y => fam.pieceIntegral_radical_invariant (piece v)
          ((piece v).iwasawa K hK0').1 φ (hCTinv v) lam u hu y)
        Cabs dd hCabs0 hdd (hAbs v) test htest B hBdecay g
    have hSint : ∀ v : Wm, Integrable (fam.leviPairingIntegrand J (S v) g test)
        (normOneRationalQuotientHaarMeasure F (fam.M J)) := by
      intro v
      by_cases hv : J = Jv v
      · rw [hS_full ⟨v, hv⟩]
        exact hdomFull ⟨v, hv⟩ g
      · exact (hProper v hv).1
    have hTint : ∀ v : FullV, ∀ ν ∈ sv v, Integrable (fam.leviPairingIntegrand J (Tv v ν) g test)
        (normOneRationalQuotientHaarMeasure F (fam.M J)) := fun v ν hν =>
      hspan_dom v (hTspan' v ν hν) g
    have hCEint : Integrable (fam.leviPairingIntegrand J
        (fam.constantTerm J (hK.eisensteinSeries φ lam)) g test)
        (normOneRationalQuotientHaarMeasure F (fam.M J)) := by
      rw [hCE, fam.leviPairingIntegrand_finsetSum J Finset.univ S test g]
      exact integrable_finsetSum _ fun v _ => hSint v
    have hRHS : ∑ k, fam.leviPairing J (Tv (e.symm k).1.1 (e.symm k).2.val) g test =
        ∑ v : FullComp, fam.leviPairing J (S v.1.1) g test := by
      rw [Equiv.sum_comp e.symm (fun x : Ix => fam.leviPairing J (Tv x.1.1 x.2.val) g test),
        Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_coe_sort (sv v.1) (fun ν => fam.leviPairing J (Tv v.1 ν) g test),
        hS_full v.1, hTsum' v.1,
        fam.leviPairing_finsetSum_of_integrable J (sv v.1) (Tv v.1) test g (hTint v.1)]
    have hsplit1 : ∑ v : Wm, fam.leviPairing J (S v) g test =
        ∑ v : FullV, fam.leviPairing J (S v.1) g test := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun v : Wm => J = Jv v)
        (fun v => fam.leviPairing J (S v) g test)]
      have h0 : ∑ v : {v : Wm // ¬ J = Jv v}, fam.leviPairing J (S v.1) g test = 0 :=
        Finset.sum_eq_zero (fun v _ => (hProper v.1 v.2).2)
      rw [h0, add_zero]
    have hsplit2 : ∑ v : FullV, fam.leviPairing J (S v.1) g test =
        ∑ v : {v : FullV // J ≤ Q ∧ v.1.val = wW}, fam.leviPairing J (S v.1.1) g test +
          ∑ v : FullComp, fam.leviPairing J (S v.1.1) g test :=
      (Fintype.sum_subtype_add_sum_subtype (fun v : FullV => J ≤ Q ∧ v.1.val = wW)
        (fun v => fam.leviPairing J (S v.1) g test)).symm
    have hselsum : Integrable (fam.leviPairingIntegrand J (fam.parabolicConstantTerm Q J
          (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam)) g test)
          (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
        ∑ v : {v : FullV // J ≤ Q ∧ v.1.val = wW}, fam.leviPairing J (S v.1.1) g test =
        fam.leviPairing J (fam.parabolicConstantTerm Q J
          (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam)) g test := by
      by_cases hJQ : J ≤ Q
      · have hPJQ := hJQiff.mp hJQ
        have hmin₀ : IsMinimal cs PJ PI wW := hsel.1 PJ hPJQ
        let v₀ : Wm := ⟨wW, hmin₀⟩
        have hfull₀ : J = Jv v₀ := by
          show J = fam.indexOfSimpleRoots (intersectionSubset cs PI PJ wW⁻¹)
          rw [(hsel.2.1 PJ hmin₀).mpr hPJQ, fam.indexOfSimpleRoots_simpleRootsOfIndex]
        let x₀ : {v : FullV // J ≤ Q ∧ v.1.val = wW} := ⟨⟨v₀, hfull₀⟩, hJQ, rfl⟩
        have hminQ : IsMinimal cs PQ PI wW := hsel.1 PQ subset_rfl
        have hQpiece := fam.standardBruhatPiece n cs PI PQ hcs hminQ
        rw [fam.indexOfSimpleRoots_simpleRootsOfIndex I,
          fam.indexOfSimpleRoots_simpleRootsOfIndex Q] at hQpiece
        let pcQ := hQpiece.some
        have hI₂ : I = fam.indexOfSimpleRoots (intersectionSubset cs PQ PI wW) := by
          rw [hsel.2.2, fam.indexOfSimpleRoots_simpleRootsOfIndex]
        have hQ₂ : Q = fam.indexOfSimpleRoots (intersectionSubset cs PI PQ wW⁻¹) := by
          rw [(hsel.2.1 PQ hminQ).mpr subset_rfl, fam.indexOfSimpleRoots_simpleRootsOfIndex]
        have hn₀ : n = lift v₀ := (hliftn v₀ rfl).symm
        have hEqSel : fam.parabolicConstantTerm Q J
            (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) = Pint v₀ := by
          unfold StandardParabolicFamily.parabolicConstantTerm
          simp only [hJQ, ↓reduceIte]
          funext y
          exact fam.selectedPiece_constantTerm hGLU (piece v₀) hn₀ hfull₀ pcQ hI₂ hQ₂ hJQ hK
            ((piece v₀).iwasawa K hK0').1 (pcQ.iwasawa K hK0').1 rho hN hφc hφinv lam b dd hb hb0
            hdd hbound y
        refine ⟨by rw [hEqSel]; exact hdomFull ⟨v₀, hfull₀⟩ g, ?_⟩
        rw [Fintype.sum_eq_single x₀ (fun x hx =>
          absurd (Subtype.ext (Subtype.ext (Subtype.ext x.2.2))) hx)]
        change fam.leviPairing J (S v₀) g test = _
        rw [hS_full ⟨v₀, hfull₀⟩, hEqSel]
      · have hEq0 : fam.parabolicConstantTerm Q J
            (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) = 0 := by
          unfold StandardParabolicFamily.parabolicConstantTerm
          simp only [hJQ, ↓reduceIte]
        rw [hEq0]
        refine ⟨(fam.leviPairingDomain J test).zero_mem g, ?_⟩
        rw [Finset.sum_eq_zero (fun v _ => (hJQ v.2.1).elim)]
        simp [StandardParabolicFamily.leviPairing, StandardParabolicFamily.leviPairingIntegrand]
    refine ⟨hCEint, hselsum.1, fun k => hTint _ _ (e.symm k).2.property, ?_⟩
    rw [hCE, fam.leviPairing_finsetSum_of_integrable J Finset.univ S test g (fun v _ => hSint v), hRHS,
      hsplit1, hsplit2, hselsum.2]
    ring

/-- `ConvergentCuspidalTestExpansionStatement` from its three analytic inputs: forget the degree
bound and the integrability of the left-hand integrands in
`convergentCuspidalTestExpansion_uniform_of_inputs`. -/
theorem convergentCuspidalTestExpansion_of_inputs
    (hAut : ConstantTermAutomorphyStatement.{u})
    (hDec : AutomorphicExponentDecompositionStatement.{u})
    (hDecay : LeviCuspFormRapidDecayStatement.{u}) :
    ConvergentCuspidalTestExpansionStatement.{u} := by
  intro F _ _ G _ _ _ fam I Q _ _ _ n c hW w hwI hwQ K hK hKmax hK0 hKlevi N d rho hsmooth hrho
    Kinf r hA hT φ hφ J
  obtain ⟨R, data, deg, h⟩ := convergentCuspidalTestExpansion_uniform_of_inputs hAut hDec
    hDecay F G fam I Q n c hW hwI hwQ K hK hKmax hK0 hKlevi rho hsmooth hrho φ hφ J
  refine ⟨R, data, fun lam hlam => ?_⟩
  obtain ⟨terms, hexp, htest⟩ := h lam hlam
  exact ⟨terms, fun k => ⟨deg, hexp k⟩, fun test ht g =>
    ⟨(htest test ht g).2.2.1, (htest test ht g).2.2.2⟩⟩

/-- The implication `ConvergentCuspidalTestExpansionReductionStatement`. -/
theorem convergentCuspidalTestExpansionReduction :
    ConvergentCuspidalTestExpansionReductionStatement.{u} :=
  convergentCuspidalTestExpansion_of_inputs

end Langlands.Global

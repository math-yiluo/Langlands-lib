import Langlands.GroupScheme.SubgroupFunctorProduct
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermFourierModelTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardLeviConstantTerm

/-! # Fourier evaluation in the nested constant-term diagram of VIII.2.1 -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

local instance nestedFourierAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance nestedFourierFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

local instance nestedFourierCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance nestedFourierParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

private theorem nestedFourierLeviCompactOpen (p : SemistandardSpectralIndex i)
    (d : CompactData p) : Nonempty (CompactOpenSubgroup (levi p)) := by
  obtain ⟨L, hLc, _⟩ := compactOpenCofinal p d ⊤
  exact ⟨⟨L, hLc⟩⟩

section Evaluation

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (p : SemistandardSpectralIndex i) (m : LeviModel p) (d : CompactData p)
  (hdelta : ModularNormalization p)
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (muM : Measure (levi p ⧸ C)) [muM.IsHaarMeasure] [muM.IsInvInvariant]
  (hsqPi : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation muM)
  (hT : ∀ A : UnitaryOrbitRepresentative m.normCharacters pi,
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.val.obj).representation)
  (muL : Measure (levi p)) (muU : Measure (radical p)) (XiM sigmaM : levi p → ℝ)
  (hin : RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
    p m d pi muL muU XiM sigmaM)

/-- Evaluation of the actual normalized product-induced function on both
arguments, in the inducing coefficient tensor. -/
abbrev semistandardCoefficientEval {p : SemistandardSpectralIndex i}
    {A : SmoothRep.{0, u, uV} ℂ (levi p)}
    (v : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A)
    (x : rationalPoints G × rationalPoints G) : CoefficientTensor A :=
  Induction.eval ((parabolic p).prod (parabolic p))
    (inducingRepresentation ((decomposition p).prod (decomposition p))
      ((isClosed_radical p).prod (isClosed_radical p)) (productLeviObject A A.contragredient)) v x

/-- The formal degree at a member of the actual unitary orbit. -/
abbrev semistandardOrbitFormalDegree (A : UnitaryOrbitRepresentative m.normCharacters pi) : ℝ :=
  representationFormalDegree C hC muM (compactOpenCofinal p d)
    (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi A)
    A.val.property.1

/-- Pointwise VII.1.2 for each actual member of a semistandard Fourier orbit. -/
theorem rationalSemistandardFourierOrbit_eval_constantTerm
    (f : RationalSchwartzSpace hKc hPK rho)
    (A : UnitaryOrbitRepresentative m.normCharacters pi) (x : rationalPoints G × rationalPoints G) :
    let := nestedFourierLeviCompactOpen p d
    let := hin.levi_left
    let := hin.levi_right
    semistandardCoefficientEval
      (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
        p m d hdelta pi C hC muM hsqPi hT f A) x =
    coefficientFourierTransform A.val.obj hin.levi_weights A.val.property.2
      (hin.orbit_tempered A) hin.levi_xi_inv hin.levi_height_inv
      (semistandardOrbitFormalDegree p m d pi C hC muM hsqPi A)
      (Space.constantTermInd hin.constant_term hin.constant_term_estimate
        (rationalTranslationWeights K.isOpen hKc hPK rho) hin.levi_translations f x) := by
  let := hin.ambient_inv
  let := hin.ambient_sigmaFinite
  let := hin.levi_left
  let := hin.levi_right
  let := hin.levi_inv
  let := hin.levi_sfinite
  let := hin.radical_left
  let := hin.radical_right
  let := hin.radical_sfinite
  let := nestedFourierLeviCompactOpen p d
  rw [rationalSemistandardFourierOrbit_apply,
    rationalSemistandardInducedFourierTransform_eq_inducedFourierTransform]
  exact eval_inducedFourierTransform
    (decomposition p) (isClosed_radical p) (isClosed_parabolic p)
    d.projection_continuous d.compact d.isCompact d.factorization_mem
    _ hdelta A.val.obj (compactOpenCofinal p d) C hC muM _ A.val.property.1
    (rationalL2Weights K.isOpen hKc hPK rho hsw) (hT A)
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
    hin.radical_unimodular hin.levi_weights (hin.orbit_tempered A) hin.levi_xi_inv hin.levi_height_inv
    hin.constant_term hin.conjugation_modulus hin.constant_term_estimate
    (rationalTranslationWeights K.isOpen hKc hPK rho) hin.levi_translations
    hin.ambient_compact_volume hin.compact_factorization hin.levi_compact_volume
    hin.radical_compact_volume f (hin.double_integrability f A) x

end Evaluation

section ParabolicLift

variable (p : SemistandardSpectralIndex i) (m : LeviModel p)
  {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  (q : SemistandardSpectralIndex iM) (r : SemistandardSpectralIndex i)

/-- The all-test parabolic product, final Levi image and inner radical of the
lift `P' = P^M U` in VIII.2.1. -/
structure RationalSemistandardParabolicLift : Prop where
  parabolic_product : r.parabolic.IsPointwiseProduct (q.parabolic.map m.inclusion) p.radical
  levi_image : q.levi.map m.inclusion = r.levi
  radical_comap : q.radical = r.radical.comap m.inclusion

variable (h : RationalSemistandardParabolicLift p m q r)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
include h in
theorem RationalSemistandardParabolicLift.parabolic_le : r.parabolic ≤ p.parabolic := by
  have hP : q.parabolic.map m.inclusion ≤ p.parabolic :=
    ((SubgroupFunctor.map_le_range _ _).trans_eq m.represents.2).trans p.levi_le_parabolic
  intro X x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.parabolic_product X x).mp hx
  exact (p.parabolic.carrier X).mul_mem (hP X ha) (p.radical_le_parabolic X hb)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
include h in
theorem RationalSemistandardParabolicLift.isProper (hp : p.parabolic ≠ ⊤) :
    r.parabolic ≠ ⊤ := by
  intro hr
  have hle : (⊤ : SubgroupFunctor G) ≤ p.parabolic := hr ▸ h.parabolic_le
  apply hp
  refine le_antisymm ?_ hle
  intro T x _
  exact Subgroup.mem_top x

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
include h in
theorem RationalSemistandardParabolicLift.levi_points_le : levi r ≤ levi p := by
  have hLevi : r.levi ≤ p.levi :=
    h.levi_image ▸ (SubgroupFunctor.map_le_range m.inclusion q.levi).trans_eq m.represents.2
  exact hLevi _

variable {p m q r} in
/-- The comparison between the two literal final Levi groups. -/
def RationalSemistandardParabolicLift.leviEquiv
    (eL : levi q ≃ₜ* (levi r).subgroupOf (levi p)) : levi q ≃ₜ* levi r :=
  eL.trans (Subgroup.subgroupOfContinuousMulEquivOfLe h.levi_points_le)

end ParabolicLift

section NestedComparison

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (p : SemistandardSpectralIndex i) (m : LeviModel p)
  {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  {nuM : cocharacterLattice SM} (hiM : IsMaximalSplitTorus iM)
  (hnuM : IsGenericCocharacter iM nuM)
  {KM : OpenSubgroup (rationalPoints m.scheme)}
  (hKMc : IsCompact (KM : Set (rationalPoints m.scheme)))
  (hPMK : IsIwasawaPair (standardParabolicPoints iM nuM ∅) (KM : Subgroup (rationalPoints m.scheme)))
  {muM : Measure (rationalPoints m.scheme)} [muM.IsMulLeftInvariant] [muM.IsMulRightInvariant]
  (hswM : SquareIntegrableWeight muM (rationalXi hKMc hPMK)
    (rationalHeight (F := F) (rho.restrict m.inclusion)))
  {XiM sigmaM : levi p → ℝ}
  (hXiM : ∀ x, rationalXi hKMc hPMK x = XiM (m.pointHomeomorph x))
  (hSigmaM : ∀ x, rationalHeight (F := F) (rho.restrict m.inclusion) x = sigmaM (m.pointHomeomorph x))
  (muU : Measure (radical p)) [SFinite muU]
  (hD : ConstantTermData muU (semistandardUnipotentModulus p))
  (hE : ConstantTermEstimate muU (semistandardUnipotentModulus p)
    (rationalXi hKc hPK) (rationalHeight (F := F) rho) XiM sigmaM)
  (htM : TranslationWeights XiM sigmaM)
  (q : SemistandardSpectralIndex iM) (mq : LeviModel q) (dq : CompactData q)
  (r : SemistandardSpectralIndex i) (mr : LeviModel r) (dr : CompactData r)
  (hlift : RationalSemistandardParabolicLift p m q r)
  (hdeltaQ : ModularNormalization q) (hdeltaR : ModularNormalization r)
  (piQ : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi q))
  (piR : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi r))
  (CQ : Subgroup (levi q)) [CQ.Normal] (hCQ : CQ ≤ Subgroup.center (levi q))
  (CR : Subgroup (levi r)) [CR.Normal] (hCR : CR ≤ Subgroup.center (levi r))
  [MeasurableSpace (levi q ⧸ CQ)] [BorelSpace (levi q ⧸ CQ)]
  [MeasurableSpace (levi r ⧸ CR)] [BorelSpace (levi r ⧸ CR)]
  (muCQ : Measure (levi q ⧸ CQ)) [muCQ.IsHaarMeasure] [muCQ.IsInvInvariant]
  (muCR : Measure (levi r ⧸ CR)) [muCR.IsHaarMeasure] [muCR.IsInvInvariant]
  (hsqQ : IsSquareIntegrableModCentralSubgroup CQ hCQ piQ.obj.representation muCQ)
  (hsqR : IsSquareIntegrableModCentralSubgroup CR hCR piR.obj.representation muCR)
  (hTQ : ∀ B : UnitaryOrbitRepresentative mq.normCharacters piQ,
    HasTemperedCoefficients (rationalXi hKMc hPMK) (rationalHeight (F := F) (rho.restrict m.inclusion))
      ((normalizedInductionFunctor (decomposition q) (isClosed_radical q)).obj B.val.obj).representation)
  (hTR : ∀ A : UnitaryOrbitRepresentative mr.normCharacters piR,
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition r) (isClosed_radical r)).obj A.val.obj).representation)
  (muLQ : Measure (levi q)) (muLR : Measure (levi r))
  (muQ : Measure (radical q)) (muR : Measure (radical r))
  (XiQ sigmaQ : levi q → ℝ) (XiR sigmaR : levi r → ℝ)
  (muI : Measure ((radical r).subgroupOf (levi p))) [SFinite muI]
  (deltaI : (levi r).subgroupOf (levi p) →* ℝ≥0ˣ)
  (eL : levi q ≃ₜ* (levi r).subgroupOf (levi p))
  (eU : radical q ≃ₜ* (radical r).subgroupOf (levi p))

/-- The ambient arguments in the III.6 diagram. -/
private abbrev liftedArguments (g : rationalPoints G × rationalPoints G)
    (x : rationalPoints m.scheme × rationalPoints m.scheme) : rationalPoints G × rationalPoints G :=
  ((m.pointHomeomorph x.1 : rationalPoints G) * g.1, (m.pointHomeomorph x.2 : rationalPoints G) * g.2)

/-- Both inverse half-moduli from the outer parabolic in III.6. -/
private abbrev liftedModulusFactor (x : rationalPoints m.scheme × rationalPoints m.scheme) : ℂ :=
  (((NNReal.sqrt (semistandardUnipotentModulus p (m.pointHomeomorph x.1)) : ℝ) : ℂ) *
    ((NNReal.sqrt (semistandardUnipotentModulus p (m.pointHomeomorph x.2)) : ℝ) : ℂ))⁻¹

/-- The nested VIII.2.1 comparison at individual members of the two actual
unitary orbits, with the Levi model, Haar and III.6 comparisons explicit. -/
def RationalSemistandardNestedFourierStatement : Prop :=
  RationalSemistandardFourierAnalyticInputs (muG := muM) hKMc hPMK (rho.restrict m.inclusion)
    q mq dq piQ muLQ muQ XiQ sigmaQ →
  RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
    r mr dr piR muLR muR XiR sigmaR →
  RationalSemistandardConstantTermModelComparison p m q r muQ muI deltaI eL eU →
  TransitivityData muR (semistandardUnipotentModulus r)
    muU (semistandardUnipotentModulus p) muI deltaI →
  IsConjModulus (semistandardLeviPoints_le_normalizer_radicalPoints p) muU
    (semistandardUnipotentModulus p) →
  MeasurePreserving (hlift.leviEquiv eL) muLQ muLR →
  ∀ (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G)
    (B : UnitaryOrbitRepresentative mq.normCharacters piQ)
    (A : UnitaryOrbitRepresentative mr.normCharacters piR)
    (eA : (SmoothRep.pullback (hlift.leviEquiv eL) A.val.obj).representation.Equiv
      B.val.obj.representation)
    (x : rationalPoints m.scheme × rationalPoints m.scheme),
    semistandardOrbitFormalDegree q mq dq piQ CQ hCQ muCQ hsqQ B =
      semistandardOrbitFormalDegree r mr dr piR CR hCR muCR hsqR A →
    (∀ l : levi q, Integrable (fun u : radical r =>
      translate (liftedArguments p m g x).1 (liftedArguments p m g x).2 f
        (((hlift.leviEquiv eL l : levi r) : rationalPoints G) * u)) muR) →
    semistandardCoefficientEval
      (rationalSemistandardFourierOrbit m.reductive hiM hnuM hKMc hPMK (rho.restrict m.inclusion) hswM
        q mq dq hdeltaQ piQ CQ hCQ muCQ hsqQ hTQ
        (rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM muU hD hE htM f g)
        B) x =
      liftedModulusFactor p m x • coefficientTensorCongr eA
        (coefficientTensorPullbackEquiv (hlift.leviEquiv eL) A.val.obj
          (semistandardCoefficientEval
            (rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
              r mr dr hdeltaR piR CR hCR muCR hsqR hTR f A) (liftedArguments p m g x)))

set_option maxHeartbeats 800000 in
theorem rationalSemistandardNestedFourier :
    RationalSemistandardNestedFourierStatement hG hi hnu hKc hPK rho hsw p m hiM hnuM
      hKMc hPMK hswM hXiM hSigmaM muU hD hE htM q mq dq r mr dr hlift hdeltaQ hdeltaR
      piQ piR CQ hCQ CR hCR muCQ muCR hsqQ hsqR hTQ hTR
      muLQ muLR muQ muR XiQ sigmaQ XiR sigmaR muI deltaI eL eU := by
  intro hinQ hinR hmodel htrans hconj hmu f g B A eA x hdegree hint
  let := nestedFourierLeviCompactOpen q dq
  let := nestedFourierLeviCompactOpen r dr
  let := hinQ.levi_left
  let := hinQ.levi_right
  let := hinR.levi_left
  let := hinR.levi_right
  rw [rationalSemistandardFourierOrbit_eval_constantTerm m.reductive hiM hnuM hKMc hPMK
      (rho.restrict m.inclusion) hswM q mq dq hdeltaQ piQ CQ hCQ muCQ hsqQ hTQ muLQ muQ XiQ sigmaQ hinQ,
    rationalSemistandardFourierOrbit_eval_constantTerm hG hi hnu hKc hPK rho hsw
      r mr dr hdeltaR piR CR hCR muCR hsqR hTR muLR muR XiR sigmaR hinR, hdegree]
  refine coefficientFourierTransform_eq_smul_of_modelTransport (hlift.leviEquiv eL) eA
    hinR.levi_weights hinQ.levi_weights A.val.property.2 B.val.property.2
    (hinR.orbit_tempered A) (hinQ.orbit_tempered B) hinR.levi_xi_inv hinR.levi_height_inv
    hinQ.levi_xi_inv hinQ.levi_height_inv hmu _ _ _ _ ?_
  intro l
  exact rationalSemistandardLeviConstantTerm_induced_transitivity hKc hPK rho p m hKMc hPMK
    hXiM hSigmaM muU hD hE htM q r muQ muI deltaI eL eU hmodel muR htrans hconj
    f g x.1 x.2 l (hint l)

end NestedComparison

end Langlands.HarishChandraSchwartz

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardNestedFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperFourier

/-! # Transfer of proper Fourier vanishing to the outer Levi in VIII.2.1 -/

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

local instance leviFourierAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance leviFourierFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

local instance leviFourierCompactOpen {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] :
    Nonempty (CompactOpenSubgroup (rationalPoints H)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F H⟩

private theorem coefficientSection_ext {p : SemistandardSpectralIndex i}
    {A : SmoothRep.{0, u, uV} ℂ (levi p)}
    {v w : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A}
    (h : ∀ x, semistandardCoefficientEval (p := p) (A := A) v x =
      semistandardCoefficientEval (p := p) (A := A) w x) : v = w := by
  exact Subtype.ext (Subtype.ext (funext h))

private theorem coefficientSection_eval_zero {p : SemistandardSpectralIndex i}
    {A : SmoothRep.{0, u, uV} ℂ (levi p)} (x : rationalPoints G × rationalPoints G) :
    semistandardCoefficientEval (p := p) (A := A) 0 x = 0 := rfl

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
  {muLevi : Measure (rationalPoints m.scheme)} [muLevi.IsMulLeftInvariant] [muLevi.IsMulRightInvariant]
  (hswM : SquareIntegrableWeight muLevi (rationalXi hKMc hPMK)
    (rationalHeight (F := F) (rho.restrict m.inclusion)))
  {XiM sigmaM : levi p → ℝ}
  (hXiM : ∀ x, rationalXi hKMc hPMK x = XiM (m.pointHomeomorph x))
  (hSigmaM : ∀ x, rationalHeight (F := F) (rho.restrict m.inclusion) x = sigmaM (m.pointHomeomorph x))
  (muU : Measure (radical p)) [SFinite muU]
  (hD : ConstantTermData muU (semistandardUnipotentModulus p))
  (hE : ConstantTermEstimate muU (semistandardUnipotentModulus p)
    (rationalXi hKc hPK) (rationalHeight (F := F) rho) XiM sigmaM)
  (htM : TranslationWeights XiM sigmaM)

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ r, (T r).toGrp ⟶ (chosenLeviModel r).scheme)
  (ha : ∀ r, IsSplitComponent (a r))
  [∀ r, ((chosenLeviModel r).splitCenter (a r)).Normal]
  [∀ r, MeasurableSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  [∀ r, BorelSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  (muR : ∀ r, Measure (levi r ⧸ (chosenLeviModel r).splitCenter (a r)))
  [∀ r, (muR r).IsHaarMeasure] [∀ r, (muR r).IsInvInvariant]
  (d : ∀ r : SemistandardSpectralIndex i, CompactData r)
  (hdelta : ∀ r : SemistandardSpectralIndex i, ModularNormalization r)
  (hT : ∀ (r : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi r)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel r).splitCenter (a r))
      ((chosenLeviModel r).splitCenter_le_center (a r) (ha r)) A.obj.representation (muR r) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition r) (isClosed_radical r)).obj A.obj).representation)

variable {TM : SemistandardSpectralIndex iM → CommGroupScheme (Spec (CommRingCat.of F))}
  (aM : ∀ q, (TM q).toGrp ⟶ (chosenLeviModel q).scheme)
  (haM : ∀ q, IsSplitComponent (aM q))
  [∀ q, ((chosenLeviModel q).splitCenter (aM q)).Normal]
  [∀ q, MeasurableSpace (levi q ⧸ (chosenLeviModel q).splitCenter (aM q))]
  [∀ q, BorelSpace (levi q ⧸ (chosenLeviModel q).splitCenter (aM q))]
  (muQ : ∀ q, Measure (levi q ⧸ (chosenLeviModel q).splitCenter (aM q)))
  [∀ q, (muQ q).IsHaarMeasure] [∀ q, (muQ q).IsInvInvariant]
  (dM : ∀ q : SemistandardSpectralIndex iM, CompactData q)
  (hdeltaM : ∀ q : SemistandardSpectralIndex iM, ModularNormalization q)
  (hTM : ∀ (q : SemistandardSpectralIndex iM)
    (B : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi q)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel q).splitCenter (aM q))
      ((chosenLeviModel q).splitCenter_le_center (aM q) (haM q)) B.obj.representation (muQ q) →
    HasTemperedCoefficients (rationalXi hKMc hPMK) (rationalHeight (F := F) (rho.restrict m.inclusion))
      ((normalizedInductionFunctor (decomposition q) (isClosed_radical q)).obj B.obj).representation)

section Match

variable (t : RationalSemistandardTheta.{u, uV} aM haM muQ)
  (s : RationalSemistandardTheta.{u, uV} a ha muR)

local notation "modelQ" => chosenLeviModel (Sigma.fst t)
local notation "modelR" => chosenLeviModel (Sigma.fst s)
local notation "piQ" => orbitRepresentative modelQ (aM (Sigma.fst t)) (haM (Sigma.fst t)) (muQ (Sigma.fst t)) (Sigma.snd t)
local notation "piR" => orbitRepresentative modelR (a (Sigma.fst s)) (ha (Sigma.fst s)) (muR (Sigma.fst s)) (Sigma.snd s)
local notation "centerQ" => LeviModel.splitCenter modelQ (aM (Sigma.fst t))
local notation "centerR" => LeviModel.splitCenter modelR (a (Sigma.fst s))
local notation "hcenterQ" => LeviModel.splitCenter_le_center modelQ (aM (Sigma.fst t)) (haM (Sigma.fst t))
local notation "hcenterR" => LeviModel.splitCenter_le_center modelR (a (Sigma.fst s)) (ha (Sigma.fst s))
local notation "hsqQ" => orbitRepresentative_isSquareIntegrable modelQ (aM (Sigma.fst t)) (haM (Sigma.fst t)) (muQ (Sigma.fst t)) (Sigma.snd t)
local notation "hsqR" => orbitRepresentative_isSquareIntegrable modelR (a (Sigma.fst s)) (ha (Sigma.fst s)) (muR (Sigma.fst s)) (Sigma.snd s)

/-- Inputs for comparing one actual Levi component with an actual ambient
component in the nested VIII.2.1 diagram. -/
structure RationalSemistandardNestedFourierMatch where
  lift : RationalSemistandardParabolicLift p m t.1 s.1
  leviEquiv : levi t.1 ≃ₜ* (levi s.1).subgroupOf (levi p)
  radicalEquiv : radical t.1 ≃ₜ* (radical s.1).subgroupOf (levi p)
  innerLeviHaar : Measure (levi t.1)
  liftedLeviHaar : Measure (levi s.1)
  innerRadicalHaar : Measure (radical t.1)
  liftedRadicalHaar : Measure (radical s.1)
  intermediateHaar : Measure ((radical s.1).subgroupOf (levi p))
  intermediate_sfinite : SFinite intermediateHaar
  intermediateModulus : (levi s.1).subgroupOf (levi p) →* ℝ≥0ˣ
  innerXi : levi t.1 → ℝ
  innerHeight : levi t.1 → ℝ
  liftedXi : levi s.1 → ℝ
  liftedHeight : levi s.1 → ℝ
  innerEvaluation : RationalSemistandardFourierAnalyticInputs (muG := muLevi) hKMc hPMK
    (rho.restrict m.inclusion) t.1 modelQ (dM t.1) piQ innerLeviHaar innerRadicalHaar innerXi innerHeight
  liftedEvaluation : RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK
    rho s.1 modelR (d s.1) piR liftedLeviHaar liftedRadicalHaar liftedXi liftedHeight
  constantTermModel : RationalSemistandardConstantTermModelComparison p m t.1 s.1 innerRadicalHaar
    intermediateHaar intermediateModulus leviEquiv radicalEquiv
  transitivity : TransitivityData liftedRadicalHaar (semistandardUnipotentModulus s.1)
    muU (semistandardUnipotentModulus p) intermediateHaar intermediateModulus
  levi_measure : MeasurePreserving (lift.leviEquiv leviEquiv) innerLeviHaar liftedLeviHaar
  orbit_match : ∀ B : UnitaryOrbitRepresentative (LeviModel.normCharacters modelQ) piQ,
    ∃ A : UnitaryOrbitRepresentative (LeviModel.normCharacters modelR) piR,
      Nonempty ((SmoothRep.pullback (lift.leviEquiv leviEquiv) A.val.obj).representation.Equiv
        B.val.obj.representation) ∧
      semistandardOrbitFormalDegree t.1 modelQ (dM t.1) piQ centerQ hcenterQ (muQ t.1) hsqQ B =
        semistandardOrbitFormalDegree s.1 modelR (d s.1) piR centerR hcenterR (muR s.1) hsqR A
  radical_integrability : ∀ (f : RationalSchwartzSpace hKc hPK rho)
    (g : rationalPoints G × rationalPoints G) (x : rationalPoints m.scheme × rationalPoints m.scheme)
    (l : levi t.1), Integrable (fun v : radical s.1 =>
      translate ((m.pointHomeomorph x.1 : rationalPoints G) * g.1)
        ((m.pointHomeomorph x.2 : rationalPoints G) * g.2) f
          (((lift.leviEquiv leviEquiv l : levi s.1) : rationalPoints G) * v)) liftedRadicalHaar

local notation "ambientFourier" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muR d hdelta hT
local notation "leviFourier" =>
  rationalSemistandardFourierFamily m.reductive hiM hnuM hKMc hPMK (rho.restrict m.inclusion) hswM
    aM haM muQ dM hdeltaM hTM
local notation "leviTerm" =>
  rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM muU hD hE htM

set_option maxHeartbeats 1200000 in
/-- Zero of the matched ambient Fourier component transfers to the whole
inner orbit component of the actual Levi Schwartz constant term. -/
theorem rationalSemistandardLeviFourierComponent_eq_zero
    (c : RationalSemistandardNestedFourierMatch (muG := muG) (muLevi := muLevi) hKc hPK rho p m
      hKMc hPMK muU a ha muR d aM haM muQ dM t s)
    (hconj : IsConjModulus (semistandardLeviPoints_le_normalizer_radicalPoints p)
      muU (semistandardUnipotentModulus p))
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G)
    (hf : ambientFourier f s = 0) : leviFourier (leviTerm f g) t = 0 := by
  let := c.intermediate_sfinite
  funext B
  refine coefficientSection_ext (p := t.1) (A := B.val.obj) ?_
  intro x
  obtain ⟨A, ⟨eA⟩, hdegree⟩ := c.orbit_match B
  have hA : ambientFourier f s A = 0 := congrFun hf A
  have hEval := rationalSemistandardNestedFourier hG hi hnu hKc hPK rho hsw p m hiM hnuM
    hKMc hPMK hswM hXiM hSigmaM muU hD hE htM t.1 modelQ (dM t.1) s.1 modelR (d s.1)
    c.lift (hdeltaM t.1) (hdelta s.1) piQ piR centerQ hcenterQ centerR hcenterR
    (muQ t.1) (muR s.1) hsqQ hsqR
    (fun B' => hTM t.1 B'.val (unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _ hsqQ B'))
    (fun A' => hT s.1 A'.val (unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _ hsqR A'))
    c.innerLeviHaar c.liftedLeviHaar c.innerRadicalHaar c.liftedRadicalHaar
    c.innerXi c.innerHeight c.liftedXi c.liftedHeight c.intermediateHaar c.intermediateModulus
    c.leviEquiv c.radicalEquiv c.innerEvaluation c.liftedEvaluation c.constantTermModel
    c.transitivity hconj c.levi_measure f g B A eA x hdegree (c.radical_integrability f g x)
  change semistandardCoefficientEval (p := t.1) (A := B.val.obj) (leviFourier (leviTerm f g) t B) x =
    _ • coefficientTensorCongr eA
      (coefficientTensorPullbackEquiv (c.lift.leviEquiv c.leviEquiv) A.val.obj
        (semistandardCoefficientEval (p := s.1) (A := A.val.obj) (ambientFourier f s A)
          ((m.pointHomeomorph x.1 : rationalPoints G) * g.1,
            (m.pointHomeomorph x.2 : rationalPoints G) * g.2))) at hEval
  rw [hA] at hEval
  simpa only [Pi.zero_apply, coefficientSection_eval_zero, map_zero, smul_zero] using hEval

end Match

/-- Every actual inner orbit has a matched actual lifted orbit with the
nested comparison inputs. The inner index ranges over the full family. -/
def RationalSemistandardNestedFourierCoverage : Prop :=
  ∀ t : RationalSemistandardTheta.{u, uV} aM haM muQ,
    ∃ s : RationalSemistandardTheta.{u, uV} a ha muR,
      Nonempty (RationalSemistandardNestedFourierMatch (muG := muG) (muLevi := muLevi) hKc hPK rho p m
        hKMc hPMK muU a ha muR d aM haM muQ dM t s)

/-- Transfer from the actual proper cutoff on `G` to the full Fourier family
of the induced constant-term Schwartz function on `M`. -/
def RationalSemistandardLeviFourierVanishingStatement : Prop :=
  p.IsProper →
  RationalSemistandardNestedFourierCoverage.{u, uV} (muG := muG) (muLevi := muLevi) hKc hPK rho p m
    hKMc hPMK muU a ha muR d aM haM muQ dM →
  IsConjModulus (semistandardLeviPoints_le_normalizer_radicalPoints p) muU
    (semistandardUnipotentModulus p) →
  ∀ (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G),
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muR d hdelta hT f = 0 →
    rationalSemistandardFourierFamily m.reductive hiM hnuM hKMc hPMK (rho.restrict m.inclusion) hswM
      aM haM muQ dM hdeltaM hTM
      (rationalSemistandardLeviConstantTerm hKc hPK rho p m hKMc hPMK hXiM hSigmaM muU hD hE htM f g) = 0

theorem rationalSemistandardLeviFourierVanishing :
    RationalSemistandardLeviFourierVanishingStatement hG hi hnu hKc hPK rho hsw p m hiM hnuM
      hKMc hPMK hswM hXiM hSigmaM muU hD hE htM a ha muR d hdelta hT aM haM muQ dM hdeltaM hTM := by
  intro hp hcoverage hconj f g hf
  have hv := (rationalSemistandardProperFourier_eq_zero_iff hG hi hnu hKc hPK rho hsw
    a ha muR d hdelta hT f).mp hf
  funext t
  obtain ⟨s, ⟨c⟩⟩ := hcoverage t
  have hs : s.1.IsProper := RationalSemistandardParabolicLift.isProper p m t.1 s.1 c.lift hp
  exact rationalSemistandardLeviFourierComponent_eq_zero hG hi hnu hKc hPK rho hsw p m hiM hnuM
    hKMc hPMK hswM hXiM hSigmaM muU hD hE htM a ha muR d hdelta hT aM haM muQ dM hdeltaM hTM
    t s c hconj f g (hv s hs)

end Langlands.HarishChandraSchwartz

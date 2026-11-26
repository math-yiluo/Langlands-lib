import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierReconstruction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperOrbitSymmetry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationFormula

/-! # Waldspurger VIII.1 (3): the character inversion formula

Waldspurger (2003), VIII.1, printed p. 320, formula (3). The target is a Prop-valued
definition. The module proves the independence of its integrand from the choice of
inducing objects. Under VII.1.1 (iii) and the VII.2.4 association formula it proves that
(1) and (2) imply (3), and that (3) gives the reconstruction `κ(psi_f) = f` whenever the
invariant Fourier lift of `f` exists. With invariant-carrier membership of every
`psi_f` (`FourierInvariantLiftStatement`) as a further hypothesis, (3) is equivalent to
(1) and (2). -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.WaldspurgerSourceNormalization (IsSourceCompactAt)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion

open GlobalSynthesis

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

local instance characterCompactOpen {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance characterParabolicLC {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

section FixedData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
set_option quotPrecheck false in
local notation "fam" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT
set_option hygiene false in
set_option quotPrecheck false in
local notation "leftTranslate" =>
  Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) 1
set_option hygiene false in
set_option quotPrecheck false in
local notation "checkC" =>
  Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
set_option hygiene false in
set_option quotPrecheck false in
local notation "character" => semistandardInducedSchwartzCharacter hKc hPK rho a ha mu d hsw hT
set_option hygiene false in
set_option quotPrecheck false in
local notation "sqAt(" t "," A ")" =>
  unitaryOrbitRepresentative_isDiscreteSeries (chosenLeviModel (t : Θ).1).normCharacters
    (orbitRepresentative (chosenLeviModel (t : Θ).1) (a (t : Θ).1) (ha (t : Θ).1) (mu (t : Θ).1)
      (t : Θ).2)
    ((chosenLeviModel (t : Θ).1).splitCenter (a (t : Θ).1))
    ((chosenLeviModel (t : Θ).1).splitCenter_le_center (a (t : Θ).1) (ha (t : Θ).1))
    (mu (t : Θ).1)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel (t : Θ).1) (a (t : Θ).1)
      (ha (t : Θ).1) (mu (t : Θ).1) (t : Θ).2) (A)

/-! ## The character and the coefficient of the Fourier family -/

/-- `d(ω) θ_ω^G(λ(g) ˇf)` at an actual inducing object `A` of the orbit of `t`: the
formal degree for the actual split-central quotient Haar measure, times the trace of
the finite-rank normalized induced operator at `λ(g) ˇf`. -/
def formalDegreeCharacter (t : Θ) (A : ComponentOrbitRepresentative a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G) : ℂ :=
  (componentFormalDegree a ha mu d t A : ℂ) *
    character t.1 A.val (sqAt(t, A)) (leftTranslate g (checkC f))

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- VII.1.1 (iii) for the full family: `d(ω) θ_ω^G(λ(g) ˇf)` is the value at `g` of the
coefficient of `psi_f[O,P](ω)`. -/
theorem formalDegreeCharacter_eq_coefficient (t : Θ) (A : ComponentOrbitRepresentative a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G) :
    formalDegreeCharacter hG hi hnu hKc hPK rho hsw a ha mu d hT t A f g =
      rationalSemistandardFourierCoefficientMap hG t.1 (d t.1) (hdelta t.1) A.val.obj
        ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1) (sqAt(t, A))
        (fam f t A) g :=
  (rationalSemistandardFourier_trace hG hi hnu hKc hPK rho hsw t.1 (d t.1) (hdelta t.1)
    A.val.obj _ _ (mu t.1) (sqAt(t, A)) A.val.property.1 (hT t.1 A.val (sqAt(t, A))) f g).symm

include hdelta in
omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- `d(ω) θ_ω^G(λ(g) ˇf)` depends only on the orbit point `ω`: two inducing objects
with the same class give the same value, by VII.1.1 (iii), the representative
coherence of `psi_f` and the invariance of the coefficient map under transport. -/
theorem formalDegreeCharacter_eq_of_point_eq [muG.IsInvInvariant] (t : Θ)
    (A B : ComponentOrbitRepresentative a ha mu t)
    (hab : componentOrbitPoint a ha mu t A = componentOrbitPoint a ha mu t B)
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G) :
    formalDegreeCharacter hG hi hnu hKc hPK rho hsw a ha mu d hT t A f g =
      formalDegreeCharacter hG hi hnu hKc hPK rho hsw a ha mu d hT t B f g := by
  have hclass : (Quotient.mk _ A.val : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi t.1)) =
      Quotient.mk _ B.val :=
    congrArg (fun ω => ω.val.val) hab
  let e : A.val.obj.representation.Equiv B.val.obj.representation :=
    SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := levi t.1)).ι.mapIso
      (Classical.choice (Quotient.exact hclass)))
  rw [formalDegreeCharacter_eq_coefficient hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT t A f g,
    formalDegreeCharacter_eq_coefficient hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT t B f g,
    rationalSemistandardFourierFamily_coherent hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT f t
      A B e]
  exact congrArg (fun L : LocallyConstant (rationalPoints G) ℂ => L g)
    (CompactInduction.coefficientMap_transport (decomposition t.1) (isClosed_radical t.1)
      (isClosed_parabolic t.1) (d t.1).compact (d t.1).isCompact (d t.1).factorization_mem
      (fun x => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter x)
      (hdelta t.1) (d t.1).projection_continuous (sqAt(t, A)).1 (sqAt(t, B)).1 e
      (fam f t A)).symm


/-- A choice of actual inducing object at every point of the orbit of `t`. -/
def OrbitSelection (t : Θ) : Type _ :=
  {s : GlobalForm.OrbitPoint a ha mu t → ComponentOrbitRepresentative a ha mu t //
    ∀ ω, componentOrbitPoint a ha mu t (s ω) = ω}

/-- Orbit points have actual inducing objects, so selections exist. -/
def OrbitSelection.choose (t : Θ) : OrbitSelection a ha mu t :=
  ⟨fun ω => Classical.choose (componentOrbitPoint_surjective a ha mu t ω),
    fun ω => Classical.choose_spec (componentOrbitPoint_surjective a ha mu t ω)⟩

section Character

variable (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (C.presentation theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

set_option hygiene false in
set_option quotPrecheck false in
local notation "density" => GlobalForm.componentDensity hG a ha mu C.presentation Q
set_option hygiene false in
set_option quotPrecheck false in
local notation "measureAt" => componentOrbitMeasure a ha mu hindex
set_option hygiene false in
set_option quotPrecheck false in
local notation "coefficient(" t ")" =>
  SourcePacket.coefficientMap hG (chosenLeviModel (t : Θ).1) (C.presentation (t : Θ).1)
    (d (t : Θ).1)
    (orbitRepresentative (chosenLeviModel (t : Θ).1) (a (t : Θ).1) (ha (t : Θ).1) (mu (t : Θ).1)
      (t : Θ).2)
    ((chosenLeviModel (t : Θ).1).splitCenter (a (t : Θ).1))
    ((chosenLeviModel (t : Θ).1).splitCenter_le_center (a (t : Θ).1) (ha (t : Θ).1))
    (mu (t : Θ).1)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel (t : Θ).1) (a (t : Θ).1)
      (ha (t : Θ).1) (mu (t : Θ).1) (t : Θ).2)
set_option hygiene false in
set_option quotPrecheck false in
local notation "packet" => componentPacket hG a ha mu d C.presentation hindex Q

/-- The integrand of VIII.1 (3): `μ(ω) d(ω) θ_ω^G(λ(g) ˇf)` at each point `ω` of the
orbit of `t`, with the actual density of the source packets, computed at the
selected inducing object. -/
def characterIntegrand (t : Θ) (s : OrbitSelection a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G)
    (ω : GlobalForm.OrbitPoint a ha mu t) : ℂ :=
  density t ω * formalDegreeCharacter hG hi hnu hKc hPK rho hsw a ha mu d hT t (s.1 ω) f g

/-- The orbit integral of VIII.1 (3) for the actual normalized orbit measure. -/
def characterOrbitIntegral (t : Θ) (s : OrbitSelection a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G) : ℂ :=
  ∫ ω, characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hT C Q t s f g ω ∂measureAt t

include hdelta in
omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- The integrand of VIII.1 (3) does not depend on the selected inducing objects. -/
theorem characterIntegrand_selection_independent [muG.IsInvInvariant] (t : Θ)
    (s s' : OrbitSelection a ha mu t) (f : RationalSchwartzSpace hKc hPK rho)
    (g : rationalPoints G) :
    characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hT C Q t s f g =
      characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hT C Q t s' f g := by
  funext ω
  unfold characterIntegrand
  rw [formalDegreeCharacter_eq_of_point_eq hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT t
    (s.1 ω) (s'.1 ω) ((s.2 ω).trans (s'.2 ω).symm) f g]

include hdelta in
/-- The orbit integral of VIII.1 (3) does not depend on the selected inducing objects. -/
theorem characterOrbitIntegral_selection_independent [muG.IsInvInvariant] (t : Θ)
    (s s' : OrbitSelection a ha mu t) (f : RationalSchwartzSpace hKc hPK rho)
    (g : rationalPoints G) :
    characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q t s f g =
      characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q t s' f g := by
  unfold characterOrbitIntegral
  rw [characterIntegrand_selection_independent hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C Q
    t s s' f g]

/-- The right side of VIII.1 (3) at `g`: the sum over the association
representatives `R` of `c(G|M)^-2 gamma(G|M)^-1 |Stab(O,M)|^-1` times the orbit
integral, with the coefficient of the Library's VII.2.4 formulas. -/
def characterInversionSum (R : Association.Representatives.{u, uV} a ha mu)
    (s : ∀ t : Θ, OrbitSelection a ha mu t) (f : RationalSchwartzSpace hKc hPK rho)
    (g : rationalPoints G) : ℂ :=
  Association.representativeSum a ha mu R (fun t =>
    (Association.coefficientAtRepresentative C K0 hK0 t : ℂ) *
      characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q t (s t) f g)

/-- **Waldspurger VIII.1 (3).** For every Schwartz function `f`, every `g`, every set
`R` of association representatives and every selection of inducing objects: each
orbit integrand is integrable, only finitely many association classes contribute, and
`f(g)` is the sum over `R` of `c(G|M)^-2 gamma(G|M)^-1 |Stab(O,M)|^-1` times
`∫_O μ(ω) d(ω) θ_ω^G(λ(g) ˇf) dω`. -/
def CharacterInversionStatement : Prop :=
  ∀ (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G)
    (R : Association.Representatives.{u, uV} a ha mu) (s : ∀ t : Θ, OrbitSelection a ha mu t),
    (∀ t : Θ, Integrable (characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hT C Q t (s t) f g)
      (measureAt t)) ∧
    (Function.support (fun c : Association.AssociationClass.{u, uV} a ha mu =>
      (Association.coefficientAtRepresentative C K0 hK0 (R.select c) : ℂ) *
        characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q (R.select c)
          (s (R.select c)) f g)).Finite ∧
    f g = characterInversionSum hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q K0 hK0 R s f g

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- VII.1.1 (iii) along the orbit: when `psi_f[O,P]` is a smooth section, the integrand
of VIII.1 (3) is the integrand `μ(ω) (E_P^G psi_f[O,P](ω))(g)` of the actual source
packet of `psi_f[O,P]`. -/
theorem characterIntegrand_eq_packetIntegrand (t : Θ) (s : OrbitSelection a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (g : rationalPoints G) :
    characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hT C Q t s f g =
      fun ω => density t ω * coefficient(t) ⟨fam f t, hsm⟩ ω g := by
  funext ω
  unfold characterIntegrand
  congr 1
  have key : ∀ (A : ComponentOrbitRepresentative a ha mu t) (ω' : GlobalForm.OrbitPoint a ha mu t),
      componentOrbitPoint a ha mu t A = ω' →
        formalDegreeCharacter hG hi hnu hKc hPK rho hsw a ha mu d hT t A f g =
          coefficient(t) ⟨fam f t, hsm⟩ ω' g := by
    rintro A ω' rfl
    erw [SourcePacket.coefficientMap_representative hG (chosenLeviModel t.1) (C.presentation t.1)
      (d t.1) (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
      ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1)
      (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
      ⟨fam f t, hsm⟩ A]
    exact formalDegreeCharacter_eq_coefficient hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT t A f g
  exact key (s.1 ω) ω (s.2 ω)

/-- When `psi_f[O,P]` is a smooth section, each integrand of VIII.1 (3) is integrable:
it is continuous on the compact orbit. -/
theorem integrable_characterIntegrand (t : Θ) (s : OrbitSelection a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (g : rationalPoints G) :
    Integrable (characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hT C Q t s f g)
      (measureAt t) := by
  rw [characterIntegrand_eq_packetIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C Q t s f
    hsm g]
  let : CompactSpace (GlobalForm.OrbitPoint a ha mu t) :=
    SourcePacket.sourceOrbit_compactSpace (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
      (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
  have hd : Continuous (density t) :=
    SourceForm.continuous_orbitDensity hG (chosenLeviModel t.1) (C.presentation t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
      ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1)
      (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
      (Q t)
  have hc := SourcePacket.continuous_coefficient hG (chosenLeviModel t.1) (C.presentation t.1)
    (d t.1) (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
    ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
    ⟨fam f t, hsm⟩ g
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hd.mul hc⟩).integrable (measureAt t)

/-- When `psi_f[O,P]` is a smooth section, its actual source packet at `g` is the orbit
integral of VIII.1 (3). -/
theorem componentPacket_eq_characterOrbitIntegral (t : Θ) (s : OrbitSelection a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (g : rationalPoints G) :
    packet t ⟨fam f t, hsm⟩ g =
      characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q t s f g := by
  unfold characterOrbitIntegral
  rw [characterIntegrand_eq_packetIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C Q t s f
    hsm g]
  rfl

/-- The classes contributing to VIII.1 (3) meet the literal support of `psi_f`, when
all components are smooth. -/
theorem support_characterSummand_subset (s : ∀ t : Θ, OrbitSelection a ha mu t)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (g : rationalPoints G) :
    Function.support (fun t : Θ => (Association.coefficientAtRepresentative C K0 hK0 t : ℂ) *
        characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q t (s t) f g) ⊆
      rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f) := by
  intro t ht
  change fam f t ≠ 0
  intro hz
  apply ht
  change (Association.coefficientAtRepresentative C K0 hK0 t : ℂ) *
      characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q t (s t) f g = 0
  rw [← componentPacket_eq_characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
    hindex Q t (s t) f (hsm t) g]
  have h0 : (⟨fam f t, hsm t⟩ : rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) = 0 :=
    Subtype.ext hz
  rw [h0, map_zero, Pi.zero_apply, mul_zero]

/-- VII.1.1 (iii) and VII.2.4 identify the actual synthesis of the invariant lift of
`psi_f` with the right side of VIII.1 (3), for every set of association
representatives and every selection of inducing objects. -/
theorem weightedSynthesis_eq_characterInversionSum
    (hassoc : Association.AssociationFormulaStatement C K0 hK0 hindex Q)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f)
    (R : Association.Representatives.{u, uV} a ha mu) (s : ∀ t : Θ, OrbitSelection a ha mu t)
    (g : rationalPoints G) :
    weightedSynthesis hG a ha mu d C.presentation hindex Q K0 hK0
        (fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf).val g =
      characterInversionSum hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q K0 hK0 R s f g := by
  rw [(hassoc R).1, Association.packetRepresentativeSum_eq_finiteSum]
  unfold characterInversionSum
  rw [Association.representativeSum_eq_sum a ha mu R _ hf.1.2
    (support_characterSummand_subset hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0
      hK0 s f hf.1.1 g)]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact componentPacket_eq_characterOrbitIntegral hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
    hindex Q (R.select c) (s (R.select c)) f (hf.1.1 (R.select c)) g

section Statements

variable
  (hsynth : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K0 hK0 hKc hPK rho)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K0) (hQ : ∀ theta : Θ, (Q theta).compact = K0)

/-- VIII.1 (1) and (2) give (3), by VII.1.1 (iii) and the VII.2.4 association formula. -/
theorem characterInversion_of_fourierInversion
    (hassoc : Association.AssociationFormulaStatement C K0 hK0 hindex Q)
    (h : FourierInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
      hsynth hspecial hd hQ) :
    CharacterInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q K0 hK0 := by
  intro f g R s
  obtain ⟨hf, hrec⟩ := h f
  refine ⟨fun t => integrable_characterIntegrand hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
    hindex Q t (s t) f (hf.1.1 t) g, ?_, ?_⟩
  · exact (hf.1.2.image (Association.classOf a ha mu)).subset
      (Association.support_representativeSummand_subset a ha mu R
        (support_characterSummand_subset hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q
          K0 hK0 s f hf.1.1 g))
  · exact (congrArg (fun F : RationalSchwartzSpace hKc hPK rho => F g) hrec).symm.trans
      (weightedSynthesis_eq_characterInversionSum hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
        hindex Q K0 hK0 hassoc f hf R s g)

/-- Under VII.2.4, the character formula (3) gives the reconstruction (2) by the actual
`κ` of every Schwartz function whose Fourier family lies in `C^∞(Θ)_inv`. -/
theorem synthesisReconstruction_of_characterInversion
    (hassoc : Association.AssociationFormulaStatement C K0 hK0 hindex Q)
    (h : CharacterInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q K0 hK0) :
    SynthesisReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
      hsynth hspecial hd hQ := by
  intro f hf
  ext g
  obtain ⟨-, -, hfg⟩ := h f g (Association.Representatives.ofQuotient a ha mu)
    (fun t => OrbitSelection.choose a ha mu t)
  exact (weightedSynthesis_eq_characterInversionSum hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
    hindex Q K0 hK0 hassoc f hf _ _ g).trans hfg.symm

/-- Under VII.2.4 and invariant-carrier membership of every `psi_f`, formula (3) is
equivalent to VIII.1 (1) and (2) for the actual `κ`. -/
theorem characterInversion_iff_fourierInversion
    (hassoc : Association.AssociationFormulaStatement C K0 hK0 hindex Q)
    (hlift : FourierInvariantLiftStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C) :
    CharacterInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hT C hindex Q K0 hK0 ↔
      FourierInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
        hsynth hspecial hd hQ :=
  ⟨fun h => (fourierInversionStatement_iff hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q
      K0 hK0 hsynth hspecial hd hQ).mpr
      ⟨hlift, synthesisReconstruction_of_characterInversion hG hi hnu hKc hPK rho hsw a ha mu d
        hdelta hT C hindex Q K0 hK0 hsynth hspecial hd hQ hassoc h⟩,
    characterInversion_of_fourierInversion hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q
      K0 hK0 hsynth hspecial hd hQ hassoc⟩

end Statements

end Character

end FixedData

/-- Local VIII.1 (3) for one group: for all normalized source data (one source special
compact `K` serving as the Schwartz compact and the compact of every compact picture and
scalar datum, a source height `rho`, that is a closed matrix embedding with `K` in its
integral subgroup, the Haar measure `RationalDynamicSource.ambientHaar K hK` of mass one
on `K`, and the I.1 split-central quotient Haar measures), the character inversion
formula holds. -/
def RationalLocalCharacterInversionStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho)
    (_hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
    [∀ t, IsAffine (T t).X.left]
    (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
    (ha : ∀ t, IsSplitComponent (a t))
    [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
    [∀ t, (rationalPoints.map (a t)).range.Normal]
    [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
    [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
    (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A.obj).representation)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
    (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
    (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
      OrbitPacketData (C.presentation theta.1)
        (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
          (mu theta.1) theta.2)),
    IsSourceCompactAt i K.toSubgroup →
    (∀ t, (d t).compact = K) →
    (∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K) →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    haveI := sourceAmbientHaar_isMulRightInvariant hG hK
    CharacterInversionStatement hG hi hnu hK hPK rho hsw a ha mu d hT C hindex Q K hK

/-- All-field, all-group closure of local VIII.1 (3). -/
def RationalCharacterInversionGlobalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    RationalLocalCharacterInversionStatement.{u, uV} G

end Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion

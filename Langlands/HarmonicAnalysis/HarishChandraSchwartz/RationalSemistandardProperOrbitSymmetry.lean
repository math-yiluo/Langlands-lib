import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierCharacterSymmetry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaParts

/-! # Orbit comparisons for the proper Fourier synthesis in VIII.2.2 -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (muM : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (muM t).IsHaarMeasure] [∀ t, (muM t).IsInvInvariant]

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha muM
set_option hygiene false in
local notation "Orb(" p ")" =>
  OrbitClass.{u, uV} (chosenLeviModel (p)) (a (p)) (ha (p)) (muM (p))
set_option hygiene false in
local notation "Rep(" p ")" => IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi (p))
set_option hygiene false in
local notation "model(" t ")" => chosenLeviModel (t : Theta).1
set_option hygiene false in
local notation "center(" t ")" => (model(t)).splitCenter (a (t : Theta).1)
set_option hygiene false in
local notation "central(" t ")" => (model(t)).splitCenter_le_center (a (t : Theta).1) (ha (t : Theta).1)
set_option hygiene false in
local notation "rep(" t ")" =>
  orbitRepresentative (model(t)) (a (t : Theta).1) (ha (t : Theta).1) (muM (t : Theta).1) (t : Theta).2
set_option hygiene false in
local notation "sq(" t ")" =>
  orbitRepresentative_isSquareIntegrable (model(t)) (a (t : Theta).1) (ha (t : Theta).1)
    (muM (t : Theta).1) (t : Theta).2

/-- The actual inducing objects parametrizing the coherent sections of a component. -/
abbrev ComponentOrbitRepresentative (t : Theta) :=
  UnitaryOrbitRepresentative (model(t)).normCharacters (rep(t))

/-- The class of an actual inducing object in the orbit used by the source integral. -/
abbrev componentOrbitPoint (t : Theta) (A : ComponentOrbitRepresentative a ha muM t) :
    GlobalForm.OrbitPoint a ha muM t :=
  unitaryOrbitRepresentativeDiscreteSeriesOrbit (model(t)).normCharacters (rep(t))
    (center(t)) (central(t)) (muM t.1) (sq(t)) A

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, (muM t).IsInvInvariant] in
theorem componentOrbitPoint_surjective (t : Theta) :
    Function.Surjective (componentOrbitPoint a ha muM t) :=
  unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective (model(t)).normCharacters (rep(t))
    (center(t)) (central(t)) (muM t.1) (sq(t))

variable (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)

/-- The Haar measure in the actual I.1 and VI.3 orbit integral. -/
abbrev componentOrbitMeasure (t : Theta) : Measure (GlobalForm.OrbitPoint a ha muM t) :=
  SourceMeasure.normalizedOrbitMeasure (model(t)) (a t.1) (ha t.1) (hindex t.1)
    (muM t.1) (discreteSeriesClass (center(t)) (central(t)) (muM t.1) (rep(t)) (sq(t)))

/-- The Schur degree of this actual representative for the quotient Haar
used in VII.1.1(iii). -/
abbrev componentFormalDegree (t : Theta) (A : ComponentOrbitRepresentative a ha muM t) : ℝ :=
  representationFormalDegree (center(t)) (central(t)) (muM t.1) (compactOpenCofinal t.1 (d t.1))
    (unitaryOrbitRepresentative_isDiscreteSeries (model(t)).normCharacters (rep(t))
      (center(t)) (central(t)) (muM t.1) (sq(t)) A) A.val.property.1

variable (hG : IsConnectedReductive G)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (Q : ∀ t : Theta, OrbitPacketData (rs t.1) (rep(t)))

set_option hygiene false in
local notation "measureAt" => componentOrbitMeasure a ha muM hindex
set_option hygiene false in
local notation "degreeAt" => componentFormalDegree a ha muM d
set_option hygiene false in
local notation "density" => GlobalForm.componentDensity hG a ha muM rs Q

/-- Data for an orbit symmetry at a fixed literal parabolic. The analytic
comparisons concern the actual normalized measure, density and Schur degree.
The relation on representatives specifies the underlying operation. -/
structure ProperOrbitSymmetry
    (e : ∀ p : SemistandardSpectralIndex i, Orb(p) ≃ Orb(p))
    (rel : ∀ p : SemistandardSpectralIndex i, Rep(p) → Rep(p) → Prop) where
  pointEquiv (p : SemistandardSpectralIndex i) (hp : p.IsProper) (O : Orb(p)) :
    GlobalForm.OrbitPoint a ha muM ⟨p, O⟩ ≃ₜ GlobalForm.OrbitPoint a ha muM ⟨p, e p O⟩
  measurePreserving (p : SemistandardSpectralIndex i) (hp : p.IsProper) (O : Orb(p)) :
    MeasurePreserving (pointEquiv p hp O) (measureAt ⟨p, O⟩) (measureAt ⟨p, e p O⟩)
  representative (p : SemistandardSpectralIndex i) (hp : p.IsProper) (O : Orb(p))
      (A : ComponentOrbitRepresentative a ha muM ⟨p, O⟩) :
    ∃ B : ComponentOrbitRepresentative a ha muM ⟨p, e p O⟩,
      pointEquiv p hp O (componentOrbitPoint a ha muM ⟨p, O⟩ A) =
        componentOrbitPoint a ha muM ⟨p, e p O⟩ B ∧
      rel p A.val B.val ∧
      degreeAt ⟨p, O⟩ A = degreeAt ⟨p, e p O⟩ B
  density_eq (p : SemistandardSpectralIndex i) (hp : p.IsProper) (O : Orb(p))
      (omega : GlobalForm.OrbitPoint a ha muM ⟨p, O⟩) :
    density ⟨p, e p O⟩ (pointEquiv p hp O omega) = density ⟨p, O⟩ omega

/-- The actual contragredient comparison at every proper semistandard index. -/
def ProperOrbitCheckComparisonStatement : Prop :=
  ∃ e : ∀ p : SemistandardSpectralIndex i, Orb(p) ≃ Orb(p),
    Nonempty (ProperOrbitSymmetry a ha muM d hindex hG rs Q e fun _ A B =>
      Nonempty ((smoothContragredient A.obj.representation).Equiv B.obj.representation))

/-- The actual conjugate-complex-space comparison at every proper
semistandard index. -/
def ProperOrbitConjComparisonStatement : Prop :=
  ∃ e : ∀ p : SemistandardSpectralIndex i, Orb(p) ≃ Orb(p),
    Nonempty (ProperOrbitSymmetry a ha muM d hindex hG rs Q e fun _ A B =>
      Nonempty ((ConjSpace.rep A.obj.representation).Equiv B.obj.representation))

/-- The actual ambient unitary twist is an internal translation on each
proper orbit. Its density identity is the `mu(omega ⊗ χ) = mu(omega)` of VIII.2.2. -/
def ProperOrbitTwistComparisonStatement : Prop :=
  ∀ χ : rationalUnitaryUnramifiedCharacters G,
    Nonempty (ProperOrbitSymmetry a ha muM d hindex hG rs Q (fun _ => Equiv.refl _) fun p A B =>
      Nonempty ((Langlands.twist (χ.val.toMonoidHom.comp (levi p).subtype)
        A.obj.representation).Equiv B.obj.representation))

/-- The portion of density reality needed for complex conjugation of the
proper orbit integrals. -/
def ProperOrbitDensityRealStatement : Prop :=
  ∀ (t : Theta), t.1.IsProper → ∀ omega : GlobalForm.OrbitPoint a ha muM t,
    conj (density t omega) = density t omega

/-- The orbit comparisons underlying the three proper synthesis symmetries. -/
def ProperOrbitSymmetryStatement : Prop :=
  ProperOrbitCheckComparisonStatement a ha muM d hindex hG rs Q ∧
  ProperOrbitConjComparisonStatement a ha muM d hindex hG rs Q ∧
  ProperOrbitTwistComparisonStatement a ha muM d hindex hG rs Q ∧
  ProperOrbitDensityRealStatement a ha muM hG rs Q

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

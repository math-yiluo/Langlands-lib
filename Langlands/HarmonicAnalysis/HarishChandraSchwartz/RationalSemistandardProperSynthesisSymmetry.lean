import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperOrbitSymmetry
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Symmetries of the proper Fourier synthesis in VIII.2.2 -/

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

local instance properSynthesisCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance properSynthesisParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "C" => RationalSchwartzSpace hKc hPK rho
set_option hygiene false in
local notation "leftTranslate" =>
  Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) 1
set_option hygiene false in
local notation "checkC" =>
  Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)

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
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha muM
set_option hygiene false in
local notation "Orb(" p ")" =>
  OrbitClass.{u, uV} (chosenLeviModel (p)) (a (p)) (ha (p)) (muM (p))
set_option hygiene false in
local notation "Rep(" p ")" => IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi (p))
set_option hygiene false in
local notation "SquareInt(" p "," A ")" => IsSquareIntegrableModCentralSubgroup
  ((chosenLeviModel (p)).splitCenter (a (p)))
  ((chosenLeviModel (p)).splitCenter_le_center (a (p)) (ha (p))) (A).obj.representation (muM (p))
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
set_option hygiene false in
local notation "sqAt(" t "," A ")" =>
  unitaryOrbitRepresentative_isDiscreteSeries (model(t)).normCharacters (rep(t))
    (center(t)) (central(t)) (muM (t : Theta).1) (sq(t)) (A)

variable (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ t : Theta, OrbitPacketData (rs t.1) (rep(t)))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i) (A : Rep(p)), SquareInt(p,A) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
local notation "SmoothSections" => rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d
set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d
set_option hygiene false in
local notation "sectionAt" => rationalSemistandardThetaComponent a ha muM d
set_option hygiene false in
local notation "density" => GlobalForm.componentDensity hG a ha muM rs Q
set_option hygiene false in
local notation "measureAt" => componentOrbitMeasure a ha muM hindex
set_option hygiene false in
local notation "degreeAt" => componentFormalDegree a ha muM d
set_option hygiene false in
local notation "pointAt" => componentOrbitPoint a ha muM
set_option hygiene false in
local notation "coefficient(" t ")" =>
  SourcePacket.coefficientMap hG (model(t)) (rs (t : Theta).1) (d (t : Theta).1) (rep(t))
    (center(t)) (central(t)) (muM (t : Theta).1) (sq(t))
set_option hygiene false in
local notation "packet" => componentPacket hG a ha muM d rs hindex Q
set_option hygiene false in
local notation "weight" => sourceWeight hG rs K0 hK0
set_option hygiene false in
local notation "character" => semistandardInducedSchwartzCharacter hKc hPK rho a ha muM d hsw hT
set_option hygiene false in
local notation "fourier" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

variable (hsm : ∀ (f : C) (t : Theta), t.1.IsProper → fourier f t ∈ component t)
  (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT)

set_option hygiene false in
local notation "properLift" =>
  rationalSemistandardFourierThetaProperSmoothFamily hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT hsm hfs

/-- The actual raw source synthesis applied to the finitely supported proper
Fourier family. -/
def properFourierSynthesis : C →ₗ[ℂ] (rationalPoints G → ℂ) :=
  (weightedSynthesis hG a ha muM d rs hindex Q K0 hK0).comp properLift

set_option hygiene false in
local notation "properSynthesis" =>
  properFourierSynthesis hG hi hnu hKc hPK rho a ha muM d rs hindex Q K0 hK0 hsw hdelta hT hsm hfs

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
private theorem properFourierCoefficient_trace (t : Theta) (ht : t.1.IsProper)
    (A : ComponentOrbitRepresentative a ha muM t) (f : C) (g : rationalPoints G) :
    coefficient(t) (sectionAt t (properLift f)) (pointAt t A) g =
      (degreeAt t A : ℂ) * character t.1 A.val (sqAt(t,A)) (leftTranslate g (checkC f)) := by
  erw [SourcePacket.coefficientMap_representative hG (model(t)) (rs t.1) (d t.1)
    (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) (sectionAt t (properLift f)) A]
  have hval : (sectionAt t (properLift f)).val A = fourier f t A :=
    congrFun (rationalSemistandardThetaProperPart_apply_of_mem ht (fourier f)) A
  rw [hval]
  exact rationalSemistandardFourier_trace hG hi hnu hKc hPK rho hsw t.1 (d t.1) (hdelta t.1)
    A.val.obj (center(t)) (central(t)) (muM t.1) (sqAt(t,A)) A.val.property.1
    (hT t.1 A.val (sqAt(t,A))) f g

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
private theorem properFourierComponent_zero (t : Theta) (ht : ¬ t.1.IsProper) (f : C) :
    sectionAt t (properLift f) = 0 :=
  Subtype.ext (rationalSemistandardThetaProperPart_apply_of_not_mem ht (fourier f))

omit [∀ t, (muM t).IsInvInvariant] in
private theorem componentPacket_eq_orbitIntegral (t : Theta) (v : component t)
    (g : rationalPoints G) :
    packet t v g = ∫ omega, density t omega * coefficient(t) v omega g ∂measureAt t :=
  rfl

omit [∀ t, (muM t).IsInvInvariant] in
private theorem componentOrbitIntegrable (t : Theta) (v : component t) (g : rationalPoints G) :
    Integrable (fun omega => density t omega * coefficient(t) v omega g) (measureAt t) := by
  let : CompactSpace (GlobalForm.OrbitPoint a ha muM t) :=
    SourcePacket.sourceOrbit_compactSpace (model(t)) (a t.1) (ha t.1) (muM t.1) (rep(t)) (sq(t))
  have hd : Continuous (density t) :=
    SourceForm.continuous_orbitDensity hG (model(t)) (rs t.1) (rep(t))
      (center(t)) (central(t)) (muM t.1) (sq(t)) (Q t)
  have hc := SourcePacket.continuous_coefficient hG (model(t)) (rs t.1) (d t.1)
    (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) v g
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hd.mul hc⟩).integrable (measureAt t)

variable {e : ∀ p : SemistandardSpectralIndex i, Orb(p) ≃ Orb(p)}
  {rel : ∀ p : SemistandardSpectralIndex i, Rep(p) → Rep(p) → Prop}

set_option hygiene false in
local notation "orbitComparison" => ProperOrbitSymmetry a ha muM d hindex hG rs Q e rel

set_option maxHeartbeats 2500000 in
private theorem componentPacket_compare (orbit : orbitComparison)
    (p : SemistandardSpectralIndex i) (hp : p.IsProper) (O : Orb(p))
    (f f' : C) (x y : rationalPoints G) (L : ℂ →L[ℝ] ℂ)
    (hMul : ∀ (omega : GlobalForm.OrbitPoint a ha muM ⟨p, O⟩) (z : ℂ),
      L (density ⟨p, O⟩ omega * z) = density ⟨p, O⟩ omega * L z)
    (hChar : ∀ (A B : Rep(p)) (hA : SquareInt(p,A)) (hB : SquareInt(p,B)),
      rel p A B → L (character p A hA (leftTranslate x (checkC f))) =
        character p B hB (leftTranslate y (checkC f'))) :
    L (packet ⟨p, O⟩ (sectionAt ⟨p, O⟩ (properLift f)) x) =
      packet ⟨p, e p O⟩ (sectionAt ⟨p, e p O⟩ (properLift f')) y := by
  let t : Theta := ⟨p, O⟩
  let t' : Theta := ⟨p, e p O⟩
  let transport := orbit.pointEquiv p hp O
  let v := sectionAt t (properLift f)
  let v' := sectionAt t' (properLift f')
  let F₁ := fun omega => density t omega * coefficient(t) v omega x
  let F₂ := fun omega => density t' omega * coefficient(t') v' omega y
  change L (packet t v x) = packet t' v' y
  calc
    _ = L (∫ omega, F₁ omega ∂measureAt t) :=
      congrArg L (componentPacket_eq_orbitIntegral hG a ha muM d rs hindex Q t v x)
    _ = ∫ omega, L (F₁ omega) ∂measureAt t :=
      (L.integral_comp_comm (componentOrbitIntegrable hG a ha muM d rs hindex Q t v x)).symm
    _ = ∫ omega, F₂ (transport omega) ∂measureAt t := ?_
    _ = ∫ omega, F₂ omega ∂measureAt t' :=
      (orbit.measurePreserving p hp O).integral_comp transport.measurableEmbedding F₂
    _ = _ := (componentPacket_eq_orbitIntegral hG a ha muM d rs hindex Q t' v' y).symm
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  obtain ⟨A, rfl⟩ := componentOrbitPoint_surjective a ha muM t omega
  obtain ⟨B, hB, hR, hD⟩ := orbit.representative p hp O A
  change L (density t (pointAt t A) * coefficient(t) v (pointAt t A) x) =
    density t' (transport (pointAt t A)) * coefficient(t') v' (transport (pointAt t A)) y
  rw [hMul, orbit.density_eq p hp O, hB]
  change density t (pointAt t A) * L (coefficient(t) (sectionAt t (properLift f)) (pointAt t A) x) =
    density t (pointAt t A) * coefficient(t') (sectionAt t' (properLift f')) (pointAt t' B) y
  rw [properFourierCoefficient_trace hG hi hnu hKc hPK rho a ha muM d rs hsw hdelta hT hsm hfs
      t hp A f x,
    properFourierCoefficient_trace hG hi hnu hKc hPK rho a ha muM d rs hsw hdelta hT hsm hfs
      t' hp B f' y]
  congr 1
  calc
    _ = (degreeAt t A : ℂ) * L (character p A.val (sqAt(t,A)) (leftTranslate x (checkC f))) := by
      simpa only [Complex.real_smul] using L.map_smul (degreeAt t A)
        (character p A.val (sqAt(t,A)) (leftTranslate x (checkC f)))
    _ = _ := by rw [hD, hChar A.val B.val (sqAt(t,A)) (sqAt(t',B)) hR]

set_option hygiene false in
local notation "summand(" v "," g ")" => fun t : Theta =>
  (weight t.1 : ℂ) * packet t (sectionAt t (v)) (g)

omit [∀ t, (muM t).IsInvInvariant] in
private theorem weightedPacket_support_subset (v : SmoothSections) (g : rationalPoints G) :
    Function.support summand(v,g) ⊆ FiniteSupportSections.support v.val := by
  intro t ht
  change v.val t ≠ 0
  intro hz
  have hzero : sectionAt t v = 0 := Subtype.ext hz
  exact ht (by change (weight t.1 : ℂ) * packet t (sectionAt t v) g = 0; simp [hzero])

private theorem properSynthesis_apply_finsum (f : C) (g : rationalPoints G) :
    properSynthesis f g = ∑ᶠ t, (weight t.1 : ℂ) * packet t (sectionAt t (properLift f)) g := by
  change weightedSynthesis hG a ha muM d rs hindex Q K0 hK0 (properLift f) g = _
  rw [weightedSynthesis_apply]
  symm
  apply finsum_eq_sum_of_support_subset
  intro t ht
  exact (properLift f).property.2.mem_toFinset.mpr
    (weightedPacket_support_subset hG a ha muM d rs hindex Q K0 hK0 (properLift f) g ht)

set_option maxHeartbeats 2500000 in
private theorem properSynthesis_compare (orbit : orbitComparison)
    (f f' : C) (x y : rationalPoints G) (L : ℂ →L[ℝ] ℂ)
    (hMul : ∀ (t : Theta), t.1.IsProper →
      ∀ (omega : GlobalForm.OrbitPoint a ha muM t) (z : ℂ),
        L (density t omega * z) = density t omega * L z)
    (hChar : ∀ (p : SemistandardSpectralIndex i) (A B : Rep(p))
      (hA : SquareInt(p,A)) (hB : SquareInt(p,B)),
      rel p A B → L (character p A hA (leftTranslate x (checkC f))) =
        character p B hB (leftTranslate y (checkC f'))) :
    L (properSynthesis f x) = properSynthesis f' y := by
  simp only [properSynthesis_apply_finsum]
  have hfinite := (properLift f).property.2.subset
    (weightedPacket_support_subset hG a ha muM d rs hindex Q K0 hK0 (properLift f) x)
  change L.toLinearMap.toAddMonoidHom (∑ᶠ t, summand(properLift f,x) t) = _
  rw [L.toLinearMap.toAddMonoidHom.map_finsum hfinite]
  apply finsum_eq_of_bijective (Equiv.sigmaCongrRight e) (Equiv.sigmaCongrRight e).bijective
  rintro ⟨p, O⟩
  change L ((weight p : ℂ) * packet ⟨p, O⟩ (sectionAt ⟨p, O⟩ (properLift f)) x) =
    (weight p : ℂ) * packet ⟨p, e p O⟩ (sectionAt ⟨p, e p O⟩ (properLift f')) y
  by_cases hp : p.IsProper
  · calc
      _ = (weight p : ℂ) * L (packet ⟨p, O⟩ (sectionAt ⟨p, O⟩ (properLift f)) x) := by
        simpa only [Complex.real_smul] using L.map_smul (weight p)
          (packet ⟨p, O⟩ (sectionAt ⟨p, O⟩ (properLift f)) x)
      _ = _ := congrArg ((weight p : ℂ) * ·)
        (componentPacket_compare hG hi hnu hKc hPK rho a ha muM d rs hindex Q hsw hdelta hT hsm hfs
          orbit p hp O f f' x y L (hMul ⟨p, O⟩ hp) (hChar p))
  · have hz := properFourierComponent_zero hG hi hnu hKc hPK rho a ha muM d hsw hdelta hT hsm hfs
      ⟨p, O⟩ hp f
    have hz' := properFourierComponent_zero hG hi hnu hKc hPK rho a ha muM d hsw hdelta hT hsm hfs
      ⟨p, e p O⟩ hp f'
    simp only [hz, hz', map_zero, Pi.zero_apply, mul_zero]

/-- The three VIII.2.2 comparisons on the actual subtracted synthesis term. -/
def ProperFourierSynthesisSymmetryStatement : Prop :=
  SemistandardInducedCharacterSymmetryStatement hG hi hnu hKc hPK rho a ha muM d hsw hT →
    ProperOrbitSymmetryStatement a ha muM d hindex hG rs Q →
      ∀ (f : C) (g : rationalPoints G),
        properSynthesis f g⁻¹ = properSynthesis (checkC f) g ∧
        conj (properSynthesis f g) = properSynthesis (Space.complexConj f) g ∧
        ∀ χ : rationalUnitaryUnramifiedCharacters G,
          properSynthesis f g * (χ.val g : ℂ) =
            properSynthesis (rationalSchwartzUnitaryTwist hG hKc hPK rho χ f) g

/-- VII.1.1(iii), measure transport, and sum reindexing give all three
proper-synthesis comparisons. -/
theorem properFourierSynthesis_symmetry :
    ProperFourierSynthesisSymmetryStatement hG hi hnu hKc hPK rho a ha muM d rs hindex Q K0 hK0
      hsw hdelta hT hsm hfs := by
  intro hchar horbit f g
  rcases horbit with ⟨⟨eCheck, ⟨hCheck⟩⟩, ⟨eConj, ⟨hConj⟩⟩, hTwist, hReal⟩
  refine ⟨?_, ?_, ?_⟩
  · exact properSynthesis_compare hG hi hnu hKc hPK rho a ha muM d rs hindex Q K0 hK0
      hsw hdelta hT hsm hfs hCheck f (checkC f) g⁻¹ g (ContinuousLinearMap.id ℝ ℂ)
      (fun _ _ _ _ => rfl) (fun p A B hA hB h => by
        simpa only [ContinuousLinearMap.id_apply, Space.check_check] using hchar.1 p A B hA hB h f g)
  · exact properSynthesis_compare hG hi hnu hKc hPK rho a ha muM d rs hindex Q K0 hK0
      hsw hdelta hT hsm hfs hConj f (Space.complexConj f) g g Complex.conjCLE.toContinuousLinearMap
      (fun t ht omega z => by
        change conj (density t omega * z) = density t omega * conj z
        rw [map_mul, hReal t ht omega])
      (fun p A B hA hB h => hchar.2.1 p A B hA hB h f g)
  · intro χ
    obtain ⟨hχ⟩ := hTwist χ
    let mulChar : ℂ →L[ℝ] ℂ := (χ.val g : ℂ) • ContinuousLinearMap.id ℝ ℂ
    have hmul (t : Theta) (_ : t.1.IsProper) (omega : GlobalForm.OrbitPoint a ha muM t) (z : ℂ) :
        mulChar (density t omega * z) = density t omega * mulChar z :=
      mul_left_comm (χ.val g : ℂ) (density t omega) z
    simpa only [mulChar, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      mul_comm (χ.val g : ℂ)] using
      properSynthesis_compare hG hi hnu hKc hPK rho a ha muM d rs hindex Q K0 hK0
        hsw hdelta hT hsm hfs hχ f (rationalSchwartzUnitaryTwist hG hKc hPK rho χ f) g g mulChar
        hmul (fun p A B hA hB h => hchar.2.2 χ p A B hA hB h f g)

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

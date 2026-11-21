import Langlands.Representation.Plancherel.ActualConjugateLeviTwist
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalarTransport
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Plancherel.OppositeIntertwiningHermitianAdjunction
import Langlands.Representation.Plancherel.NestedStandardIntertwiningIntegral

/-! # Conjugation of the canonical opposite scalar (Waldspurger IV.3 (3)) -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open OppositeIntertwiningHermitianAdjunction Haar

universe u uV

section InducedSections

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U P' M' U' : Subgroup H}
  (d : IsSemidirectDecomposition P M U) (d' : IsSemidirectDecomposition P' M' U')
  (e : H ≃ₜ* H) (hP : ∀ x, x ∈ P' ↔ e x ∈ P) (hM : ∀ x, x ∈ M' ↔ e x ∈ M)
  (hU : ∀ x, x ∈ U' ↔ e x ∈ U)

set_option hygiene false in
local notation "eM" => GroupTransport.subgroupEquiv e hM
set_option hygiene false in
local notation "eP" => GroupTransport.subgroupEquiv e hP

private def compactSectionTransport (K K' : OpenSubgroup H)
    (eK : K' ≃ₜ* K) (heK : ∀ k : K', (eK k : H) = e (k : H))
    (A : SmoothRep.{0, u, uV} ℂ M) :
    CompactInductionPicture d K A ≃ₗ[ℂ] CompactInductionPicture d' K' (SmoothRep.pullback eM A) := by
  letI : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  letI : IsTopologicalGroup K' := inferInstanceAs (IsTopologicalGroup K'.toSubgroup)
  let ePK := GroupTransport.subgroupEquiv eK
    (show ∀ k : K', k ∈ P'.comap K'.toSubgroup.subtype ↔
      eK k ∈ P.comap K.toSubgroup.subtype from fun k => by
        change (k : H) ∈ P' ↔ (eK k : H) ∈ P
        rw [heK, hP])
  refine (precomposeSmoothInducedGroupEquiv eK ePK.toMulEquiv (fun _ => rfl) ?_).toLinearEquiv
  intro p
  let pp : P' := K'.toSubgroup.subtype.subgroupComap P' p
  change A.representation (d.projection (K.toSubgroup.subtype.subgroupComap P (ePK p))) =
    A.representation (eM (d'.projection pp))
  rw [GroupTransport.projection_transport d d' e hP hM hU pp]
  congr 2
  exact Subtype.ext (heK p.val)

private def compactSectionEval (d : IsSemidirectDecomposition P M U) (K : OpenSubgroup H)
    (A : SmoothRep.{0, u, uV} ℂ M) (f : CompactInductionPicture d K A) : K → A :=
  eval _ _ f

omit [LocallyCompactSpace H] in
private theorem compactSectionTransport_eval (K K' : OpenSubgroup H)
    (eK : K' ≃ₜ* K) (heK : ∀ k : K', (eK k : H) = e (k : H))
    (A : SmoothRep.{0, u, uV} ℂ M) (f : CompactInductionPicture d K A) (k : K') :
    compactSectionEval d' K' (SmoothRep.pullback eM A)
        (compactSectionTransport d d' e hP hM hU K K' eK heK A f) k =
      compactSectionEval d K A f (eK k) :=
  rfl

variable (eM' : M' ≃ₜ* M) (heM' : ∀ m, eM' m = eM m)
  (cU : IsClosed (U : Set H)) (cU' : IsClosed (U' : Set H))
  (B : SmoothRep.{0, u, uV} ℂ M) (ρ' : Representation ℂ M' B) (hs' : IsSmooth ρ')
  (hρ : ρ' = B.representation.comp eM'.toMonoidHom)

set_option hygiene false in
local notation "B'" => SmoothRep.of ρ' hs'
set_option hygiene false in
set_option quotPrecheck false in
local notation "I" => (DynamicNormalization.leviTwistedInductionFunctor d cU).obj B
set_option hygiene false in
set_option quotPrecheck false in
local notation "I'" => (DynamicNormalization.leviTwistedInductionFunctor d' cU').obj B'

include hM hU heM' hρ in
private def inducedSectionTransport :
    Representation.Equiv ((I).representation.comp e.toMonoidHom) (I').representation := by
  refine precomposeSmoothInducedGroupEquiv e (eP).toMulEquiv (fun _ => rfl) ?_
  intro p
  change (↑(HaarModulus.closedHalfCharacter U cU M d.levi_le_normalizer
    (d.projection (eP p))) : ℂ) • B.representation (d.projection (eP p)) =
    (↑(HaarModulus.closedHalfCharacter U' cU' M' d'.levi_le_normalizer
    (d'.projection p)) : ℂ) • ρ' (d'.projection p)
  simp only [GroupTransport.closedHalfCharacter_transport e hU hM cU cU'
    d.levi_le_normalizer d'.levi_le_normalizer, hρ, MonoidHom.comp_apply,
    ← GroupTransport.projection_transport d d' e hP hM hU]
  rw [show eM'.toMonoidHom (d'.projection p) = eM (d'.projection p) from heM' _]

private def leviSectionEval
    (d : IsSemidirectDecomposition P M U) (cU : IsClosed (U : Set H))
    (B : SmoothRep.{0, u, uV} ℂ M)
    (f : (DynamicNormalization.leviTwistedInductionFunctor d cU).obj B) : H → B :=
  eval P (leviInflatedInducingRepresentation d cU B) f

private theorem leviSectionEval_injective
    (d : IsSemidirectDecomposition P M U) (cU : IsClosed (U : Set H))
    (B : SmoothRep.{0, u, uV} ℂ M) : Function.Injective (leviSectionEval d cU B) := by
  intro f f' h
  exact Subtype.ext (Subtype.ext h)

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] in
private theorem compactSectionEval_injective (d : IsSemidirectDecomposition P M U)
    (K : OpenSubgroup H) (A : SmoothRep.{0, u, uV} ℂ M) :
    Function.Injective (compactSectionEval d K A) := by
  intro f f' h
  exact Subtype.ext (Subtype.ext h)

end InducedSections

section TwistTransport

variable {M M' : Type u} [Group M] [Group M'] [TopologicalSpace M] [TopologicalSpace M']
  (eM : M' ≃ₜ* M) (A : SmoothRep.{0, u, uV} ℂ M)
  (α : M →* ℂˣ) (β : M' →* ℂˣ)

private theorem twist_comp_of_apply_eq (h : ∀ m, β m = α (eM m)) :
    Langlands.twist β (A.representation.comp eM.toMonoidHom) =
      (Langlands.twist α A.representation).comp eM.toMonoidHom := by
  apply MonoidHom.ext
  intro m
  apply LinearMap.ext
  intro v
  change (β m : ℂ) • A.representation (eM m) v = (α (eM m) : ℂ) • A.representation (eM m) v
  rw [h]

end TwistTransport

section TwistedSections

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U P' M' U' : Subgroup H}
  (d : IsSemidirectDecomposition P M U) (d' : IsSemidirectDecomposition P' M' U')
  (e : H ≃ₜ* H) (hP : ∀ x, x ∈ P' ↔ e x ∈ P) (hM : ∀ x, x ∈ M' ↔ e x ∈ M)
  (hU : ∀ x, x ∈ U' ↔ e x ∈ U)
  (eM : M' ≃ₜ* M) (heM : ∀ m, eM m = GroupTransport.subgroupEquiv e hM m)
  (cU : IsClosed (U : Set H)) (cU' : IsClosed (U' : Set H))
  (A : SmoothRep.{0, u, uV} ℂ M) (α : M →* ℂˣ) (β : M' →* ℂˣ)
  (hα : IsOpen (α.ker : Set M)) (hβ : IsOpen (β.ker : Set M'))
  (hχ : ∀ m, β m = α (eM m))

set_option hygiene false in
local notation "B" => A.twist α hα
set_option hygiene false in
local notation "B'" => (SmoothRep.pullback eM A).twist β hβ
set_option hygiene false in
set_option quotPrecheck false in
local notation "I" => (DynamicNormalization.leviTwistedInductionFunctor d cU).obj B
set_option hygiene false in
set_option quotPrecheck false in
local notation "I'" => (DynamicNormalization.leviTwistedInductionFunctor d' cU').obj B'

private def inducedTwistTransport :
    Representation.Equiv ((I).representation.comp e.toMonoidHom) (I').representation :=
  inducedSectionTransport d d' e hP hM hU eM heM cU cU' B
    (Langlands.twist β (A.representation.comp eM.toMonoidHom))
    (B').isSmooth (twist_comp_of_apply_eq eM A α β hχ)

private theorem restriction_transport (K K' : OpenSubgroup H)
    (eK : K' ≃ₜ* K) (heK : ∀ k : K', (eK k : H) = e (k : H))
    (R : I ≃ₗ[ℂ] CompactInductionPicture d K A) (hR : ∀ f k,
      compactSectionEval d K A (R f) k = leviSectionEval d cU B f (k : H))
    (R' : I' ≃ₗ[ℂ] CompactInductionPicture d' K' (SmoothRep.pullback
      (GroupTransport.subgroupEquiv e hM) A)) (hR' : ∀ f k,
      compactSectionEval d' K' (SmoothRep.pullback (GroupTransport.subgroupEquiv e hM) A)
        (R' f) k = leviSectionEval d' cU' B' f (k : H))
    (E : I ≃ₗ[ℂ] I') (hE : ∀ f x, eval _ _ (E f) x = eval _ _ f (e x))
    (f : I) :
    R' (E f) = compactSectionTransport d d' e hP hM hU K K' eK heK A (R f) := by
  apply compactSectionEval_injective d' K' (SmoothRep.pullback (GroupTransport.subgroupEquiv e hM) A)
  funext k
  exact (hR' (E f) k).trans ((hE f (k : H)).trans
    ((congrArg (leviSectionEval d cU B f) (heK k).symm).trans
      ((hR f (eK k)).symm.trans
        (compactSectionTransport_eval d d' e hP hM hU K K' eK heK A (R f) k).symm)))

end TwistedSections

section QuotientMeasures

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {U V U' V' : Subgroup H}
  (eV : V' ≃ₜ* V) (hbot : U ⊓ V = ⊥) (hbot' : U' ⊓ V' = ⊥)

private abbrev oppositeQuotientChart (h : U ⊓ V = ⊥) : V ≃ₜ QuotientSpace (U := U) V :=
  trivialQuotientChart (U.subgroupOf V) (subgroupOf_eq_one h)

private def oppositeQuotientTransport :
    QuotientSpace (U := U') V' ≃ₜ QuotientSpace (U := U) V :=
  ((oppositeQuotientChart hbot').symm.trans eV.toHomeomorph).trans (oppositeQuotientChart hbot)

private theorem oppositeQuotientTransport_mk (v : V') :
    oppositeQuotientTransport eV hbot hbot' (Quotient.mk _ v) = Quotient.mk _ (eV v) := by
  change (oppositeQuotientChart hbot) (eV ((oppositeQuotientChart hbot').symm
    ((oppositeQuotientChart hbot') v))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

variable [MeasurableSpace V] [BorelSpace V] [MeasurableSpace V'] [BorelSpace V']
  [MeasurableSpace (QuotientSpace (U := U) V)] [BorelSpace (QuotientSpace (U := U) V)]
  [MeasurableSpace (QuotientSpace (U := U') V')] [BorelSpace (QuotientSpace (U := U') V')]

omit [BorelSpace V] [BorelSpace (QuotientSpace (U := U) V)] in
private theorem measurePreserving_oppositeQuotientTransport {mu : Measure V} {mu' : Measure V'}
    {ν : Measure (QuotientSpace (U := U) V)} {ν' : Measure (QuotientSpace (U := U') V')}
    (hV : MeasurePreserving eV mu' mu)
    (hq : MeasurePreserving (oppositeQuotientChart hbot) mu ν)
    (hq' : MeasurePreserving (oppositeQuotientChart hbot') mu' ν') :
    MeasurePreserving (oppositeQuotientTransport eV hbot hbot') ν' ν :=
  hq.comp (hV.comp (hq'.symm (oppositeQuotientChart hbot').toMeasurableEquiv))

end QuotientMeasures

section IntegralTransport

open HarmonicAnalysis.SmoothWeakIntegral in
private theorem weakIntegral_transport_iff {X Y M M' W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Group M] [TopologicalSpace M]
    [Group M'] [TopologicalSpace M'] [AddCommGroup W] [Module ℂ W]
    (eM : M' ≃ₜ* M) (ρ : Representation ℂ M W) (ρ' : Representation ℂ M' W)
    (hρ : ρ' = ρ.comp eM.toMonoidHom) (eq : Y ≃ᵐ X)
    {mu : Measure X} {mu' : Measure Y} (hmu : MeasurePreserving eq mu' mu)
    (f : X → W) (f' : Y → W) (hf : ∀ y, f' y = f (eq y)) (v : W) :
    HarmonicAnalysis.SmoothWeakIntegral.HasIntegral ρ' mu' f' v ↔
      HarmonicAnalysis.SmoothWeakIntegral.HasIntegral ρ mu f v := by
  rw [hρ, hasIntegral_comp_continuousMulEquiv_iff, funext hf]
  exact (hasIntegral_measurePreserving_equiv_iff eq hmu f v).symm

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U V P' M' U' V' : Subgroup H}
  {d : IsSemidirectDecomposition P M U} {d' : IsSemidirectDecomposition P' M' U'}
  {cU : IsClosed (U : Set H)} {cU' : IsClosed (U' : Set H)}
  {A : SmoothRep.{0, u, uV} ℂ M} {α : M →* ℂˣ} {β : M' →* ℂˣ}
  {hα : IsOpen (α.ker : Set M)} {hβ : IsOpen (β.ker : Set M')}
  (e : H ≃ₜ* H) (eM : M' ≃ₜ* M) (hχ : ∀ m, β m = α (eM m))

set_option hygiene false in
local notation "B" => A.twist α hα
set_option hygiene false in
local notation "B'" => (SmoothRep.pullback eM A).twist β hβ
set_option hygiene false in
set_option quotPrecheck false in
local notation "I" => (DynamicNormalization.leviTwistedInductionFunctor d cU).obj B
set_option hygiene false in
set_option quotPrecheck false in
local notation "I'" => (DynamicNormalization.leviTwistedInductionFunctor d' cU').obj B'

variable (eV : V' ≃ₜ* V) (heV : ∀ v : V', (eV v : H) = e (v : H))
  [MeasurableSpace (QuotientSpace (U := U) V)] [BorelSpace (QuotientSpace (U := U) V)]
  [MeasurableSpace (QuotientSpace (U := U') V')] [BorelSpace (QuotientSpace (U := U') V')]
  (hbot : U ⊓ V = ⊥) (hbot' : U' ⊓ V' = ⊥)
  {ν : Measure (QuotientSpace (U := U) V)} {ν' : Measure (QuotientSpace (U := U') V')}
  (hν : MeasurePreserving (oppositeQuotientTransport eV hbot hbot') ν' ν)
  (E : I ≃ₗ[ℂ] I') (hE : ∀ (f : I) x, eval _ _ (E f) x = eval _ _ f (e x))

include hν hχ heV in
private theorem hasIntegral_transport_iff (f : I) (f' : I')
    (hf : ∀ x, eval _ _ f' x = eval _ _ f (e x)) (J : H → B) :
    HasIntegral d' cU' V' B' ν' f' (J ∘ e) ↔ HasIntegral d cU V B ν f J := by
  have hx (x : H) :
      HarmonicAnalysis.SmoothWeakIntegral.HasIntegral (B').representation ν'
        (integrand d' cU' V' B' x f') (J (e x)) ↔
      HarmonicAnalysis.SmoothWeakIntegral.HasIntegral (B).representation ν
        (integrand d cU V B (e x) f) (J (e x)) := by
    apply weakIntegral_transport_iff eM _ _ (twist_comp_of_apply_eq eM A α β hχ)
      (oppositeQuotientTransport eV hbot hbot').toMeasurableEquiv hν
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      change integrand d' cU' V' B' x f' (Quotient.mk _ v) =
        integrand d cU V B (e x) f (oppositeQuotientTransport eV hbot hbot' (Quotient.mk _ v))
      rw [oppositeQuotientTransport_mk, integrand_mk, integrand_mk]
      refine (hf ((v : H) * x)).trans ?_
      rw [map_mul, heV]
      rfl
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact (hx y).mp (h y)
  · intro h x
    exact (hx x).mpr (h (e x))

include hν hχ heV hE in
private theorem hasIntegral_transport_equiv (f : I) (J : H → B)
    (hJ : HasIntegral d cU V B ν f J) : HasIntegral d' cU' V' B' ν' (E f) (J ∘ e) :=
  (hasIntegral_transport_iff e eM hχ eV heV hbot hbot' hν f (E f) (hE f) J).2 hJ

include hν hχ heV hE in
private theorem integralValues_transport
    {Q W Q' W' : Subgroup H}
    (dOut : IsSemidirectDecomposition Q M W) (dOut' : IsSemidirectDecomposition Q' M' W')
    (cW : IsClosed (W : Set H)) (cW' : IsClosed (W' : Set H)) (cM' : IsClosed (M' : Set H))
    (EOut : (DynamicNormalization.leviTwistedInductionFunctor dOut cW).obj B ≃ₗ[ℂ]
      (DynamicNormalization.leviTwistedInductionFunctor dOut' cW').obj B')
    (hEOut : ∀ J x, eval _ _ (EOut J) x = eval _ _ J (e x))
    (f : I) (J : (DynamicNormalization.leviTwistedInductionFunctor dOut cW).obj B)
    (J' : (DynamicNormalization.leviTwistedInductionFunctor dOut' cW').obj B')
    (hJ : HasIntegral d cU V B ν f (leviSectionEval dOut cW B J))
    (hJ' : HasIntegral d' cU' V' B' ν' (E f) (leviSectionEval dOut' cW' B' J')) :
    J' = EOut J := by
  have hTransport := hasIntegral_transport_equiv e eM hχ eV heV hbot hbot' hν E hE f _ hJ
  apply leviSectionEval_injective dOut' cW' B'
  funext x
  exact (HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.unique (compactCofinal cM')
    (B').isSmooth (hJ' x) (hTransport x)).trans (hEOut J x).symm

include hν hχ heV hE in
private theorem domain_eq_top_transport_iff :
    domain d' cU' V' B' ν' = ⊤ ↔ domain d cU V B ν = ⊤ := by
  have h f J := hasIntegral_transport_iff e eM hχ eV heV hbot hbot' hν f (E f) (hE f) J
  constructor
  · intro ht
    apply eq_top_iff.mpr
    intro f _
    obtain ⟨J', hJ'⟩ := (mem_domain d' cU' V' B' ν' (E f)).1 (by rw [ht]; trivial)
    apply (mem_domain d cU V B ν f).2
    refine ⟨J' ∘ e.symm, (h f (J' ∘ e.symm)).mp ?_⟩
    have hcomp : (J' ∘ e.symm) ∘ e = J' :=
      funext fun x => congrArg J' (e.symm_apply_apply x)
    exact (congrArg (HasIntegral d' cU' V' B' ν' (E f)) hcomp).mpr hJ'
  · intro ht
    apply eq_top_iff.mpr
    intro f' _
    obtain ⟨f, rfl⟩ := E.surjective f'
    obtain ⟨J, hJ⟩ := (mem_domain d cU V B ν f).1 (by rw [ht]; trivial)
    exact (mem_domain d' cU' V' B' ν' (E f)).2 ⟨J ∘ e, (h f J).mpr hJ⟩

end IntegralTransport

section DynamicConjugation

open ActualConjugateLeviTwist DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  Langlands.Plancherel.hermitianAdjunctionPointMeasurable
  Langlands.Plancherel.hermitianAdjunctionPointBorel
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace3
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace3
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace4
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace4
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace5
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace5
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace6
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace6

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)

set_option hygiene false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "eg" => (GroupScheme.rationalPointsConjHomeomorph G g).symm
set_option hygiene false in
local notation "Xχ" => unramifiedCharacters (normCharacters χ)

private theorem mem_of_conj_mem {H : Type u} [Group H] [TopologicalSpace H]
    (e : H ≃ₜ* H) {S T : Set H} (h : ∀ x, e x ∈ T ↔ x ∈ S) (y : H) :
    y ∈ T ↔ e.symm y ∈ S := by
  simpa only [e.apply_symm_apply] using h (e.symm y)

private theorem parabolic_mem_inverseConjugation (x : RationalPoint F G.X) :
    x ∈ parabolic χg ↔ (eg) x ∈ parabolic χ :=
  mem_of_conj_mem _ (conjugateParabolic_mem_iff χ g) x

private theorem oppositeParabolic_mem_inverseConjugation (x : RationalPoint F G.X) :
    x ∈ oppositeParabolic χg ↔ (eg) x ∈ oppositeParabolic χ :=
  mem_of_conj_mem _ (conjugateOppositeParabolic_mem_iff χ g) x

private theorem levi_mem_inverseConjugation (x : RationalPoint F G.X) :
    x ∈ levi χg ↔ (eg) x ∈ levi χ :=
  mem_of_conj_mem _ (conjugateLevi_mem_iff χ g) x

private theorem radical_mem_inverseConjugation (x : RationalPoint F G.X) :
    x ∈ radical χg ↔ (eg) x ∈ radical χ :=
  mem_of_conj_mem _ (RationalDynamicSource.radical_conjugation_mem_iff χ g) x

private theorem oppositeRadical_mem_inverseConjugation (x : RationalPoint F G.X) :
    x ∈ oppositeRadical χg ↔ (eg) x ∈ oppositeRadical χ := by
  rw [oppositeRadical, inverseCocharacter_conjugate]
  exact radical_mem_inverseConjugation (Dynamic.inverseCocharacter χ) g x

set_option hygiene false in
local notation "eLevi" => (leviConjugation χ g).symm
set_option hygiene false in
local notation "eRadical" => GroupTransport.subgroupEquiv eg (radical_mem_inverseConjugation χ g)
set_option hygiene false in
local notation "eOppRadical" =>
  GroupTransport.subgroupEquiv eg (oppositeRadical_mem_inverseConjugation χ g)

private abbrev parameterTwist (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : Xχ) :=
  A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : Xχ)

set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "Bz" => parameterTwist χ A z
set_option hygiene false in
local notation "Bzg" => parameterTwist χg Ag (conjugateParameter χ g z)

set_option hygiene false in
local notation "αz" => (parameterTransport χ z).val.toMonoidHom
set_option hygiene false in
local notation "βz" => (parameterTransport χg (conjugateParameter χ g z)).val.toMonoidHom

private def parabolicSectionConjugation :
    Representation.Equiv
      (((DynamicNormalization.leviTwistedInductionFunctor (decomposition χ)
        (radical_isClosed χ)).obj Bz).representation.comp (eg).toMonoidHom)
      ((DynamicNormalization.leviTwistedInductionFunctor (decomposition χg)
        (radical_isClosed χg)).obj Bzg).representation :=
  inducedTwistTransport (decomposition χ) (decomposition χg) eg
    (parabolic_mem_inverseConjugation χ g) (levi_mem_inverseConjugation χ g)
    (radical_mem_inverseConjugation χ g) eLevi (fun _ => rfl)
    (radical_isClosed χ) (radical_isClosed χg)
    A αz βz (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    (conjugateParameter_apply χ g z)

private def oppositeSectionConjugation :
    Representation.Equiv
      (((DynamicNormalization.leviTwistedInductionFunctor (oppositeDecomposition χ)
        (oppositeRadical_isClosed χ)).obj Bz).representation.comp (eg).toMonoidHom)
      ((DynamicNormalization.leviTwistedInductionFunctor (oppositeDecomposition χg)
        (oppositeRadical_isClosed χg)).obj Bzg).representation :=
  inducedTwistTransport (oppositeDecomposition χ) (oppositeDecomposition χg) eg
    (oppositeParabolic_mem_inverseConjugation χ g) (levi_mem_inverseConjugation χ g)
    (oppositeRadical_mem_inverseConjugation χ g) eLevi (fun _ => rfl) (oppositeRadical_isClosed χ)
    (oppositeRadical_isClosed χg) A αz βz
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    (conjugateParameter_apply χ g z)

private theorem inductionIrreducible_conjugation :
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible ↔
    (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
      (leviNormCharacters χg) (parameterTransport χg (conjugateParameter χ g z)) Ag).IsIrreducible :=
  (isIrreducible_comp_continuousMulEquiv_iff _ eg).symm.trans
    (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (parabolicSectionConjugation χ g A z))

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

set_option hygiene false in
local notation "Kg" => RationalDynamicSource.conjugateCompact g K
set_option hygiene false in
local notation "hKg" => RationalDynamicSource.conjugateCompact_isCompact g K hK

private def compactConjugation : Kg ≃ₜ* K := by
  let eK := GroupTransport.subgroupEquiv eg
    (show ∀ x : RationalPoint F G.X, x ∈ Kg ↔ (eg) x ∈ K from fun _ => Iff.rfl)
  exact eK

private def parabolicCompactConjugation :
    CompactInductionPicture (decomposition χ) K A ≃ₗ[ℂ]
      CompactInductionPicture (decomposition χg) Kg Ag :=
  compactSectionTransport (decomposition χ) (decomposition χg) eg
    (parabolic_mem_inverseConjugation χ g) (levi_mem_inverseConjugation χ g)
    (radical_mem_inverseConjugation χ g) K Kg (compactConjugation g K) (fun _ => rfl) A

private def oppositeCompactConjugation :
    CompactInductionPicture (oppositeDecomposition χ) K A ≃ₗ[ℂ]
      CompactInductionPicture (oppositeDecomposition χg) Kg Ag :=
  compactSectionTransport (oppositeDecomposition χ) (oppositeDecomposition χg) eg
    (oppositeParabolic_mem_inverseConjugation χ g) (levi_mem_inverseConjugation χ g)
    (oppositeRadical_mem_inverseConjugation χ g) K Kg (compactConjugation g K) (fun _ => rfl) A

private theorem measurePreserving_radicalTransport
    (V V' : Subgroup (RationalPoint F G.X))
    (cV : IsClosed (V : Set (RationalPoint F G.X)))
    (cV' : IsClosed (V' : Set (RationalPoint F G.X)))
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace V'] [BorelSpace V']
    (hV : ∀ x, x ∈ V' ↔ (eg) x ∈ V) :
    MeasurePreserving (GroupTransport.subgroupEquiv eg hV)
      (subgroupCompactOpenHaar Kg hKg V' cV') (subgroupCompactOpenHaar K hK V cV) := by
  let eV := GroupTransport.subgroupEquiv eg hV
  let source := subgroupCompactOpenHaar Kg hKg V' cV'
  have : (Measure.map eV source).Regular := Measure.Regular.map eV.toHomeomorph
  have : IsHaarMeasure (Measure.map eV source) := eV.isHaarMeasure_map source
  refine ⟨eV.continuous.measurable, ?_⟩
  apply compactOpenHaarAlong_eq_of_mass_one K hK V.subtype cV.isClosedEmbedding_subtypeVal
  have hset : MeasurableSet {v : V | (v : RationalPoint F G.X) ∈ K} :=
    (K.isOpen.preimage continuous_subtype_val).measurableSet
  have he : Measurable (eV : V' → V) := eV.continuous.measurable
  change Measure.map eV source {v : V | (v : RationalPoint F G.X) ∈ K} = 1
  rw [Measure.map_apply he hset]
  exact subgroupCompactOpenHaar_mass Kg hKg V' cV'

private theorem measurePreserving_forwardChart :
    MeasurePreserving (oppositeQuotientChart (radical_inf_oppositeRadical χ))
      (oppositeRadicalHaar χ K hK) (forwardQuotientMeasure χ K hK) := by
  let : LocallyCompactSpace (oppositeRadical χ) := (oppositeRadical_isClosed χ).locallyCompactSpace
  let : SecondCountableTopology (oppositeRadical χ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hm : forwardIntersectionHaar χ K hK Set.univ = 1 :=
    sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ)
  let : IsFiniteMeasure (forwardIntersectionHaar χ K hK) := ⟨by rw [hm]; exact ENNReal.one_lt_top⟩
  exact measurePreserving_trivialQuotientChart _ (subgroupOf_eq_one (radical_inf_oppositeRadical χ))
    ((radical_isClosed χ).preimage continuous_subtype_val) hm
    (forwardQuotientMeasure_isCompatible χ K hK)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem oppositeRadical_inf_radical : oppositeRadical χ ⊓ radical χ = ⊥ :=
  (inf_comm _ _).trans (radical_inf_oppositeRadical χ)

private theorem measurePreserving_reverseChart :
    MeasurePreserving (oppositeQuotientChart (oppositeRadical_inf_radical χ))
      (radicalHaar χ K hK) (reverseQuotientMeasure χ K hK) := by
  let : LocallyCompactSpace (radical χ) := (radical_isClosed χ).locallyCompactSpace
  let : SecondCountableTopology (radical χ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hm : reverseIntersectionHaar χ K hK Set.univ = 1 :=
    sourceIntersectionHaar_univ K hK _ _ _ _ (oppositeRadical_inf_radical χ)
  let : IsFiniteMeasure (reverseIntersectionHaar χ K hK) := ⟨by rw [hm]; exact ENNReal.one_lt_top⟩
  exact measurePreserving_trivialQuotientChart _ (subgroupOf_eq_one (oppositeRadical_inf_radical χ))
    ((oppositeRadical_isClosed χ).preimage continuous_subtype_val) hm
    (reverseQuotientMeasure_isCompatible χ K hK)

private theorem measurePreserving_forwardQuotientTransport :
    MeasurePreserving
      (oppositeQuotientTransport eOppRadical (radical_inf_oppositeRadical χ)
        (radical_inf_oppositeRadical χg))
      (forwardQuotientMeasure χg Kg hKg) (forwardQuotientMeasure χ K hK) :=
  measurePreserving_oppositeQuotientTransport _ _ _
    (measurePreserving_radicalTransport g K hK (oppositeRadical χ) (oppositeRadical χg)
      (oppositeRadical_isClosed χ) (oppositeRadical_isClosed χg)
      (oppositeRadical_mem_inverseConjugation χ g))
    (measurePreserving_forwardChart χ K hK) (measurePreserving_forwardChart χg Kg hKg)

private theorem measurePreserving_reverseQuotientTransport :
    MeasurePreserving
      (oppositeQuotientTransport eRadical (oppositeRadical_inf_radical χ)
        (oppositeRadical_inf_radical χg))
      (reverseQuotientMeasure χg Kg hKg) (reverseQuotientMeasure χ K hK) :=
  measurePreserving_oppositeQuotientTransport _ _ _
    (measurePreserving_radicalTransport g K hK (radical χ) (radical χg)
      (radical_isClosed χ) (radical_isClosed χg) (radical_mem_inverseConjugation χ g))
    (measurePreserving_reverseChart χ K hK) (measurePreserving_reverseChart χg Kg hKg)

private theorem forwardFullDomain_conjugation :
    conjugateParameter χ g z ∈ forwardFullDomainRegion χg Kg hKg Ag ↔
      z ∈ forwardFullDomainRegion χ K hK A :=
  domain_eq_top_transport_iff (d := decomposition χ) (d' := decomposition χg)
    (cU := radical_isClosed χ) (cU' := radical_isClosed χg)
    (A := A) (α := αz) (β := βz) eg eLevi (conjugateParameter_apply χ g z)
    eOppRadical (fun _ => rfl) (radical_inf_oppositeRadical χ) (radical_inf_oppositeRadical χg)
    (measurePreserving_forwardQuotientTransport χ g K hK)
    (parabolicSectionConjugation χ g A z).toLinearEquiv (fun _ _ => rfl)

private theorem reverseFullDomain_conjugation :
    conjugateParameter χ g z ∈ reverseFullDomainRegion χg Kg hKg Ag ↔
      z ∈ reverseFullDomainRegion χ K hK A :=
  domain_eq_top_transport_iff (d := oppositeDecomposition χ) (d' := oppositeDecomposition χg)
    (cU := oppositeRadical_isClosed χ) (cU' := oppositeRadical_isClosed χg)
    (A := A) (α := αz) (β := βz) eg eLevi (conjugateParameter_apply χ g z)
    eRadical (fun _ => rfl) (oppositeRadical_inf_radical χ) (oppositeRadical_inf_radical χg)
    (measurePreserving_reverseQuotientTransport χ g K hK)
    (oppositeSectionConjugation χ g A z).toLinearEquiv (fun _ _ => rfl)

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)

set_option maxHeartbeats 650000 in
private theorem forwardFamily_conjugation (z : forwardFullDomainRegion χ K hK A)
    (f : UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    conditionalForwardFamily χg Kg hKg hRefl hCST hG Ag
        ⟨conjugateParameter χ g z.val, (forwardFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
        (parabolicSectionConjugation χ g A z.val f) =
      oppositeSectionConjugation χ g A z.val
        (conditionalForwardFamily χ K hK hRefl hCST hG A z f) := by
  let z' : forwardFullDomainRegion χg Kg hKg Ag :=
    ⟨conjugateParameter χ g z.val, (forwardFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
  refine integralValues_transport (d := decomposition χ) (d' := decomposition χg)
    (cU := radical_isClosed χ) (cU' := radical_isClosed χg) (A := A)
    (α := (parameterTransport χ z.val).val.toMonoidHom)
    (β := (parameterTransport χg (conjugateParameter χ g z.val)).val.toMonoidHom)
    eg eLevi (conjugateParameter_apply χ g z.val) eOppRadical (fun _ => rfl)
    (radical_inf_oppositeRadical χ) (radical_inf_oppositeRadical χg)
    (measurePreserving_forwardQuotientTransport χ g K hK)
    (parabolicSectionConjugation χ g A z.val).toLinearEquiv ?_
    (oppositeDecomposition χ) (oppositeDecomposition χg)
    (oppositeRadical_isClosed χ) (oppositeRadical_isClosed χg) (levi_isClosed χg)
    (oppositeSectionConjugation χ g A z.val).toLinearEquiv ?_ f
    (conditionalForwardFamily χ K hK hRefl hCST hG A z f)
    (conditionalForwardFamily χg Kg hKg hRefl hCST hG Ag z' (parabolicSectionConjugation χ g A z.val f))
    ?_ ?_
  · intro v x
    rfl
  · intro J x
    rfl
  · exact conditionalForwardFamily_spec χ K hK hRefl hCST hG A z f
  · exact conditionalForwardFamily_spec χg Kg hKg hRefl hCST hG Ag z'
      (parabolicSectionConjugation χ g A z.val f)

set_option maxHeartbeats 650000 in
private theorem reverseFamily_conjugation (z : reverseFullDomainRegion χ K hK A)
    (f : UnramifiedLeviInduction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    conditionalReverseFamily χg Kg hKg hRefl hCST hG Ag
        ⟨conjugateParameter χ g z.val, (reverseFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
        (oppositeSectionConjugation χ g A z.val f) =
      parabolicSectionConjugation χ g A z.val
        (conditionalReverseFamily χ K hK hRefl hCST hG A z f) := by
  let z' : reverseFullDomainRegion χg Kg hKg Ag :=
    ⟨conjugateParameter χ g z.val, (reverseFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
  refine integralValues_transport (d := oppositeDecomposition χ) (d' := oppositeDecomposition χg)
    (cU := oppositeRadical_isClosed χ) (cU' := oppositeRadical_isClosed χg) (A := A)
    (α := (parameterTransport χ z.val).val.toMonoidHom)
    (β := (parameterTransport χg (conjugateParameter χ g z.val)).val.toMonoidHom)
    eg eLevi (conjugateParameter_apply χ g z.val) eRadical (fun _ => rfl)
    (oppositeRadical_inf_radical χ) (oppositeRadical_inf_radical χg)
    (measurePreserving_reverseQuotientTransport χ g K hK)
    (oppositeSectionConjugation χ g A z.val).toLinearEquiv ?_
    (decomposition χ) (decomposition χg)
    (radical_isClosed χ) (radical_isClosed χg) (levi_isClosed χg)
    (parabolicSectionConjugation χ g A z.val).toLinearEquiv ?_ f
    (conditionalReverseFamily χ K hK hRefl hCST hG A z f)
    (conditionalReverseFamily χg Kg hKg hRefl hCST hG Ag z' (oppositeSectionConjugation χ g A z.val f))
    ?_ ?_
  · intro v x
    rfl
  · intro J x
    rfl
  · exact conditionalReverseFamily_spec χ K hK hRefl hCST hG A z f
  · exact conditionalReverseFamily_spec χg Kg hKg hRefl hCST hG Ag z'
      (oppositeSectionConjugation χ g A z.val f)

private abbrev parabolicRestriction
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X)) :=
  unramifiedLeviInductionCompactEquiv (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (parameterTransport χ z) A

private theorem parabolicRestriction_eval
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (f : UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A) (k : K) :
    compactSectionEval (decomposition χ) K A (parabolicRestriction χ A z K hK hG hPK f) k =
      leviSectionEval (decomposition χ) (radical_isClosed χ) Bz f (k : RationalPoint F G.X) :=
  unramifiedLeviInductionCompactEquiv_eval (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (parameterTransport χ z) A f k

set_option maxHeartbeats 600000 in
private theorem parabolicRestriction_conjugation
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (f : UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A) :
    parabolicRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
        (conjugate_parabolic_mul_compact χ g K hPK) (parabolicSectionConjugation χ g A z f) =
      parabolicCompactConjugation χ g A K (parabolicRestriction χ A z K hK hG hPK f) :=
  restriction_transport (decomposition χ) (decomposition χg) eg
    (parabolic_mem_inverseConjugation χ g) (levi_mem_inverseConjugation χ g)
    (radical_mem_inverseConjugation χ g) eLevi
    (radical_isClosed χ) (radical_isClosed χg) A αz βz
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    K Kg (compactConjugation g K) (fun _ => rfl)
    (parabolicRestriction χ A z K hK hG hPK) (parabolicRestriction_eval χ A z K hK hG hPK)
    (parabolicRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
      (conjugate_parabolic_mul_compact χ g K hPK))
    (parabolicRestriction_eval χg Ag (conjugateParameter χ g z) Kg hKg hG
      (conjugate_parabolic_mul_compact χ g K hPK))
    (parabolicSectionConjugation χ g A z).toLinearEquiv (fun _ _ => rfl) f

private theorem parabolicExtension_conjugation
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (v : CompactInductionPicture (decomposition χ) K A) :
    (parabolicRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
        (conjugate_parabolic_mul_compact χ g K hPK)).symm (parabolicCompactConjugation χ g A K v) =
      parabolicSectionConjugation χ g A z ((parabolicRestriction χ A z K hK hG hPK).symm v) := by
  let R := parabolicRestriction χ A z K hK hG hPK
  let R' := parabolicRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
    (conjugate_parabolic_mul_compact χ g K hPK)
  apply R'.symm_apply_eq.mpr
  exact (congrArg (parabolicCompactConjugation χ g A K) (R.apply_symm_apply v).symm).trans
    (parabolicRestriction_conjugation χ g A z K hK hG hPK (R.symm v)).symm

private abbrev oppositeRestriction
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X)) :=
  unramifiedLeviInductionCompactEquiv (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K (oppositeParabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (oppositeProjection_continuous χ) (parameterTransport χ z) A

private theorem oppositeRestriction_eval
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (f : UnramifiedLeviInduction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A) (k : K) :
    compactSectionEval (oppositeDecomposition χ) K A (oppositeRestriction χ A z K hK hG hPK f) k =
      leviSectionEval (oppositeDecomposition χ) (oppositeRadical_isClosed χ) Bz f (k : RationalPoint F G.X) :=
  unramifiedLeviInductionCompactEquiv_eval (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K (oppositeParabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (oppositeProjection_continuous χ) (parameterTransport χ z) A f k

set_option maxHeartbeats 600000 in
private theorem oppositeRestriction_conjugation
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (f : UnramifiedLeviInduction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A) :
    oppositeRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
        (conjugate_oppositeParabolic_mul_compact χ g K hPK) (oppositeSectionConjugation χ g A z f) =
      oppositeCompactConjugation χ g A K (oppositeRestriction χ A z K hK hG hPK f) :=
  restriction_transport (oppositeDecomposition χ) (oppositeDecomposition χg) eg
    (oppositeParabolic_mem_inverseConjugation χ g) (levi_mem_inverseConjugation χ g)
    (oppositeRadical_mem_inverseConjugation χ g) eLevi
    (oppositeRadical_isClosed χ) (oppositeRadical_isClosed χg) A αz βz
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    K Kg (compactConjugation g K) (fun _ => rfl)
    (oppositeRestriction χ A z K hK hG hPK) (oppositeRestriction_eval χ A z K hK hG hPK)
    (oppositeRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
      (conjugate_oppositeParabolic_mul_compact χ g K hPK))
    (oppositeRestriction_eval χg Ag (conjugateParameter χ g z) Kg hKg hG
      (conjugate_oppositeParabolic_mul_compact χ g K hPK))
    (oppositeSectionConjugation χ g A z).toLinearEquiv (fun _ _ => rfl) f

private theorem oppositeExtension_conjugation
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (v : CompactInductionPicture (oppositeDecomposition χ) K A) :
    (oppositeRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
        (conjugate_oppositeParabolic_mul_compact χ g K hPK)).symm (oppositeCompactConjugation χ g A K v) =
      oppositeSectionConjugation χ g A z ((oppositeRestriction χ A z K hK hG hPK).symm v) := by
  let R := oppositeRestriction χ A z K hK hG hPK
  let R' := oppositeRestriction χg Ag (conjugateParameter χ g z) Kg hKg hG
    (conjugate_oppositeParabolic_mul_compact χ g K hPK)
  apply R'.symm_apply_eq.mpr
  exact (congrArg (oppositeCompactConjugation χ g A K) (R.apply_symm_apply v).symm).trans
    (oppositeRestriction_conjugation χ g A z K hK hG hPK (R.symm v)).symm

private theorem forwardCompactFamily_conjugation
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (z : forwardFullDomainRegion χ K hK A)
    (v : CompactInductionPicture (decomposition χ) K A) :
    conditionalForwardCompactFamily χg hRefl hCST hG Kg hKg
        (conjugate_parabolic_mul_compact χ g K hPK)
        (conjugate_oppositeParabolic_mul_compact χ g K hOppK) Ag
        ⟨conjugateParameter χ g z.val, (forwardFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
        (parabolicCompactConjugation χ g A K v) =
      oppositeCompactConjugation χ g A K
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z v) := by
  let z' : forwardFullDomainRegion χg Kg hKg Ag :=
    ⟨conjugateParameter χ g z.val, (forwardFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
  let RIn := parabolicRestriction χ A z.val K hK hG hPK
  let ROut := oppositeRestriction χ A z.val K hK hG hOppK
  let RIn' := parabolicRestriction χg Ag z'.val Kg hKg hG
    (conjugate_parabolic_mul_compact χ g K hPK)
  let ROut' := oppositeRestriction χg Ag z'.val Kg hKg hG
    (conjugate_oppositeParabolic_mul_compact χ g K hOppK)
  let J := conditionalForwardFamily χ K hK hRefl hCST hG A z
  let J' := conditionalForwardFamily χg Kg hKg hRefl hCST hG Ag z'
  change ROut' (J' (RIn'.symm (parabolicCompactConjugation χ g A K v))) =
    oppositeCompactConjugation χ g A K (ROut (J (RIn.symm v)))
  exact (congrArg (fun f => ROut' (J' f))
      (parabolicExtension_conjugation χ g A z.val K hK hG hPK v)).trans
    ((congrArg (fun f => ROut' f)
      (forwardFamily_conjugation χ g A K hK hRefl hCST hG z (RIn.symm v))).trans
      (oppositeRestriction_conjugation χ g A z.val K hK hG hOppK (J (RIn.symm v))))

private theorem reverseCompactFamily_conjugation
    (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (z : reverseFullDomainRegion χ K hK A)
    (v : CompactInductionPicture (oppositeDecomposition χ) K A) :
    conditionalReverseCompactFamily χg hRefl hCST hG Kg hKg
        (conjugate_parabolic_mul_compact χ g K hPK)
        (conjugate_oppositeParabolic_mul_compact χ g K hOppK) Ag
        ⟨conjugateParameter χ g z.val, (reverseFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
        (oppositeCompactConjugation χ g A K v) =
      parabolicCompactConjugation χ g A K
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z v) := by
  let z' : reverseFullDomainRegion χg Kg hKg Ag :=
    ⟨conjugateParameter χ g z.val, (reverseFullDomain_conjugation χ g A z.val K hK).2 z.2⟩
  let RIn := oppositeRestriction χ A z.val K hK hG hOppK
  let ROut := parabolicRestriction χ A z.val K hK hG hPK
  let RIn' := oppositeRestriction χg Ag z'.val Kg hKg hG
    (conjugate_oppositeParabolic_mul_compact χ g K hOppK)
  let ROut' := parabolicRestriction χg Ag z'.val Kg hKg hG
    (conjugate_parabolic_mul_compact χ g K hPK)
  let J := conditionalReverseFamily χ K hK hRefl hCST hG A z
  let J' := conditionalReverseFamily χg Kg hKg hRefl hCST hG Ag z'
  change ROut' (J' (RIn'.symm (oppositeCompactConjugation χ g A K v))) =
    parabolicCompactConjugation χ g A K (ROut (J (RIn.symm v)))
  exact (congrArg (fun f => ROut' (J' f))
      (oppositeExtension_conjugation χ g A z.val K hK hG hOppK v)).trans
    ((congrArg (fun f => ROut' f)
      (reverseFamily_conjugation χ g A K hK hRefl hCST hG z (RIn.symm v))).trans
      (parabolicRestriction_conjugation χ g A z.val K hK hG hPK (J (RIn.symm v))))

/-- The canonical opposite scalar for the conjugate data is the transport of the original scalar
along conjugation of the actual Levi parameter scheme (Waldspurger IV.3 (3)). -/
theorem conditionalDynamicOppositeConjugationScalar :
    ConditionalDynamicOppositeConjugationScalarStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG g K hK hPK hOppK A p q DForward DReverse
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ D hD hne hi
    p' q' DForward' DReverse' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ'
    D' hD' hne' hi'
  exact DynamicOppositeConjugationScalarTransport.conditionalCanonicalRationalScalar_conjugation_of_compact
    χ hRefl hCST hG g K hK hPK hOppK A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'
    (parabolicCompactConjugation χ g A K) (oppositeCompactConjugation χ g A K)
    (fun z => forwardFullDomain_conjugation χ g A z K hK)
    (fun z => reverseFullDomain_conjugation χ g A z K hK)
    (forwardCompactFamily_conjugation χ g A K hK hRefl hCST hG hPK hOppK)
    (reverseCompactFamily_conjugation χ g A K hK hRefl hCST hG hPK hOppK)
    (inductionIrreducible_conjugation χ g A)

end DynamicConjugation

end Langlands.Plancherel

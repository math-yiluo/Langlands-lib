import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylOrbits
import Langlands.Representation.Plancherel.ActualParabolicUnitaryTranslation
import Langlands.Representation.Aubert.General.SupportCategory

/-! # Pointwise transport between intrinsic Weyl-conjugate coefficient fibers -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WeylComparison

section Conjugation

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

private def twistEqOneIso (A : SmoothRep.{0, u, uV} ℂ H) (α : H →* ℂˣ)
    (hα : IsOpen (α.ker : Set H)) (he : α = 1) : A.twist α hα ≅ A := by
  subst α
  exact SmoothRep.twistOneIso hα A

private def conjugationCompAt {M N L : Subgroup H} (s t c : H) (hc : t * s = c)
    (hs : ∀ x : H, x ∈ N ↔ s⁻¹ * x * s ∈ M)
    (ht : ∀ x : H, x ∈ L ↔ t⁻¹ * x * t ∈ N)
    (h : ∀ x : H, x ∈ L ↔ c⁻¹ * x * c ∈ M)
    (A : SmoothRep.{0, u, uV} ℂ M) :
    (conjugationFunctor t ht).obj ((conjugationFunctor s hs).obj A) ≅
      (conjugationFunctor c h).obj A := by
  subst c
  exact conjugationFunctorCompIsoApp s t hs ht A

private def identityRoundTrip {M N : Subgroup H}
    (h : ∀ x : H, x ∈ N ↔ (1 : H)⁻¹ * x * 1 ∈ M)
    (h' : ∀ x : H, x ∈ M ↔ (1 : H)⁻¹ * x * 1 ∈ N)
    (A : SmoothRep.{0, u, uV} ℂ M) :
    (conjugationFunctor 1 h').obj ((conjugationFunctor 1 h).obj A) ≅ A := by
  have hM : ∀ x : H, x ∈ M ↔ (1 : H)⁻¹ * x * 1 ∈ M := by
    intro x
    simp
  exact conjugationCompAt 1 1 1 (one_mul _) h h' hM A ≪≫ conjugationFunctorOneIso hM A

private def changeConjugationPresentation {M N L J : Subgroup H} (g : H)
    (h₀ : ∀ x : H, x ∈ N ↔ (1 : H)⁻¹ * x * 1 ∈ M)
    (h₁ : ∀ x : H, x ∈ L ↔ g⁻¹ * x * g ∈ N)
    (h₂ : ∀ x : H, x ∈ J ↔ (1 : H)⁻¹ * x * 1 ∈ L)
    (h : ∀ x : H, x ∈ J ↔ g⁻¹ * x * g ∈ M)
    (A : SmoothRep.{0, u, uV} ℂ M) :
    (conjugationFunctor 1 h₂).obj
      ((conjugationFunctor g h₁).obj ((conjugationFunctor 1 h₀).obj A)) ≅
      (conjugationFunctor g h).obj A := by
  have h₀₁ : ∀ x : H, x ∈ L ↔ g⁻¹ * x * g ∈ M := by
    intro x
    simpa only [inv_one, one_mul, mul_one] using (h₁ x).trans (h₀ (g⁻¹ * x * g))
  exact (conjugationFunctor 1 h₂).mapIso
      (conjugationCompAt 1 g g (mul_one g) h₀ h₁ h₀₁ A) ≪≫
    conjugationCompAt g 1 g (one_mul g) h₀₁ h₂ h A

end Conjugation

open ActualCommonLeviCoherence
open ActualCommonLeviTensor ActualConjugateLeviV3 ActualParabolicUnitaryTranslation
open ActualCommonLeviV3 (unitaryParameter)
open WeylOrbits

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {p q : SemistandardSpectralIndex i}
  {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p) (r' : CocharacterPresentation hG q)
  (d : CompactData p) (d' : CompactData q)

set_option hygiene false in
local notation "H" => rationalPoints G
set_option hygiene false in
local notation "χ" => r.hom

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Inverse of the literal identity change of Levi presentation. -/
theorem reverseLeviMembership (x : H) :
    x ∈ DynamicOppositeStandardIntertwining.levi χ ↔ (1 : H)⁻¹ * x * 1 ∈ levi p := by
  simpa only [inv_one, one_mul, mul_one] using (CoefficientFiber.leviMembership χ r.levi_eq x).symm

/-- The dynamic inducing object of the given intrinsic representative. -/
abbrev dynamicInducing (A : SmoothRep.{0, u, uV} ℂ (levi p)) :=
  (conjugationFunctor 1 (reverseLeviMembership r)).obj A

private def twistOneIso (A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi χ)) :
    twistObject χ (unitaryParameter χ 1) A ≅ A :=
  twistEqOneIso A _ _ (by rw [map_one, map_one]; rfl)

variable (hP : torusCentralizer i ≤ p.levi)
  (n : CompactLift (p := p) (q := q) hP d.compact)
  (hK : d'.compact = d.compact)

set_option hygiene false in
local notation "nK" => compactPoint hP d.compact n
set_option hygiene false in
local notation "g" => (nK : H)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "hc" => conjugateAnchor_eq hP d.compact n χ r.levi_eq
set_option hygiene false in
local notation "zg" => unitaryConjugateParameter χ g

/-- Source parabolic in the comparison's actual common compact. -/
abbrev sourceParabolic := CoefficientFiber.comparisonParabolic r d χ r.levi_eq

/-- Target parabolic in the very same actual compact. -/
def targetParabolic : ParabolicPresentation χg d.compact where
  cocharacter := r'.hom
  centralizer_eq := r'.levi_eq.trans (hc).symm
  iwasawa := hK ▸ (CoefficientFiber.comparisonParabolic r' d' χg hc).iwasawa

variable (A : SmoothRep.{0, u, uV} ℂ (levi p))

set_option hygiene false in
local notation "B" => dynamicInducing r A
set_option hygiene false in
local notation "Bg" => conjugateRepresentation χ g B
set_option hygiene false in
local notation "sourceTwist" => twistObject χ (unitaryParameter χ 1) B
set_option hygiene false in
local notation "targetTwist" => twistObject χg (unitaryParameter χg (zg 1)) Bg

/-- The source dynamic fiber at the unit character is the intrinsic fiber
of the original actual inducing object. -/
def sourceFiberEquiv :=
  let e := (conjugationFunctor 1 (CoefficientFiber.leviMembership χ r.levi_eq)).mapIso
      (twistOneIso r B) ≪≫
    identityRoundTrip (reverseLeviMembership r) (CoefficientFiber.leviMembership χ r.levi_eq) A
  (CoefficientFiber.fiberEquiv r d χ r.levi_eq sourceTwist).trans
    (productInducedCoefficientTransport (decomposition p) (isClosed_radical p)
      (SmoothRep.equivOfIso e))

private def targetTwist_to_rawConjugate :
    targetTwist ≅ (conjugationFunctor g (DynamicCoefficientConjugation.levi_mem_conjugation χ g)).obj B :=
  (SmoothRep.mkIso (unitaryTwistEquiv χ g B 1)).symm ≪≫
    (SmoothRep.pullbackFunctor (leviConjugation χ g).symm).mapIso (twistOneIso r B) ≪≫
    (eqToIso (DynamicCoefficientConjugation.conjugationFunctor_obj_eq χ g B)).symm

/-- The target dynamic fiber at the conjugate unit character is the intrinsic
fiber of the actual Weyl-conjugate inducing object. -/
def targetFiberEquiv :=
  let h₀ := reverseLeviMembership r
  let h₁ := DynamicCoefficientConjugation.levi_mem_conjugation χ g
  let h₂ := CoefficientFiber.leviMembership χg hc
  let e := (conjugationFunctor 1 h₂).mapIso (targetTwist_to_rawConjugate r d hP n A) ≪≫
    changeConjugationPresentation g h₀ h₁ h₂ (WeylOrbits.conjugationMembership hP d.compact n) A
  (CoefficientFiber.fiberEquiv r' d' χg hc targetTwist).trans
    (productInducedCoefficientTransport (decomposition q) (isClosed_radical q)
      (SmoothRep.equivOfIso e))

/-- Transport a displayed comparison at the unit parameter of this inducing
object to the two intrinsic coefficient representations. -/
def comparisonAtOne
    (T : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ g B d.compact d.compact
      (sourceParabolic r d) (targetParabolic r r' d d' hP n hK)) :=
  (targetFiberEquiv r r' d d' hP n A).toIntertwiningMap.comp
    ((T 1).comp (sourceFiberEquiv r d A).symm.toIntertwiningMap)

end Langlands.HarishChandraSchwartz.RationalSemistandard.WeylComparison

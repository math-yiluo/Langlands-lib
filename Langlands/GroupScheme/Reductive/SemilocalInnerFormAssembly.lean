import Langlands.GroupScheme.Adjoint.RelativeExistenceStatement
import Langlands.GroupScheme.Adjoint.RelativeInnerAction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Reductive.RelativeQuasiSplitInnerFormStatement
import Langlands.GroupScheme.Reductive.SectionedQuasiSplitInnerUniqueness
import Langlands.GroupScheme.Reductive.SemilocalQuasiSplitInnerFormStatement
import Langlands.GroupScheme.RelativeLevi.AdjointTorusWeilPresentation
import Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationStatement

/-! # Semilocal inner forms from four geometric prerequisites -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Construct an actual comparison isomorphism by assembling the four explicitly
supplied geometric statements. -/
def quasiSplitInnerFormsIsoOfGeometricPrerequisites
    (hModel : RelativeQuasiSplitInnerFormExistenceStatement.{u})
    (hQuot : RelativeAdjointQuotientExistenceStatement.{u})
    (hFil : RelativeUnipotentRadicalFiltrationStatement.{u})
    (hWeil : RelativeBorelAdjointTorusWeilPresentationStatement.{u})
    {R : Type u} [CommRing R] [Finite (MaximalSpectrum R)]
    {F Fad H₁ H₂ : GroupScheme (Spec (CommRingCat.of R))}
    (hF : IsReductive F)
    (qF : F ⟶ Fad) (hqF : RelativeRoot.IsFppfQuotient (center F) qF)
    (a : AutomorphicAction Fad F)
    (ha : a.restrict qF = AutomorphicAction.conjugation (𝟙 F))
    (h₁ : IsRelativeQuasiSplit H₁) (he₁ : a.IsEtaleInnerForm H₁)
    (h₂ : IsRelativeQuasiSplit H₂) (he₂ : a.IsEtaleInnerForm H₂) : H₁ ≅ H₂ :=
  Classical.choice (by
    obtain ⟨G, hinner, hqs, B, i, T, tG, hi, hT, htG, hmax, hti⟩ :=
      hModel (Spec (CommRingCat.of R)) F hF Fad qF hqF a ha
    have hG : IsReductive G := hqs.isReductive
    let : Mono i.hom.hom := hi.1.mono
    let hiRep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
    let t : T.toGrp ⟶ B := hiRep.factorHom tG hti
    have htiG : t ≫ i = tG := hiRep.factorHom_comp tG hti
    have htG' : IsClosedSubgroup (t ≫ i) := by rwa [htiG]
    have hmax' : IsFibrewiseMaximalTorus (t ≫ i) := by rwa [htiG]
    obtain ⟨A, q, hA, hq⟩ := hQuot (Spec (CommRingCat.of R)) G hG
    let : IsAffineHom G.X.hom := hG.isAffineHom
    let : IsAffineHom A.X.hom := hA
    let c : AutomorphicAction A G := hq.innerAction
    have hc : c.restrict q = AutomorphicAction.conjugation (𝟙 G) :=
      hq.innerAction_restrict
    let d := hi.adjointBorelExtensionData hG q hq c hc T t hT htG' hmax'
    let w := d.torusWeilPresentation hWeil hG hi hq hT htG' hmax'
    have hK : RelativeUnipotent.HasFiniteVectorBundleSeries d.retraction.radical :=
      hFil (Spec (CommRingCat.of R)) G B d.retraction.radical i
        d.retraction.radicalInclusion hG hi.1 d.retraction.isRelativeUnipotentRadical
    let : Mono d.retraction.radicalInclusion.hom.hom :=
      d.retraction.isRelativeUnipotentRadical.isClosedSubgroup.mono_overHom
    let : IsAffineHom B.X.hom := hi.1.isAffineHom
    let : IsClosedImmersion d.retraction.radicalInclusion.hom.hom.left :=
      d.retraction.isRelativeUnipotentRadical.isClosedSubgroup
    let : IsAffineHom d.retraction.radical.X.hom := by
      rw [← Over.w d.retraction.radicalInclusion.hom.hom]
      infer_instance
    let : IsClosedImmersion d.borel.inclusion.hom.hom.left := d.borel.closed
    let : IsAffineHom d.borel.group.X.hom := by
      rw [← Over.w d.borel.inclusion.hom.hom]
      infer_instance
    let : IsAffine d.borel.group.X.left := isAffine_of_isAffineHom d.borel.group.X.hom
    exact ⟨SectionedQuotientExtension.quasiSplitInnerFormsIsoOfSemilocal
      (C := CommRingCat.of w.algebra)
      d.retraction.radicalInclusion d.retraction.projection t d.centerToTorus
      d.borel.projection d.torus.projection d.retraction.section_eq
      d.retraction.isFppfQuotient d.borel_quotient d.torus_quotient hK w.iso
      q hq c hc i hG hi d.borel.inclusion d.borel.represents
      qF hqF a ha hinner h₁ he₁ h₂ he₂⟩)

/-- The four supplied geometric statements imply exactly the published
semilocal quasi-split inner-form proposition, in every universe. -/
theorem reductiveSemilocalQuasiSplitInnerFormStatement_of_geometricPrerequisites
    (hModel : RelativeQuasiSplitInnerFormExistenceStatement.{u})
    (hQuot : RelativeAdjointQuotientExistenceStatement.{u})
    (hFil : RelativeUnipotentRadicalFiltrationStatement.{u})
    (hWeil : RelativeBorelAdjointTorusWeilPresentationStatement.{u}) :
    ReductiveSemilocalQuasiSplitInnerFormStatement.{u} := by
  intro R _ hR F hF Fad qF hqF a ha
  let : Finite (MaximalSpectrum R) := hR
  constructor
  · obtain ⟨G, hinner, hqs, _⟩ :=
      hModel (Spec (CommRingCat.of R)) F hF Fad qF hqF a ha
    exact ⟨G, hqs, hinner⟩
  · intro H₁ H₂ h₁ he₁ h₂ he₂
    exact ⟨quasiSplitInnerFormsIsoOfGeometricPrerequisites hModel hQuot hFil hWeil
      hF qF hqF a ha h₁ he₁ h₂ he₂⟩

end Langlands.GroupScheme

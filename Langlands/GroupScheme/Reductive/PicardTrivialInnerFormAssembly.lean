import Langlands.GroupScheme.Reductive.SemilocalInnerFormAssembly
import Langlands.GroupScheme.Reductive.PicardTrivialQuasiSplitInnerFormStatement

/-! # Quasi-split inner forms over Picard-trivial bases from the geometric prerequisites -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Construct an actual comparison isomorphism over a ring all of whose finite étale
algebras have trivial Picard group, by assembling the four explicitly supplied geometric
statements. -/
def quasiSplitInnerFormsIsoOfGeometricPrerequisitesOfPicTrivial
    (hModel : RelativeQuasiSplitInnerFormExistenceStatement.{u})
    (hQuot : RelativeAdjointQuotientExistenceStatement.{u})
    (hFil : RelativeUnipotentRadicalFiltrationStatement.{u})
    (hWeil : RelativeBorelAdjointTorusWeilPresentationStatement.{u})
    {R : Type u} [CommRing R]
    (hPic : ∀ (R' : Type u) [CommRing R'] [Algebra R R'], Algebra.Etale R R' →
      Module.Finite R R' → Subsingleton (CommRing.Pic R'))
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
    let : Subsingleton (CommRing.Pic (CommRingCat.of w.algebra)) :=
      hPic w.algebra w.etale inferInstance
    exact ⟨SectionedQuotientExtension.quasiSplitInnerFormsIsoOfPicTrivial
      (C := CommRingCat.of w.algebra)
      d.retraction.radicalInclusion d.retraction.projection t d.centerToTorus
      d.borel.projection d.torus.projection d.retraction.section_eq
      d.retraction.isFppfQuotient d.borel_quotient d.torus_quotient hK w.iso
      q hq c hc i hG hi d.borel.inclusion d.borel.represents
      qF hqF a ha hinner h₁ he₁ h₂ he₂⟩)

/-- The four geometric statements, together with the triviality of Picard groups of finite
étale algebras over rings isomorphic to `ℤ` and over polynomial rings `k[x₁, …, xₙ]` with
`char k = 0`, imply exactly the published Picard-trivial quasi-split inner-form
proposition, in every universe. -/
theorem reductivePicardTrivialQuasiSplitInnerFormStatement_of_prerequisites
    (hModel : RelativeQuasiSplitInnerFormExistenceStatement.{u})
    (hQuot : RelativeAdjointQuotientExistenceStatement.{u})
    (hFil : RelativeUnipotentRadicalFiltrationStatement.{u})
    (hWeil : RelativeBorelAdjointTorusWeilPresentationStatement.{u})
    (hZ : ∀ (R : Type u) [CommRing R], Nonempty (R ≃+* ℤ) →
      ∀ (R' : Type u) [CommRing R'] [Algebra R R'], Algebra.Etale R R' →
        Module.Finite R R' → Subsingleton (CommRing.Pic R'))
    (hAff : ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (A : Type u) [CommRing A]
      [Algebra (MvPolynomial (Fin n) k) A], Algebra.Etale (MvPolynomial (Fin n) k) A →
        Module.Finite (MvPolynomial (Fin n) k) A → Subsingleton (CommRing.Pic A)) :
    ReductivePicardTrivialQuasiSplitInnerFormStatement.{u} := by
  unfold ReductivePicardTrivialQuasiSplitInnerFormStatement
  intro QSInner
  have h1 : ∀ (R : Type u) [CommRing R],
      (∀ (R' : Type u) [CommRing R'] [Algebra R R'], Algebra.Etale R R' →
        Module.Finite R R' → Subsingleton (CommRing.Pic R')) → QSInner R := by
    intro R _ hPic F hF Fad qF hqF a ha
    constructor
    · obtain ⟨G, hinner, hqs, _⟩ :=
        hModel (Spec (CommRingCat.of R)) F hF Fad qF hqF a ha
      exact ⟨G, hqs, hinner⟩
    · intro H₁ H₂ h₁ he₁ h₂ he₂
      exact ⟨quasiSplitInnerFormsIsoOfGeometricPrerequisitesOfPicTrivial hModel hQuot hFil
        hWeil hPic hF qF hqF a ha h₁ he₁ h₂ he₂⟩
  refine ⟨h1, ?_, ?_⟩
  · intro R _ he
    exact h1 R (hZ R he)
  · intro k _ _ n
    exact h1 _ (hAff k n)

end Langlands.GroupScheme

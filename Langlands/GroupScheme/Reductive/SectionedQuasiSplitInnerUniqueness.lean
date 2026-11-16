import Langlands.GroupScheme.RelativeInnerForm
import Langlands.GroupScheme.RelativeLevi.BorelSectionedInnerDescent

/-! # Quasi-split inner-form comparison through one sectioned Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SectionedQuotientExtension

variable {R C : CommRingCat.{u}} [Algebra R C]
    [Module.Finite R C] [Module.Projective R C]
    {K B T Z P D : GroupScheme (Spec R)}
    (i : K ⟶ B) (p : B ⟶ T) (t : T ⟶ B) (z : Z ⟶ T)
    (qB : B ⟶ P) (qT : T ⟶ D)
    (ht : t ≫ p = 𝟙 T)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hB : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (z ≫ t)) qB)
    (hT : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) qT)
    [Mono i.hom.hom] [IsAffine P.X.left] [IsAffineHom K.X.hom]
    (hK : RelativeUnipotent.HasFiniteVectorBundleSeries K)
    (eD : D ≅ WeilGm.groupScheme R C)
    {G Gad H : GroupScheme (Spec R)}
    (qG : G ⟶ Gad) (hqG : RelativeRoot.IsFppfQuotient (center G) qG)
    (c : AutomorphicAction Gad G)
    (hc : c.restrict qG = AutomorphicAction.conjugation (𝟙 G))
    (iG : B ⟶ G) (hG : IsReductive G) (hiG : IsRelativeBorelSubgroup iG)
    (k : P ⟶ Gad)
    (hk : (c.subgroupStabilizer (SubgroupFunctor.range iG)).IsRepresentedBy k)

/-- Choose a target Borel and an inner local family, then descend through the
supplied sectioned source Borel. -/
def quasiSplitEtaleInnerIsoOfPicTrivial [Subsingleton (CommRing.Pic C)]
    (hH : IsRelativeQuasiSplit H) (he : c.IsEtaleInnerForm H) : G ≅ H :=
  Classical.choice (by
    obtain ⟨B', jH, hjH⟩ := hH.exists_isRelativeBorelSubgroup
    obtain ⟨V, hVe, hVs, e, he⟩ := he
    let : Etale V.hom := hVe
    let : Surjective V.hom := hVs
    exact ⟨borelInnerIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD
      qG hqG c hc iG jH hG hH.isReductive hiG hjH k hk e he⟩)

variable {F Fad H₁ H₂ : GroupScheme (Spec R)}
    (qF : F ⟶ Fad) (hqF : RelativeRoot.IsFppfQuotient (center F) qF)
    (a : AutomorphicAction Fad F)
    (ha : a.restrict qF = AutomorphicAction.conjugation (𝟙 F))
    (hanchor : a.IsEtaleInnerForm G)

/-- One sectioned Borel on an inner form of a common source suffices to
compare all quasi-split inner forms of that source. -/
def quasiSplitInnerFormsIsoOfPicTrivial [Subsingleton (CommRing.Pic C)]
    (h₁ : IsRelativeQuasiSplit H₁) (he₁ : a.IsEtaleInnerForm H₁)
    (h₂ : IsRelativeQuasiSplit H₂) (he₂ : a.IsEtaleInnerForm H₂) : H₁ ≅ H₂ := by
  let e₁ := quasiSplitEtaleInnerIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD
    qG hqG c hc iG hG hiG k hk h₁
    (AutomorphicAction.IsEtaleInnerForm.compare a hqF hqG c ha hc hanchor he₁)
  let e₂ := quasiSplitEtaleInnerIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD
    qG hqG c hc iG hG hiG k hk h₂
    (AutomorphicAction.IsEtaleInnerForm.compare a hqF hqG c ha hc hanchor he₂)
  exact e₁.symm.trans e₂

/-- Finite-algebra Picard triviality supplies the sole coefficient-ring
vanishing hypothesis in the common-source comparison. -/
def quasiSplitInnerFormsIsoOfFiniteAlgebrasHaveTrivialPicard
    (hR : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} R)
    (h₁ : IsRelativeQuasiSplit H₁) (he₁ : a.IsEtaleInnerForm H₁)
    (h₂ : IsRelativeQuasiSplit H₂) (he₂ : a.IsEtaleInnerForm H₂) : H₁ ≅ H₂ := by
  let : Subsingleton (CommRing.Pic C) := hR C
  exact quasiSplitInnerFormsIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD
    qG hqG c hc iG hG hiG k hk qF hqF a ha hanchor h₁ he₁ h₂ he₂

/-- Over a semi-local ring, one supplied sectioned Borel anchor yields
an actual isomorphism between any two quasi-split inner forms. -/
def quasiSplitInnerFormsIsoOfSemilocal [Finite (MaximalSpectrum R)]
    (h₁ : IsRelativeQuasiSplit H₁) (he₁ : a.IsEtaleInnerForm H₁)
    (h₂ : IsRelativeQuasiSplit H₂) (he₂ : a.IsEtaleInnerForm H₂) : H₁ ≅ H₂ :=
  quasiSplitInnerFormsIsoOfFiniteAlgebrasHaveTrivialPicard
    i p t z qB qT ht hp hB hT hK eD qG hqG c hc iG hG hiG k hk qF hqF a ha hanchor
    (Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal R) h₁ he₁ h₂ he₂

include ht hp hB hT hK eD hqG hc hG hiG hk hqF ha hanchor in
/-- The supplied anchor also supplies the existential form, so it yields
both clauses of existence and uniqueness over the given semi-local ring. -/
theorem existsUnique_quasiSplitInnerForm_of_sectionedBorel [Finite (MaximalSpectrum R)] :
    (∃ G' : GroupScheme (Spec R), IsRelativeQuasiSplit G' ∧ a.IsEtaleInnerForm G') ∧
      ∀ H₁ H₂ : GroupScheme (Spec R),
        IsRelativeQuasiSplit H₁ → a.IsEtaleInnerForm H₁ →
        IsRelativeQuasiSplit H₂ → a.IsEtaleInnerForm H₂ → Nonempty (H₁ ≅ H₂) := by
  refine ⟨⟨G, ⟨hG, ⟨B, iG, hiG⟩⟩, hanchor⟩, ?_⟩
  intro H₁ H₂ h₁ he₁ h₂ he₂
  exact ⟨quasiSplitInnerFormsIsoOfSemilocal i p t z qB qT ht hp hB hT hK eD
    qG hqG c hc iG hG hiG k hk qF hqF a ha hanchor h₁ he₁ h₂ he₂⟩

end Langlands.GroupScheme.SectionedQuotientExtension

import Langlands.GroupScheme.Rational.TorusNormalizerRigidity
import Langlands.GroupScheme.Rational.RelativeWeylSurjectiveReduction
import Langlands.GroupScheme.Rational.TorusNormalizerStatement
import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement

/-! # Reduction of `N(k)/Z(k) ≅ N(U)/Z(U)` to structural statements

The bijectivity target `RelativeWeylGroupRestrictStatement` follows from five published
structural statements about rational parabolic subgroups: generic cocharacters give minimal
parabolics, minimal parabolics are rationally conjugate, maximal split tori in a minimal
parabolic are rationally conjugate, generic dynamic centralizers are torus centralizers, and
parabolic subgroups are self-normalizing. Injectivity and rigidity come from
`Langlands.GroupScheme.Rational.TorusNormalizerRigidity`; surjectivity from rigidity is
`RelativeWeylSurjective.relativeWeylGroupRestrict_surjective_of_rigid`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The five structural statements used to prove that `N(k)/Z(k) → N(U)/Z(U)` is bijective
for every connected test scheme `U`. -/
def RelativeWeylStructuralInputs : Prop :=
  GenericMinimalParabolicStatement.{u} ∧ MinimalParabolicConjugacyStatement.{u} ∧
    MinimalParabolicSplitTorusConjugacyStatement.{u} ∧ GenericCentralizerStatement.{u} ∧
      ParabolicSelfNormalizerStatement.{u}

/-- **Reduction to structural statements.** The five structural statements imply that
restriction `N(k)/Z(k) → N(U)/Z(U)` is bijective for every maximal split torus of a connected
reductive group over a field and every connected test scheme `U`. -/
theorem relativeWeylGroupRestrictStatement_of_structuralInputs
    (h : RelativeWeylStructuralInputs.{u}) : RelativeWeylGroupRestrictStatement.{u} := by
  obtain ⟨hgen, hconj, htorus, hcent, hself⟩ := h
  intro k _ G hG T i hi U _
  have hsub := hi.isSplitSubtorus
  have : Mono i.hom.hom.left := hsub.2.mono
  exact ⟨relativeWeylGroupRestrict_injective i hsub.1 U,
    RelativeWeylSurjective.relativeWeylGroupRestrict_surjective_of_rigid hgen hconj htorus hcent
      (fun P j hj => hself k G hG P j hj) hG i hi U
      (fun g hg => TorusConjugation.exists_isNormalizingAut_of_connected hsub.1 hg)⟩

end Langlands.GroupScheme

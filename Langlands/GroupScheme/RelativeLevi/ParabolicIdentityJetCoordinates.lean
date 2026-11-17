import Langlands.GroupScheme.IdentityJetAffineGenerators
import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientFamily
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof

/-! # Actual parabolic identity-jet tensor quotients -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open AffineCoordinates Corepresented

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  (hG : IsReductive G) {M : Over (Spec R)}
  {F : ParabolicSubgroup ((baseChange M.hom).obj G)}

namespace ParabolicRepresentative

variable (r : ParabolicRepresentative F)

include hG in
/-- The actual chosen parabolic inclusion is closed over its parameter scheme. -/
theorem identityJet_inclusion_isClosedImmersion :
    IsClosedImmersion r.hom.hom.hom.left :=
  relativeParabolicClosed M.left ((baseChange M.hom).obj G) r.group r.hom
    (hG.baseChange M.hom) r.parabolic

/-- The actual tensor generator map on each affine open of the parabolic's base. -/
def identityJetTensorCoordinates (n : ℕ) (U : M.left.affineOpens) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
    Γ(M.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1))
      →ₗ[Γ(M.left, U)] Γ(IdentityJet.module r.group n, U) := by
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  exact IdentityJet.ambientTensorCoordinates G M.hom r.hom n U

/-- Actual ambient truncated coordinates surject onto the chosen parabolic jet. -/
theorem identityJetTensorCoordinates_surjective (n : ℕ) (U : M.left.affineOpens) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
    Function.Surjective (r.identityJetTensorCoordinates hG n U) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let : IsClosedImmersion r.hom.hom.hom.left :=
    r.identityJet_inclusion_isClosedImmersion hG
  exact IdentityJet.ambientTensorCoordinates_surjective G M.hom r.hom n U

/-- The quotient by the kernel of the actual tensor map is the actual jet section
module. This does not identify that kernel with a Grassmannian point. -/
def identityJetTensorQuotientEquiv (n : ℕ) (U : M.left.affineOpens) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
    ((Γ(M.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1))) ⧸
      LinearMap.ker (r.identityJetTensorCoordinates hG n U)) ≃ₗ[Γ(M.left, U)]
        Γ(IdentityJet.module r.group n, U) := by
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
  exact (r.identityJetTensorCoordinates hG n U).quotKerEquivOfSurjective
    (r.identityJetTensorCoordinates_surjective hG n U)

end ParabolicRepresentative

variable {P : GroupScheme (Spec R)} (i : P ⟶ G)
  (hi : IsRelativeParabolicSubgroup i)
  (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i)

/-- The actual quotient family's jet is the tensor quotient by its actual kernel. -/
def homogeneousQuotientIdentityJetTensorQuotientEquiv
    (n : ℕ) (U : Q.scheme.left.affineOpens) :=
  (parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)).identityJetTensorQuotientEquiv
    hG n U

end Langlands.GroupScheme.ParabolicSubgroupModuli

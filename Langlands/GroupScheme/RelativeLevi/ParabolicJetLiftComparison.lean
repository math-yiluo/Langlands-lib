import Langlands.GroupScheme.IdentityJetFamilyNaturality
import Langlands.GroupScheme.IdentityJetFaithfulBaseChange
import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientFamily
import Langlands.GroupScheme.RelativeLevi.ParabolicRepresentativePullback

/-! # Actual quotient parabolic jet coordinates after lifting to the group -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open TorusSubgroupModuli SubgroupFunctor IdentityJet AffineCoordinates Corepresented

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  (hG : IsReductive G) (i : H ⟶ G) (hi : IsRelativeParabolicSubgroup i)
  (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i)

private theorem baseChange_affine {S T : Scheme.{u}} (K : GroupScheme S)
    [IsAffineHom K.X.hom] (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj K).X.hom := by
  change IsAffineHom (Limits.pullback.snd K.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
attribute [local instance] baseChange_affine

variable {T : Over (Spec R)} (g : T ⟶ G.X)

/-- The original quotient family's actual pullback is the actual conjugated subgroup. -/
def quotientRepresentativeLiftIso :
    (GroupScheme.baseChange (g ≫ Q.projection).left).obj
      (parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)).group ≅
        (GroupScheme.baseChange T.hom).obj H := by
  letI : Smooth Q.projection.left := Q.smooth_projection
  letI : Surjective Q.projection.left := Q.surjective_projection
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  have he : restrict hG (g ≫ Q.projection) (homogeneousQuotientParabolic hG i hi Q) =
      conjugateParabolic hG i hi g :=
    restrict_quotientParabolic_comp hG i hi Q.projection
      (fun U g h hgh => (range i).le_normalizer U ((Q.fibers U g h).mp hgh)) g
  let hr : (range (conjugateFamily i g)).IsRepresentedBy
      (familyHom r.hom (g ≫ Q.projection)) :=
    ⟨(isRelativeParabolicSubgroup_familyHom hG r.hom r.parabolic _).mono,
      congrArg Subtype.val he⟩
  let hc : (range (conjugateFamily i g)).IsRepresentedBy (conjugateFamily i g) :=
    ⟨(isRelativeParabolicSubgroup_conjugateFamily hG i hi g).mono, rfl⟩
  exact hr.isoOfIsRepresentedBy hc

/-- The lift comparison preserves the actual ambient inclusion. -/
@[reassoc]
theorem quotientRepresentativeLiftIso_hom_comp :
    (quotientRepresentativeLiftIso hG i hi Q g).hom ≫ conjugateFamily i g =
      familyHom (parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)).hom
        (g ≫ Q.projection) := by
  unfold quotientRepresentativeLiftIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

private theorem tensorCoordinates_congr {S : Scheme.{u}} (A : GroupScheme (Spec R))
    [IsAffine A.X.left] (b : S ⟶ Spec R) {K : GroupScheme S} [IsAffineHom K.X.hom]
    {h k : K ⟶ (GroupScheme.baseChange b).obj A} (hh : h = k)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    ambientTensorCoordinates A b h n U = ambientTensorCoordinates A b k n U := by
  subst k
  rfl

/-- Actual quotient-family evaluation and actual conjugation have the same jet tensor kernel. -/
theorem quotientRepresentativeLift_tensor_eq_zero_iff (n : ℕ) (U : T.left.affineOpens) :
    let : IsAffineHom G.X.hom := hG.isAffineHom
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let : IsAffineHom H.X.hom := hi.isAffineHom
    let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
    let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
    let := Scheme.TwoAffineOpenCover.algebraOfHom T.hom U
    ∀ z : Γ(T.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)),
      ambientTensorCoordinates G T.hom (familyHom r.hom (g ≫ Q.projection)) n U z = 0 ↔
        ambientTensorCoordinates G T.hom (conjugateFamily i g) n U z = 0 := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom H.X.hom := hi.isAffineHom
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let := Scheme.TwoAffineOpenCover.algebraOfHom T.hom U
  let e := quotientRepresentativeLiftIso hG i hi Q g
  change ∀ z : Γ(T.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)),
    ambientTensorCoordinates G T.hom (familyHom r.hom (g ≫ Q.projection)) n U z = 0 ↔
      ambientTensorCoordinates G T.hom (conjugateFamily i g) n U z = 0
  intro z
  have he := homSections_ambientTensorCoordinates G T.hom (conjugateFamily i g) e.hom n U z
  have hc := tensorCoordinates_congr G T.hom
    (quotientRepresentativeLiftIso_hom_comp hG i hi Q g) n U
  have hx : isoSections e n U (ambientTensorCoordinates G T.hom (conjugateFamily i g) n U z) =
      ambientTensorCoordinates G T.hom (familyHom r.hom (g ≫ Q.projection)) n U z :=
    he.trans (LinearMap.congr_fun hc z)
  rw [← hx]
  exact (isoSections e n U).map_eq_zero_iff

/-- An affine faithfully flat lift detects actual quotient-jet tensor vanishing
through the actual conjugate subgroup tensor map. -/
theorem quotientJet_tensor_eq_zero_iff_lift
    [IsAffineHom (g ≫ Q.projection).left] [Flat (g ≫ Q.projection).left]
    [Surjective (g ≫ Q.projection).left] (n : ℕ) (U : Q.scheme.left.affineOpens) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffineHom H.X.hom := hi.isAffineHom
    let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
    letI : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
    let V : T.left.affineOpens := ⟨(g ≫ Q.projection).left ⁻¹ᵁ U, U.2.preimage _⟩
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
    ∀ z : Γ(Q.scheme.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)),
      ambientTensorCoordinates G Q.scheme.hom r.hom n U z = 0 ↔
        ambientTensorCoordinates G T.hom (conjugateFamily i g) n V
          ((familyCoefficientHom (g ≫ Q.projection) U V le_rfl).toLinearMap.rTensor _ z) = 0 := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom H.X.hom := hi.isAffineHom
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let V : T.left.affineOpens := ⟨(g ≫ Q.projection).left ⁻¹ᵁ U, U.2.preimage _⟩
  let := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
  let := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
  change ∀ z : Γ(Q.scheme.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)),
    ambientTensorCoordinates G Q.scheme.hom r.hom n U z = 0 ↔
      ambientTensorCoordinates G T.hom (conjugateFamily i g) n V
        ((familyCoefficientHom (g ≫ Q.projection) U V le_rfl).toLinearMap.rTensor _ z) = 0
  intro z
  have hn := ambientTensorCoordinates_family_baseChange G r.hom (g ≫ Q.projection)
    n U V le_rfl z
  have hl := quotientRepresentativeLift_tensor_eq_zero_iff hG i hi Q g n V
    ((familyCoefficientHom (g ≫ Q.projection) U V le_rfl).toLinearMap.rTensor _ z)
  have hinj := baseChangeSectionsRingMap_injective r.group (g ≫ Q.projection).left n U
  constructor
  · intro hz
    apply hl.mp
    exact hn.symm.trans (by rw [hz, map_zero])
  · intro hz
    apply hinj
    exact hn.trans ((hl.mpr hz).trans (map_zero _).symm)

end Langlands.GroupScheme.ParabolicSubgroupModuli

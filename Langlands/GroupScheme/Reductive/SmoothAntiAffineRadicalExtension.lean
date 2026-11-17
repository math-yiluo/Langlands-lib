import Langlands.GroupScheme.Reductive.SmoothComponentUnipotentRadical
import Langlands.GroupScheme.Reductive.SmoothQuotientRadicalExtension
import Langlands.GroupScheme.Reductive.SmoothRadicalFieldExtensionStatement
import Langlands.GroupScheme.AntiAffineBaseChange
import Langlands.GroupScheme.AntiAffineQuotientExistenceStatement

/-! # Smooth radical extension from a supplied identity-component affinization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G U : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom]
    {i : U ⟶ G}

/-- A supplied anti-affine quotient of the identity component suffices for
radical preservation in an arbitrary smooth ambient group. -/
theorem IsUnipotentRadical.baseChange_of_isAlgClosed_of_antiAffineQuotient
    (hi : IsUnipotentRadical i)
    (A : AntiAffineQuotient (SmoothFieldComponent.group G)) :
    IsUnipotentRadical
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  have : Smooth A.group.X.hom := A.smooth
  have : ConnectedSpace A.group.X.left := A.connectedSpace
  have : IsAffine A.group.X.left := A.isAffinization.isAffine
  have : IsAffineHom A.group.X.hom := inferInstance
  have : Smooth A.projection.hom.hom.left := A.smooth_projection
  have : Surjective A.projection.hom.hom.left := A.surjective_projection
  have : QuasiCompact A.projection.hom.hom.left := A.quasiCompact_projection
  obtain ⟨V, j, hj⟩ := unipotentRadicalExistence k A.group
  let r := SubgroupPreimage.inclusion A.projection j
  have hr : IsUnipotentRadical r :=
    SmoothUnipotentQuotient.isUnipotentRadical_preimage A.projection
      A.hasSmoothConnectedUnipotentKernel j hj
  have hrK := hr.baseChange_of_isAlgClosed_of_smooth_quotient (K := K)
    A.projection A.hasSmoothConnectedUnipotentKernel
    (A.hasSmoothConnectedUnipotentKernel_baseChange (algebraMap k K))
  exact hi.baseChange_of_smooth_component hr hrK

/-- Actual comparison with any represented radical after the field extension,
using a supplied anti-affine quotient only on the original identity component. -/
def IsUnipotentRadical.antiAffineSmoothRadicalBaseChangeIso
    (hi : IsUnipotentRadical i)
    (A : AntiAffineQuotient (SmoothFieldComponent.group G))
    {V : GroupScheme (Spec (CommRingCat.of K))}
    {j : V ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}
    (hj : IsUnipotentRadical j) :
    (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj U ≅ V :=
  let h := hi.baseChange_of_isAlgClosed_of_antiAffineQuotient A
  h.isClosedSubgroup.sourceIsoOfRangeEq hj.isClosedSubgroup (h.range_eq hj)

/-- The comparison intertwines the actual subgroup inclusions. -/
@[reassoc]
theorem IsUnipotentRadical.antiAffineSmoothRadicalBaseChangeIso_hom_comp
    (hi : IsUnipotentRadical i)
    (A : AntiAffineQuotient (SmoothFieldComponent.group G))
    {V : GroupScheme (Spec (CommRingCat.of K))}
    {j : V ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}
    (hj : IsUnipotentRadical j) :
    (hi.antiAffineSmoothRadicalBaseChangeIso A hj).hom ≫ j =
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i := by
  let h := hi.baseChange_of_isAlgClosed_of_antiAffineQuotient (K := K) A
  exact IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp
    h.isClosedSubgroup hj.isClosedSubgroup (h.range_eq hj)

/-- Anti-affine quotient existence implies the exact unrestricted smooth
algebraically closed radical-extension proposition. -/
theorem smoothAlgebraicallyClosedUnipotentRadicalExtension_of_antiAffineQuotientExistence
    (h : AntiAffineQuotientExistenceStatement.{u}) :
    SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement.{u} := by
  intro k K _ _ _ _ _ G U i hs hi
  let : Smooth G.X.hom := hs
  obtain ⟨A⟩ := h k (SmoothFieldComponent.group G) inferInstance inferInstance
  exact hi.baseChange_of_isAlgClosed_of_antiAffineQuotient A

end Langlands.GroupScheme

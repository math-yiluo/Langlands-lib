import Langlands.GroupScheme.SpecialLinearInnerForm.AdjointPointMatrix
import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Reductive.BasedRootDatumProjection

/-! # Field matrices for the kernel of the full based-root projection -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G A : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

local instance weylActionMatrix_inclusion_closed :
    IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1

/-- A trivial full based projection puts the actual torus action in its Weyl
image. The inverse appears because the geometric root-datum map is
contravariant. -/
theorem characterAut_mem_weylImage_of_basedProjection_eq_one
    (f : G ≅ G) (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (hθ : p.basedRootDatumProjection
      (rootDatumEquivOfTorusCompatibleIso
        p.isConnectedReductive p.isConnectedReductive
        p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
        f t hsq p.isRootDatum p.isRootDatum) = 1) :
    characterAut t ∈ weylImage p.inclusion := by
  let δ := rootDatumEquivOfTorusCompatibleIso
    p.isConnectedReductive p.isConnectedReductive
    p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
    f t hsq p.isRootDatum p.isRootDatum
  have hδ : δ ∈ p.rootDatum.weylGroup :=
    (p.basedRootDatumProjection_eq_one_iff δ).mp hθ
  have hw : δ.weightEquiv ∈ weylImage p.inclusion :=
    p.isRootDatum.abstractWeylImage_le ⟨δ, hδ, rfl⟩
  have he : δ.weightEquiv = (characterAut t)⁻¹ := by
    apply LinearEquiv.ext
    intro χ
    exact rootDatumEquivOfTorusCompatibleIso_weightMap
      p.isConnectedReductive p.isConnectedReductive
      p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
      f t hsq p.isRootDatum p.isRootDatum χ
  rw [he] at hw
  simpa only [inv_inv] using (weylImage p.inclusion).inv_mem hw

open SpecialLinearInnerForm

/-- Choose an adjoint base point realizing a torus-preserving automorphism with
trivial full based projection. -/
def adjointPointOfBasedProjectionIdentity {q : G ⟶ A}
    (hq : IsAdjointQuotient q) (f : G ≅ G) (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (hθ : p.basedRootDatumProjection
      (rootDatumEquivOfTorusCompatibleIso
        p.isConnectedReductive p.isConnectedReductive
        p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
        f t hsq p.isRootDatum p.isRootDatum) = 1) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X := by
  exact Classical.choose (p.exists_adjointPoint_of_weylImage hq f t hsq
    (p.characterAut_mem_weylImage_of_basedProjection_eq_one f t hsq hθ))

theorem adjointPointOfBasedProjectionIdentity_spec {q : G ⟶ A}
    (hq : IsAdjointQuotient q) (f : G ≅ G) (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (hθ : p.basedRootDatumProjection
      (rootDatumEquivOfTorusCompatibleIso
        p.isConnectedReductive p.isConnectedReductive
        p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
        f t hsq p.isRootDatum p.isRootDatum) = 1) :
    hq.innerAction.basePointIso
      (p.adjointPointOfBasedProjectionIdentity hq f t hsq hθ) = f := by
  exact Classical.choose_spec (p.exists_adjointPoint_of_weylImage hq f t hsq
    (p.characterAut_mem_weylImage_of_basedProjection_eq_one f t hsq hθ))

/-- With a supplied special-linear presentation, a torus-preserving automorphism
in the kernel of the full based projection is conjugation by one field matrix
on every test scheme. -/
theorem exists_matrix_of_basedProjection_eq_one
    {n : Type} [Fintype n] [DecidableEq n] {q : G ⟶ A}
    (hq : IsAdjointQuotient q)
    (i : G ≅ SpecialLinear.groupScheme n (CommRingCat.of k))
    (f : G ≅ G) (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (hθ : p.basedRootDatumProjection
      (rootDatumEquivOfTorusCompatibleIso
        p.isConnectedReductive p.isConnectedReductive
        p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
        f t hsq p.isRootDatum p.isRootDatum) = 1) :
    ∃ x : Matrix.GeneralLinearGroup n k,
      ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X),
        (pointMatrix i V (g ≫ f.hom.hom.hom) : Matrix n n Γ(V.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (scalarMap V) x : Matrix n n Γ(V.left, ⊤)) *
            (pointMatrix i V g : Matrix n n Γ(V.left, ⊤)) *
            (Matrix.GeneralLinearGroup.map (scalarMap V) x⁻¹ :
              Matrix n n Γ(V.left, ⊤)) := by
  obtain ⟨x, hx⟩ := exists_matrix_for_adjoint_basePoint hq i
    (p.adjointPointOfBasedProjectionIdentity hq f t hsq hθ)
  rw [p.adjointPointOfBasedProjectionIdentity_spec hq f t hsq hθ] at hx
  exact ⟨x, hx⟩

end Langlands.GroupScheme.SplitPinning

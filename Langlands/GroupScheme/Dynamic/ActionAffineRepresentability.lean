import Langlands.GroupScheme.AutomorphicAction.SemidirectDynamic
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.FixedRepresentabilityStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Closed affine representatives for identity-limit functors of Gm-actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H G : GroupScheme B}

/-- Restriction along the identity homomorphism preserves the actual action. -/
@[simp] theorem restrict_id (a : AutomorphicAction H G) : a.restrict (𝟙 H) = a := by
  cases a
  simp only [restrict, Grp.id_hom_hom, MonoidalCategory.id_whiskerRight, Category.id_comp]

namespace Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]
    (a : AutomorphicAction (Gm (Spec R)).toGrp G)

local instance gm_isAffineHom : IsAffineHom (Gm (Spec R)).X.hom :=
  isSplitTorus_gm.isAffineHom

local instance semidirect_isAffine : IsAffine a.semidirectProduct.X.left :=
  isAffine_of_isAffineHom a.semidirectProduct.X.hom

/-- The ambient dynamic unipotent scheme, used for the original Gm-action. -/
abbrev unipotentScheme : GroupScheme (Spec R) :=
  Dynamic.Affine.unipotentScheme a.semidirectInr

/-- Its inclusion into the original affine group, factored through the normal factor. -/
def unipotentHom : unipotentScheme a ⟶ G :=
  a.semidirectUnipotentLift (𝟙 _) (by
    simpa only [Category.id_comp] using
      Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr)

/-- The factored inclusion agrees with the actual ambient unipotent inclusion. -/
theorem unipotentHom_comp_semidirectInl :
    unipotentHom a ≫ a.semidirectInl = Dynamic.Affine.unipotentHom a.semidirectInr :=
  a.semidirectUnipotentLift_comp (𝟙 _) _

/-- This scheme represents the original action's identity-limit functor on every test. -/
theorem isRepresentedBy_unipotentHom : a.unipotent.IsRepresentedBy (unipotentHom a) := by
  simpa only [restrict_id, unipotentHom] using a.isRepresentedBy_semidirectUnipotentLift (𝟙 _)
    (by simpa only [Category.id_comp] using
      Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr)

/-- The inclusion of the original action's identity-limit subgroup is closed. -/
theorem isClosedSubgroup_unipotentHom : IsClosedSubgroup (unipotentHom a) :=
  a.isClosedSubgroup_semidirectUnipotentLift (𝟙 _) _
    (Dynamic.Affine.isClosedSubgroup_unipotentHom a.semidirectInr)

/-- The constructed identity-limit group is affine over the base. -/
instance unipotentScheme_isAffineHom : IsAffineHom (unipotentScheme a).X.hom := by
  have : IsClosedImmersion (unipotentHom a).hom.hom.left := isClosedSubgroup_unipotentHom a
  rw [← (unipotentHom a).hom.hom.w]
  infer_instance

/-- Every affine Gm-action has a closed representative for its identity-limit functor. -/
theorem unipotent_isClosedRepresentable : a.unipotent.IsClosedRepresentable :=
  ⟨unipotentScheme a, unipotentHom a, isRepresentedBy_unipotentHom a,
    isClosedSubgroup_unipotentHom a⟩

end Affine

namespace Affine

attribute [local instance] gm_isAffineHom semidirect_isAffine

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)

/-- Smoothness of the ambient dynamic representative gives smoothness for any Gm-action. -/
theorem smooth_unipotentScheme : Smooth (unipotentScheme a).X.hom := by
  let : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _
  exact (dynamicSmooth k a.semidirectProduct a.semidirectInr (unipotentScheme a)
    (Dynamic.Affine.unipotentHom a.semidirectInr)).2.2
      (Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr)

/-- Every representative of the original identity-limit functor is smooth. -/
theorem smooth_of_isRepresentedBy_unipotent {U : GroupScheme (Spec (CommRingCat.of k))}
    {j : U ⟶ G} (hj : a.unipotent.IsRepresentedBy j) : Smooth U.X.hom :=
  smooth_of_over_iso
    ((Grp.forget _).mapIso (hj.isoOfIsRepresentedBy (isRepresentedBy_unipotentHom a)))
    (smooth_unipotentScheme a)

/-- The dynamic connectedness statement supplies connectedness of this same representative. -/
theorem connected_unipotentScheme (h : DynamicConnectedStatement.{u}) :
    ConnectedSpace (unipotentScheme a).X.left := by
  let : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _
  exact (h k a.semidirectProduct a.semidirectInr (unipotentScheme a)
    (Dynamic.Affine.unipotentHom a.semidirectInr)).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr)

/-- Conditional connectedness is independent of the chosen representative. -/
theorem connected_of_isRepresentedBy_unipotent (h : DynamicConnectedStatement.{u})
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : a.unipotent.IsRepresentedBy j) : ConnectedSpace U.X.left :=
  connectedSpace_of_over_iso
    ((Grp.forget _).mapIso (hj.isoOfIsRepresentedBy (isRepresentedBy_unipotentHom a)))
    (connected_unipotentScheme a h)

end Affine

end Langlands.GroupScheme.AutomorphicAction

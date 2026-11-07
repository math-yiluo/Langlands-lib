import Langlands.AlgebraicGeometry.AffineSchemePushoutStatement
import Langlands.AlgebraicGeometry.AffineSchemePushoutPresheafed
import Langlands.AlgebraicGeometry.AffineSchemePushoutSectionMaps
import Langlands.AlgebraicGeometry.AffineSchemePushoutTopology
import Langlands.AlgebraicGeometry.AffineSchemePushoutLifting
import Langlands.AlgebraicGeometry.AffineSchemePushoutTransport

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry

namespace AffineSchemePushout

variable {B C D : CommRingCat.{u}} (f : B ⟶ D) (g : C ⟶ D)

/-- The canonical spectrum square is a pushout of presheafed spaces. -/
theorem isPushout_specPresheafedSpace (hf : Function.Surjective f.hom) :
    IsPushout
      (Spec.toPresheafedSpace.map f.op) (Spec.toPresheafedSpace.map g.op)
      (Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)).op)
      (Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)).op) := by
  have wr : CommRingCat.ofHom (f.hom.pullbackFst g.hom) ≫ f =
      CommRingCat.ofHom (f.hom.pullbackSnd g.hom) ≫ g :=
    CommRingCat.hom_ext (RingHom.pullback_comm_sq f.hom g.hom)
  have w :
      Spec.toPresheafedSpace.map f.op ≫
          Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)).op =
        Spec.toPresheafedSpace.map g.op ≫
          Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, wr]
  apply isPushout_presheafedSpace w
  · exact isPushout_comap_pullback f.hom g.hom hf
  · exact isPullback_specPresheaf f g (congrArg PresheafedSpace.Hom.base w).symm

/-- The canonical affine square is a pushout in locally ringed spaces. -/
theorem isPushout_specLocallyRingedSpaceMap_canonical (hf : Function.Surjective f.hom) :
    IsPushout (Spec.locallyRingedSpaceMap f) (Spec.locallyRingedSpaceMap g)
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) :=
  isPushout_specLocallyRingedSpaceMap_of_presheafedSpace
    (isPushout_specPresheafedSpace f g hf)

/-- The affine pushout for an arbitrary supplied ring pullback, in locally ringed spaces. -/
theorem isPushout_specLocallyRingedSpaceMap {A : CommRingCat.{u}}
    {i : A ⟶ B} {j : A ⟶ C} (hf : Function.Surjective f.hom)
    (h : IsPullback i j f g) :
    IsPushout (Spec.locallyRingedSpaceMap f) (Spec.locallyRingedSpaceMap g)
      (Spec.locallyRingedSpaceMap i) (Spec.locallyRingedSpaceMap j) :=
  isPushout_map_of_canonical Spec.toLocallyRingedSpace h
    (isPushout_specLocallyRingedSpaceMap_canonical f g hf)

end AffineSchemePushout

/-- A ring pullback with one surjective map induces a pushout in all schemes. -/
theorem affineSchemePushout : AffineSchemePushoutStatement.{u} := by
  intro A B C D f g i j hf h
  exact AffineSchemePushout.isPushout_specMap_of_canonical h
    (AffineSchemePushout.isPushout_specMap_of_presheafedSpace
      (AffineSchemePushout.isPushout_specPresheafedSpace f g hf))

end Langlands.AlgebraicGeometry

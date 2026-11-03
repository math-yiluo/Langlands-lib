import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # The actual kernel and a representative of its all-test image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace KernelRepresentative

variable {S : Scheme.{u}} {G Q U : GroupScheme S}
    (q : G ⟶ Q) (i : U ⟶ G) [Mono i.hom.hom]
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)

/-- The actual kernel is canonically isomorphic to any monomorphic representative
of its full image on all test schemes. -/
def iso : kernel q ≅ U :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range (kernelι q)) ⟨inferInstance, rfl⟩
    ⟨inferInstance, hk.symm⟩

/-- The kernel comparison preserves the inclusion into the ambient group. -/
@[reassoc]
theorem iso_hom_comp : (iso q i hk).hom ≫ i = kernelι q :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (F := SubgroupFunctor.range (kernelι q)) ⟨inferInstance, rfl⟩
    ⟨inferInstance, hk.symm⟩

/-- The comparison on schemes over the same base. -/
def overIso : (kernel q).X ≅ U.X :=
  (Grp.forget (Over S)).mapIso (iso q i hk)

include i hk

/-- Smoothness transfers from a representative to the actual kernel. -/
theorem smooth [Smooth U.X.hom] : Smooth (kernel q).X.hom := by
  let e := overIso q i hk
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- Affineness transfers from a representative to the actual kernel. -/
theorem isAffineHom [IsAffineHom U.X.hom] : IsAffineHom (kernel q).X.hom := by
  let e := overIso q i hk
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- Geometric connectedness transfers over the unchanged base scheme. -/
theorem geometricallyConnected [GeometricallyConnected U.X.hom] :
    GeometricallyConnected (kernel q).X.hom := by
  let e := overIso q i hk
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have hp : IsPullback e.hom.left (kernel q).X.hom U.X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using e.hom.w⟩
  exact MorphismProperty.of_isPullback hp inferInstance

/-- Connectedness of the actual underlying scheme transfers along the comparison. -/
theorem connectedSpace [ConnectedSpace U.X.left] : ConnectedSpace (kernel q).X.left :=
  (Scheme.homeoOfIso ((Over.forget S).mapIso (overIso q i hk))).connectedSpace_iff.2
    ‹ConnectedSpace U.X.left›

end KernelRepresentative

section Field

variable {k : Type u} [Field k]
    {G Q U : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ Q) (i : U ⟶ G) [Mono i.hom.hom]
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)

include i hk

/-- Coefficient-representation unipotence transfers to the actual kernel. -/
theorem KernelRepresentative.isUnipotent (hU : IsUnipotent U) :
    IsUnipotent (kernel q) :=
  hU.of_iso (KernelRepresentative.iso q i hk)

end Field

namespace IsUnipotentRadical

variable {k : Type u} [Field k]
    {G Q U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : U ⟶ G}

/-- A represented ground-field radical makes the actual kernel geometrically
connected whenever its full all-test image is the kernel image. -/
theorem geometricallyConnected_kernel (hi : IsUnipotentRadical i) (q : G ⟶ Q)
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) :
    GeometricallyConnected (kernel q).X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth U.X.hom := hi.smooth
  have : ConnectedSpace U.X.left := hi.connectedSpace
  have : GeometricallyConnected U.X.hom := U.geometricallyConnected_of_connected
  exact KernelRepresentative.geometricallyConnected q i hk

end IsUnipotentRadical

end Langlands.GroupScheme

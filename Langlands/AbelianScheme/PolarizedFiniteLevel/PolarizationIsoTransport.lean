import Langlands.AlgebraicGeometry.Picard.DualPullbackPolarization
import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.AffineMumfordTransport
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof
import Langlands.AbelianScheme.MultiplicationSign

/-! # Transport of polarizations along isomorphisms of abelian schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The underlying scheme morphism of an isomorphism of abelian schemes is an isomorphism. -/
instance isIso_hom_of_iso {S : Scheme.{u}} {A B : AbelianScheme S} (e : A ≅ B) :
    IsIso (hom e.hom) :=
  ⟨⟨hom e.inv, by rw [← hom_comp, e.hom_inv_id, hom_id],
    by rw [← hom_comp, e.inv_hom_id, hom_id]⟩⟩

/-- Isomorphisms of abelian schemes are isogenies. -/
theorem isIsogeny_of_iso {S : Scheme.{u}} {A B : AbelianScheme S} (e : A ≅ B) :
    IsIsogeny e.hom := by
  let eg : A.toGrp ≅ B.toGrp :=
    { hom := groupHom e.hom
      inv := groupHom e.inv
      hom_inv_id := congrArg (fun f => groupHom f) e.hom_inv_id
      inv_hom_id := congrArg (fun f => groupHom f) e.inv_hom_id }
  have : IsIso eg.hom := eg.isIso_hom
  exact GroupScheme.isIsogeny_of_isIso eg.hom

section Transport

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})

include stability in
/-- The ample Mumford condition after a base change is transported along isomorphisms. -/
theorem hasAmpleMumfordAfterBaseChange_iso {S S' : Scheme.{u}} (b : S' ⟶ S)
    {A B : AbelianScheme S} (e : A ≅ B) (hA : HasDualScheme A) (hB : HasDualScheme B)
    (fB : B.X ⟶ dualScheme B hB)
    (h : HasAmpleMumfordAfterBaseChange preservation square B hB universality b fB) :
    HasAmpleMumfordAfterBaseChange preservation square A hA universality b
      ((groupHom e.hom).hom.hom ≫ fB ≫ dualSchemeMap homPicardZeroPullback e.hom hA hB) := by
  unfold HasAmpleMumfordAfterBaseChange at h ⊢
  rw [dualBaseChangeMap_dualPullback stability universality b e.hom hB hA fB]
  have : IsIso (hom ((baseChange b).map e.hom)) := isIso_hom_of_iso ((baseChange b).mapIso e)
  exact hasAmpleMumfordPresentation_dualPullback ((baseChange b).map e.hom) _ _ _
    preservation square h

include stability in
/-- The field ample Mumford condition is transported along isomorphisms. -/
theorem hasFieldAmpleMumfordPresentation_iso (k : Type u) [Field k]
    {A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))} (e : A ≅ B)
    (hA : HasDualScheme A) (hB : HasDualScheme B) (fB : B.X ⟶ dualScheme B hB)
    (h : HasFieldAmpleMumfordPresentation preservation square universality k B hB fB) :
    HasFieldAmpleMumfordPresentation preservation square universality k A hA
      ((groupHom e.hom).hom.hom ≫ fB ≫ dualSchemeMap homPicardZeroPullback e.hom hA hB) := by
  obtain ⟨K, hK, i, hi⟩ := h
  exact ⟨K, hK, i, hasAmpleMumfordAfterBaseChange_iso preservation square universality
    stability _ e hA hB fB hi⟩

end Transport

end Langlands.AbelianScheme

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The map `A ⟶ WA.dual P` obtained by transporting `lam : B ⟶ WB.dual P` along an
isomorphism `e : A ≅ B`, with the contravariant dual map of `e` on the dual side. -/
def DualWitness.transportMap (P : Prerequisites.{u}) {S : Scheme.{u}} {A B : AbelianScheme S}
    (e : A ≅ B) (WA : DualWitness A) (WB : DualWitness B) (lam : B ⟶ WB.dual P) :
    A ⟶ WA.dual P :=
  e.hom ≫ lam ≫ WA.map P WB e.hom

/-- Polarizations are transported along isomorphisms of abelian schemes: if `lam` is a
polarization of `B` for the witness `WB`, then `e.hom ≫ lam ≫ WA.map P WB e.hom` is a
polarization of `A` for the witness `WA`. -/
theorem DualWitness.isPolarization_iso_transport (P : Prerequisites.{u}) {S : Scheme.{u}}
    {A B : AbelianScheme S} (e : A ≅ B) (WA : DualWitness A) (WB : DualWitness B)
    (lam : B ⟶ WB.dual P) (h : WB.IsPolarization P lam) :
    WA.IsPolarization P (e.hom ≫ lam ≫ WA.map P WB e.hom) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨(isIsogeny_of_iso e).comp (h1.comp (isIsogeny_of_iso (WA.mapIso P WB e))), ?_⟩
  intro K _ _ s
  have heq := dualBaseChangeMap_dualPullback P.stability P.universality s e.hom WB.hasDual
    WA.hasDual (groupHom lam).hom.hom
  refine (congrArg (HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K
    ((baseChange s).obj A) (hasDualScheme_baseChange P.universality s A WA.hasDual)) heq).mpr ?_
  exact hasFieldAmpleMumfordPresentation_iso P.preservation P.square P.universality P.stability
    K ((baseChange s).mapIso e) _ _ _ (h2 K s)

/-- The transported map is a polarization whenever the original one is. -/
theorem DualWitness.isPolarization_transportMap (P : Prerequisites.{u}) {S : Scheme.{u}}
    {A B : AbelianScheme S} (e : A ≅ B) (WA : DualWitness A) (WB : DualWitness B)
    (lam : B ⟶ WB.dual P) (h : WB.IsPolarization P lam) :
    WA.IsPolarization P (DualWitness.transportMap P e WA WB lam) :=
  DualWitness.isPolarization_iso_transport P e WA WB lam h

end Langlands.AbelianScheme.PolarizedFiniteLevel

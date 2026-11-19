import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Langlands.GroupScheme.Torus.FibreSpreadingProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Fpqc reflection of the relative torus property -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorus

/-- The relative torus property is invariant under flat, surjective,
quasi-compact base change. -/
def FpqcLocalityStatement : Prop :=
  ∀ {S S' : Scheme.{u}} (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (G : GroupScheme S),
    IsTorus ((baseChange b).obj G) ↔ IsTorus G

set_option maxHeartbeats 600000 in
/-- Reflect torus geometry down an fpqc morphism and spread out the residue tori. -/
theorem fpqcLocality : FpqcLocalityStatement.{u} := by
  intro S S' b _ _ _ G
  refine ⟨fun h => ?_, fun h => h.baseChange b⟩
  have hcover : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u}) b :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hs := (IsPullback.of_hasPullback G.X.hom b).flip
  have : IsAffineHom G.X.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsAffineHom) hs hcover h.isAffineHom
  have : Smooth G.X.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) hs hcover h.smooth
  have hfib (s : S) : GroupScheme.IsTorus (RelativeIdentityComponent.residueFiber G s) := by
    obtain ⟨t, rfl⟩ := (inferInstance : Surjective b).surj s
    have hT := (h.baseChange (S'.fromSpecResidueField t)).isTorus
    exact @GroupScheme.IsTorus.of_baseChange (S.residueField (b t)) (S'.residueField t)
      inferInstance inferInstance (b.residueFieldMap t).hom.toAlgebra _
      (GroupScheme.IsTorus.of_iso (ExtensionReduction.residueFiberBaseChangeIso b G t) hT)
  have hconn (s : S) :
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left := (hfib s).connectedSpace
  choose U hU hTU using fun s => torusFibreSpreading S G hconn s (hfib s)
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S (fun s => (U s).toScheme)
    (fun s => (U s).ι) (fun s => ⟨s, ⟨s, hU s⟩, rfl⟩)
  exact IsTorus.of_openCover 𝒰 hTU

/-- A relative torus over an fpqc cover is a relative torus on the original base. -/
theorem IsTorus.of_fpqc_baseChange {S S' : Scheme.{u}} {G : GroupScheme S}
    (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (h : IsTorus ((GroupScheme.baseChange b).obj G)) : IsTorus G :=
  (fpqcLocality b G).mp h

end Langlands.GroupScheme.RelativeTorus

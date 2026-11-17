import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Langlands.GroupScheme.Reductive.SuppliedTorusLocalSplitting
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Affine pinned models preserving a supplied maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- An affine pinned model identified with the actual supplied group and
maximal torus, with their inclusion square retained exactly. -/
structure SuppliedTorusAffineChart {S : Scheme.{u}} {T : CommGroupScheme S}
    {G : GroupScheme S} (i : T.toGrp ⟶ G) where
  model : AffinePinnedModel.{u}
  map : model.base ⟶ S
  etale : Etale map
  groupIso : model.group ≅ (GroupScheme.baseChange map).obj G
  torusIso : splitTorus.commGroupScheme model.base model.coordinates ≅
    (CommGroupScheme.baseChange map).obj T
  inclusion_eq : model.inclusion ≫ groupIso.hom =
    CommGroupScheme.groupHom torusIso.hom ≫ (GroupScheme.baseChange map).map i

namespace SuppliedTorusAffineChart

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    (i : T.toGrp ⟶ G)

/-- Each point admits an affine pinned etale model whose coordinate inclusion
is precisely the given maximal torus after the displayed actual isomorphisms. -/
theorem exists_over (hG : IsReductive G) (hT : RelativeTorus.IsTorus T.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus (T := T) i) (s : S) :
    ∃ C : SuppliedTorusAffineChart i, s ∈ Set.range C.map := by
  classical
  let := hG.isAffineHom
  obtain ⟨R, f, hf, hs, I, hI, e, hc, hm, J, P, hP, hl⟩ :=
    exists_etale_affine_splitCoordinates_of_suppliedTorus G hG T i hT hi hmax s
  let : Fintype I := hI
  let H := (GroupScheme.baseChange f).obj G
  have hH : IsReductive H := hG.baseChange f
  let := hH.isAffineHom
  let : Finite J := hP.finite
  let : Fintype J := Fintype.ofFinite J
  let : P.IsReduced := hP.isReduced
  let b : P.Base := Langlands.LinearAlgebra.RootDatumBase.base P
  let M : AffinePinnedModel.{u} :=
    { ring := R
      group := H
      reductive := hH
      coordinates := I
      inclusion := e.hom ≫ (GroupScheme.baseChange f).map i
      closed := hc
      maximal := hm
      rootIndex := J
      rootDatum := P
      fibrewiseRootDatum := hP
      rootLines := hl
      basis := b
      pinning := fun a => (Classical.choice (hl a)).symm }
  refine ⟨⟨M, f, hf, Iso.refl _, CommGroupScheme.isoOfGroupIso e, ?_⟩, hs⟩
  exact Category.comp_id _

end SuppliedTorusAffineChart

end Langlands.GroupScheme

import Langlands.AlgebraicGeometry.EtaleResidueExtensions
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Actual group fibres in a prescribed etale residue extension -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.EtaleResidueExtensionData

open Langlands.GroupScheme

variable {S : Scheme.{u}} {s : S} {K : Type u} [Field K]
  [Algebra (S.residueField s) K] (d : EtaleResidueExtensionData S s K)

/-- The original field-valued point of the base. -/
def extensionPoint (_d : EtaleResidueExtensionData S s K) : Spec (CommRingCat.of K) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫ S.fromSpecResidueField s

/-- The map from the actual new residue field back to the prescribed extension field. -/
def inverseResiduePoint : Spec (d.neighbourhood.residueField d.point) ⟶ Spec (CommRingCat.of K) :=
  Spec.map d.residueIso.inv

/-- The inverse residue comparison recovers the actual new canonical fibre point. -/
theorem inverseResiduePoint_over : d.inverseResiduePoint ≫ d.extensionPoint =
    d.neighbourhood.fromSpecResidueField d.point ≫ d.projection := by
  dsimp only [extensionPoint, inverseResiduePoint]
  rw [← d.residue_over, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
  simp

/-- The actual field-valued pullback of a group agrees with the actual new residue
fibre after transport by the supplied residue-field isomorphism. -/
def groupFibreIso (G : GroupScheme S) :
    (baseChange d.inverseResiduePoint).obj ((baseChange d.extensionPoint).obj G) ≅
      (baseChange (d.neighbourhood.fromSpecResidueField d.point)).obj
        ((baseChange d.projection).obj G) :=
  (baseChangeCompIso d.extensionPoint d.inverseResiduePoint G).symm ≪≫
    eqToIso (congrArg (fun b => (baseChange b).obj G) d.inverseResiduePoint_over) ≪≫
      baseChangeCompIso d.projection (d.neighbourhood.fromSpecResidueField d.point) G

/-- Transport the specified torus inclusion to the actual new residue fibre. -/
def torusFibreInclusion (G : GroupScheme S) (T : GroupScheme (Spec (CommRingCat.of K)))
    (i : T ⟶ (baseChange d.extensionPoint).obj G) :
    (baseChange d.inverseResiduePoint).obj T ⟶
      (baseChange (d.neighbourhood.fromSpecResidueField d.point)).obj
        ((baseChange d.projection).obj G) :=
  (baseChange d.inverseResiduePoint).map i ≫ (d.groupFibreIso G).hom

/-- The transported actual torus remains split. -/
theorem torusFibre_isSplit (T : GroupScheme (Spec (CommRingCat.of K))) (hT : IsSplitTorus T) :
    IsSplitTorus ((baseChange d.inverseResiduePoint).obj T) :=
  hT.baseChange d.inverseResiduePoint

/-- A closed inclusion remains closed in the actual new residue fibre. -/
theorem torusFibreInclusion_isClosed (G : GroupScheme S)
    (T : GroupScheme (Spec (CommRingCat.of K)))
    (i : T ⟶ (baseChange d.extensionPoint).obj G) (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (d.torusFibreInclusion G T i) := by
  let : IsClosedImmersion (((baseChange d.inverseResiduePoint).map i).hom.hom.left) :=
    hi.baseChange d.inverseResiduePoint
  let e := d.groupFibreIso G
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  change IsClosedImmersion
    ((((baseChange d.inverseResiduePoint).map i).hom.hom.left) ≫ e.hom.hom.hom.left)
  infer_instance

end Langlands.AlgebraicGeometry.EtaleResidueExtensionData

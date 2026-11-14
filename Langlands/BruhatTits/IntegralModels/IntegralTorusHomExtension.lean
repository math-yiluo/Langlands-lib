import Langlands.BruhatTits.IntegralModels.IntegralTorus
import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration
import Langlands.GroupScheme.Torus.FieldHomExtension
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AbelianScheme.RelativeHomNeronExtension

/-! # Extending generic torus maps compatibly with actual integral inclusions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G} (A : IntegralTorusData D S i)
  (hA : IsSplitTorus A.torus.toGrp)

/-- The supplied split integral torus, regarded as a model of its prescribed
actual generic torus. -/
def splitTorusModel : IntegralModel R K S.toGrp where
  group := A.torus.toGrp
  affine := hA.isAffineHom
  flat := by
    let : Smooth A.torus.X.hom := hA.smooth
    infer_instance
  finiteType := by
    let : Smooth A.torus.X.hom := hA.smooth
    infer_instance
  genericIso := A.genericIso

/-- The same actual torus inclusion as a generic-compatible model morphism. -/
def splitTorusModelInclusion : (A.splitTorusModel hA).Hom D.neutral i where
  hom := A.inclusion
  generic_comm := A.generic_comm

end IntegralTorusData

namespace IntegralSplitTorusData

variable {N : IntegralModel R K G} (A : IntegralSplitTorusData N i)
  {T : CommGroupScheme (Spec (CommRingCat.of R))}
  (hT : IsSplitTorus T.toGrp)
  (f : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T ⟶ S)

/-- Extend a specified generic map into the prescribed integral split torus. -/
def fieldHomExtension : T ⟶ A.torus :=
  hT.fieldHomExtension (Spec.algebraMap R K) A.isSplit (f ≫ A.genericIso.inv)

/-- Recovery uses the target's supplied generic identification. -/
@[reassoc] theorem fieldHomExtension_generic_comm :
    (CommGroupScheme.baseChange (Spec.algebraMap R K)).map
        (A.fieldHomExtension hT f) ≫ A.genericIso.hom = f := by
  rw [fieldHomExtension, IsSplitTorus.fieldHomExtension_baseChange]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- If an integral ambient map factors through the specified generic torus,
the extended torus map gives the same factorization over the integral base. -/
theorem fieldHomExtension_comp_inclusion (j : T.toGrp ⟶ N.group)
    (hj : (GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫ N.genericIso.hom =
      CommGroupScheme.groupHom f ≫ i) :
    CommGroupScheme.groupHom (A.fieldHomExtension hT f) ≫ A.inclusion = j := by
  let : Smooth T.X.hom := hT.smooth
  have hgeneric :
      (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (CommGroupScheme.groupHom (A.fieldHomExtension hT f) ≫ A.inclusion) =
        (GroupScheme.baseChange (Spec.algebraMap R K)).map j := by
    apply (cancel_mono N.genericIso.hom).mp
    rw [Functor.map_comp, Category.assoc]
    change CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).map
          (A.fieldHomExtension hT f)) ≫ N.genericHom A.inclusion = _
    rw [A.generic_comm, ← Category.assoc, hj]
    exact congrArg (fun g => CommGroupScheme.groupHom g ≫ i)
      (A.fieldHomExtension_generic_comm hT f)
  apply Grp.hom_ext
  apply Langlands.AbelianScheme.genericFibre_map_injective K
  exact congrArg
    (fun (g : (GroupScheme.baseChange (Spec.algebraMap R K)).obj T.toGrp ⟶
      N.genericFibre) => g.hom.hom) hgeneric

end IntegralSplitTorusData
end Langlands.BruhatTits.IntegralModels

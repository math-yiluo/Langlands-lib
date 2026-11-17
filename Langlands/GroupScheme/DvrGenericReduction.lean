import Langlands.GroupScheme.GeometricReductionSubgroup
import Langlands.GroupScheme.GenericSubgroupClosureFactorization

/-! # The flat closure of a smooth reduced generic subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace GenericSubgroupClosure

/-- A surjective generic closed subgroup has surjective closure when the
ambient scheme is flat over the domain. -/
theorem surjective_closureInclusion
    {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Flat G.X.hom]
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (j : H ⟶ (baseChange (Spec.algebraMap R K)).obj G)
    [IsClosedImmersion j.hom.hom.left] [Surjective j.hom.hom.left] :
    Surjective (closureInclusion G j).hom.hom.left := by
  have : IsDominant (genericOver G j).left := by
    rw [genericOver_left]
    infer_instance
  have : IsDominant ((projectionOver G j).left ≫ (inclusionOver G j).left) := by
    rw [← Over.comp_left, projectionOver_fac]
    infer_instance
  have : IsDominant (inclusionOver G j).left :=
    IsDominant.of_comp (projectionOver G j).left (inclusionOver G j).left
  change Surjective (inclusionOver G j).left
  exact surjective_of_isDominant_of_isClosed_range _
    (inclusionOver G j).left.isClosedEmbedding.isClosed_range

end GenericSubgroupClosure

namespace DvrGenericReduction

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Flat G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The actual generic fibre, over the specified fraction field. -/
abbrev genericGroup := (baseChange (Spec.algebraMap R K)).obj G

instance generic_lft : LocallyOfFiniteType (genericGroup (K := K) G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (Spec.algebraMap R K))
  infer_instance

variable [GeometricallyReduced (ReducedSubgroup.redOver (genericGroup (K := K) G)).hom]

/-- The canonical reduced generic subgroup, with its verified group operations. -/
abbrev reducedGeneric := GeometricReductionSubgroup.group (genericGroup (K := K) G)

/-- The actual surjective closed inclusion on the generic fibre. -/
def genericInclusion : reducedGeneric (K := K) G ⟶ genericGroup (K := K) G :=
  GeometricReductionSubgroup.inclusion (genericGroup (K := K) G)

instance genericInclusion_closed : IsClosedImmersion (genericInclusion (K := K) G).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion
    (GeometricReductionSubgroup.inclusion (genericGroup (K := K) G)).hom.hom.left)

instance genericInclusion_surjective : Surjective (genericInclusion (K := K) G).hom.hom.left :=
  inferInstanceAs (Surjective
    (GeometricReductionSubgroup.inclusion (genericGroup (K := K) G)).hom.hom.left)

/-- Close the smooth reduced generic subgroup in the original group. -/
abbrev group : GroupScheme (Spec (CommRingCat.of R)) :=
  GenericSubgroupClosure.closureGroup G (genericInclusion (K := K) G)

/-- The actual finite surjective closed inclusion of the closure group. -/
def map : group (K := K) G ⟶ G :=
  GenericSubgroupClosure.closureInclusion G (genericInclusion (K := K) G)

instance flat : Flat (group (K := K) G).X.hom :=
  inferInstanceAs (Flat (GenericSubgroupClosure.closureOver G (genericInclusion (K := K) G)).hom)

instance locallyOfFiniteType : LocallyOfFiniteType (group (K := K) G).X.hom :=
  inferInstanceAs (LocallyOfFiniteType
    (GenericSubgroupClosure.closureOver G (genericInclusion (K := K) G)).hom)

instance quasiCompact [QuasiCompact G.X.hom] : QuasiCompact (group (K := K) G).X.hom :=
  inferInstanceAs (QuasiCompact
    (GenericSubgroupClosure.closureOver G (genericInclusion (K := K) G)).hom)

instance separated [IsSeparated G.X.hom] : IsSeparated (group (K := K) G).X.hom :=
  inferInstanceAs (IsSeparated
    (GenericSubgroupClosure.closureOver G (genericInclusion (K := K) G)).hom)

instance map_closed : IsClosedImmersion (map (K := K) G).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion
    (GenericSubgroupClosure.closureInclusion G (genericInclusion (K := K) G)).hom.hom.left)

instance map_finite : IsFinite (map (K := K) G).hom.hom.left := by infer_instance

instance map_surjective : Surjective (map (K := K) G).hom.hom.left :=
  GenericSubgroupClosure.surjective_closureInclusion G (genericInclusion (K := K) G)

/-- The generic fibre of the closure is the smooth reduced generic group. -/
def genericIso : reducedGeneric (K := K) G ≅ genericGroup (K := K) (group (K := K) G) :=
  GenericSubgroupClosure.genericToClosureIso G (genericInclusion (K := K) G)

instance smooth_generic : Smooth (genericGroup (K := K) (group (K := K) G)).X.hom := by
  let e := genericIso (K := K) G
  have : IsIso e.inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  rw [← Over.w e.inv.hom.hom]
  infer_instance

instance affine_generic [IsAffineHom (genericGroup (K := K) G).X.hom] :
    IsAffineHom (genericGroup (K := K) (group (K := K) G)).X.hom := by
  let e := genericIso (K := K) G
  have : IsIso e.inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  rw [← Over.w e.inv.hom.hom]
  infer_instance

end DvrGenericReduction
end Langlands.GroupScheme

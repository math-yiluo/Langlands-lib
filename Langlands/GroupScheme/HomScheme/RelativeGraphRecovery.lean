import Langlands.GroupScheme.HomScheme.GraphBaseChange

/-! # Recovery of actual relative homomorphisms from graph families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T : Over S}
variable {K L : GroupScheme M.left}

/-- Reparametrizing the source of a subgroup family commutes with pullback. -/
theorem familyHom_comp (e : L ⟶ K)
    (j : K ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) :
    familyHom (e ≫ j) a = (baseChange a.left).map e ≫ familyHom j a := by
  simp [familyHom, CategoryTheory.Functor.map_comp]

/-- Isomorphic source parametrizations give the same evaluated subgroup. -/
theorem evaluate_iso_comp (e : L ≅ K)
    (j : K ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) :
    evaluate (e.hom ≫ j) a = evaluate j a := by
  rw [evaluate, familyHom_comp]
  exact SubgroupFunctor.range_iso_comp ((baseChange a.left).mapIso e) _

end TorusSubgroupModuli

namespace HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S} {M T : Over S}
variable {K : GroupScheme M.left}

instance (i : RelativeHom H G T) : Mono (relativeGraphHom i).hom.hom := by
  change Mono ((graphHom i).hom.hom ≫
    (baseChangeTensorIso T.hom H G).inv.hom.hom)
  infer_instance

/-- The relative graph inclusion represents its literal range subgroup. -/
theorem relativeGraph_isRepresentedBy (i : RelativeHom H G T) :
    (relativeGraph i).IsRepresentedBy (relativeGraphHom i) :=
  ⟨inferInstance, rfl⟩

/-- Relative homomorphisms are determined by their actual graph subgroups. -/
theorem relativeGraph_injective :
    Function.Injective (relativeGraph (H := H) (G := G) (T := T)) := by
  intro f g h
  have hm : (relativeGraphHom f).hom.hom ∈ (relativeGraph g).carrier
      ((baseChange T.hom).obj H).X := by
    rw [← h]
    change ∃ y, y ≫ (relativeGraphHom f).hom.hom = (relativeGraphHom f).hom.hom
    exact ⟨𝟙 _, by simp⟩
  obtain ⟨y, hy⟩ := hm
  change y ≫ (relativeGraphHom g).hom.hom = (relativeGraphHom f).hom.hom at hy
  have hp := congrArg
    (fun t => t ≫ ((baseChange T.hom).map (fst H G)).hom.hom) hy
  have hyid : y = 𝟙 _ := by
    simpa only [Category.assoc, ← Grp.comp_hom_hom, relativeGraphHom_fst,
      Grp.id_hom_hom, Category.comp_id] using hp
  have hq := congrArg
    (fun t => t ≫ ((baseChange T.hom).map (snd H G)).hom.hom) hy
  apply Grp.hom_ext
  simpa only [hyid, Category.id_comp, ← Grp.comp_hom_hom,
    relativeGraphHom_snd] using hq.symm

/-- Recover a relative homomorphism by inverting the first projection of an
actual subgroup representative in the specified direct pullback product. -/
def homOfRelativeGraphRepresentative
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    [IsIso (j ≫ (baseChange M.hom).map (fst H G))] : RelativeHom H G M :=
  inv (j ≫ (baseChange M.hom).map (fst H G)) ≫
    j ≫ (baseChange M.hom).map (snd H G)

/-- The recovered graph inclusion is the given representative reparametrized
by the inverse of its first projection. -/
theorem relativeGraphHom_homOfRelativeGraphRepresentative
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    [IsIso (j ≫ (baseChange M.hom).map (fst H G))] :
    relativeGraphHom (homOfRelativeGraphRepresentative j) =
      inv (j ≫ (baseChange M.hom).map (fst H G)) ≫ j := by
  apply (cancel_mono (baseChangeTensorIso M.hom H G).hom).mp
  apply hom_ext
  · simp [Category.assoc]
  · simp [homOfRelativeGraphRepresentative, Category.assoc]

/-- The original inclusion factors through the recovered graph by its first
projection. -/
theorem firstProjection_comp_relativeGraphHom
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    [IsIso (j ≫ (baseChange M.hom).map (fst H G))] :
    (j ≫ (baseChange M.hom).map (fst H G)) ≫
        relativeGraphHom (homOfRelativeGraphRepresentative j) = j := by
  rw [relativeGraphHom_homOfRelativeGraphRepresentative]
  simp

/-- Recovery gives equality with the original all-test subgroup functor. -/
theorem relativeGraph_homOfRelativeGraphRepresentative
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    [IsIso (j ≫ (baseChange M.hom).map (fst H G))] :
    relativeGraph (homOfRelativeGraphRepresentative j) = SubgroupFunctor.range j := by
  rw [relativeGraph, relativeGraphHom_homOfRelativeGraphRepresentative]
  exact SubgroupFunctor.range_iso_comp
    (asIso (j ≫ (baseChange M.hom).map (fst H G))).symm j

/-- A monic representative of a relative graph has invertible first projection.
This uses equality on all test schemes, not only on field-valued points. -/
theorem isIso_firstProjection_of_range_eq_relativeGraph
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) [Mono j.hom.hom]
    (i : RelativeHom H G M) (h : SubgroupFunctor.range j = relativeGraph i) :
    IsIso (j ≫ (baseChange M.hom).map (fst H G)) := by
  let hj : (relativeGraph i).IsRepresentedBy j := ⟨inferInstance, h⟩
  let e := hj.isoOfIsRepresentedBy (relativeGraph_isRepresentedBy i)
  have he : e.hom ≫ relativeGraphHom i = j :=
    hj.isoOfIsRepresentedBy_hom_comp (relativeGraph_isRepresentedBy i)
  rw [← he, Category.assoc, relativeGraphHom_fst, Category.comp_id]
  infer_instance

/-- The first projection of an evaluated subgroup family is the pullback of
the original first projection followed by the source comparison. -/
theorem familyHom_fst
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) (a : T ⟶ M) :
    TorusSubgroupModuli.familyHom j a ≫ (baseChange T.hom).map (fst H G) =
      (baseChange a.left).map (j ≫ (baseChange M.hom).map (fst H G)) ≫
        (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) H).hom := by
  rw [TorusSubgroupModuli.familyHom, Category.assoc,
    ← Descent.pullbackComparison_naturality, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp]

/-- An invertible first projection remains invertible after evaluation. -/
theorem isIso_familyHom_fst
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    [IsIso (j ≫ (baseChange M.hom).map (fst H G))] (a : T ⟶ M) :
    IsIso (TorusSubgroupModuli.familyHom j a ≫
      (baseChange T.hom).map (fst H G)) := by
  rw [familyHom_fst]
  infer_instance

/-- Pullback of a graph representative gives exactly the graph subgroup of
the evaluated recovered homomorphism. -/
theorem evaluate_eq_relativeGraph_evaluate_homOfRepresentative
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    [IsIso (j ≫ (baseChange M.hom).map (fst H G))] (a : T ⟶ M) :
    TorusSubgroupModuli.evaluate j a =
      relativeGraph (evaluate a (homOfRelativeGraphRepresentative j)) := by
  calc
    TorusSubgroupModuli.evaluate j a =
        TorusSubgroupModuli.evaluate
          ((asIso (j ≫ (baseChange M.hom).map (fst H G))).hom ≫
            relativeGraphHom (homOfRelativeGraphRepresentative j)) a :=
      congrArg (fun k => TorusSubgroupModuli.evaluate k a)
        (firstProjection_comp_relativeGraphHom j).symm
    _ = TorusSubgroupModuli.evaluate
        (relativeGraphHom (homOfRelativeGraphRepresentative j)) a :=
      TorusSubgroupModuli.evaluate_iso_comp _ _ a
    _ = _ := evaluate_relativeGraphHom _ a

end HomScheme
end Langlands.GroupScheme

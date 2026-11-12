import Langlands.Representation.Jacquet.FixedVectorHeckeEquivalence
import Langlands.Representation.Category.RenardNoetherian
import Langlands.CategoryTheory.Renard.NoetherianReflection

/-! # Left Noetherianity of the Hecke algebra from the smooth category -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Langlands.Shimura.LevelHecke

universe uG uV

namespace Langlands.Jacquet

private theorem noetherianObject_of_iso {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (hB : Langlands.Renard.IsNoetherianObject B) :
    Langlands.Renard.IsNoetherianObject A := by
  let q := Subobject.mapIsoToOrderIso e
  intro S hS
  obtain ⟨_, ⟨P, hP, rfl⟩, hmax⟩ := hB (q '' S) (hS.image q)
  refine ⟨P, hP, ?_⟩
  intro Q hQ hPQ
  exact q.injective (hmax (q Q) ⟨Q, hQ, rfl⟩ (q.monotone hPQ))

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : OpenSubgroup G) [Small.{uV} (G ⧸ K.toSubgroup)]

/-- The fixed vectors of compact induction form the left regular module over
exactly the published counting-measure Hecke algebra. -/
def fixedVectorHeckeRegularEquiv : LevelHeckeAlgebra ℂ K.toSubgroup ≃ₗ[
    LevelHeckeAlgebra ℂ K.toSubgroup]
    fixedVectors (smallFixedVectorGenerator.{uG,uV} K).representation K.toSubgroup :=
  { fixedVectorHeckeAddEquiv K with
    map_smul' := by
      intro a b
      exact fixedVectorsMap_heckeAct (smallFixedVectorGeneratorEquiv K).toIntertwiningMap
        K.toSubgroup K.toSubgroup a b }

/-- Noetherianity of the ambient smooth category and subobject closure of
fixed-vector generation imply left Noetherianity of the level Hecke algebra. -/
theorem levelHecke_isNoetherianRing_of_smoothCategory
    (hK : IsCompact (K : Set G))
    [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects]
    (hcat : Langlands.Renard.IsNoetherianCategory (SmoothRep.{0,uG,uV} ℂ G)) :
    IsNoetherianRing (LevelHeckeAlgebra ℂ K.toSubgroup) := by
  let P := fixedVectorProgenerator.{uG,uV} K
  let F := (fixedVectorGenerated.{uG,uV} K.toSubgroup).ι ⋙
    heckeModuleFunctor ℂ K.toSubgroup
  have : F.IsEquivalence := fixedVectorHecke_isEquivalence K hK
  let E := F.asEquivalence
  let I := (fixedVectorGenerated.{uG,uV} K.toSubgroup).ι
  have : I.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _
  have hP : Langlands.Renard.IsNoetherianObject P.obj :=
    hcat.2 P.obj ((SmoothRep.renardFiniteType_iff P.obj).mpr
      (smallFixedVectorGenerator_finite K))
  have hEP : Langlands.Renard.IsNoetherianObject ((E.inverse ⋙ I).obj (F.obj P)) :=
    noetherianObject_of_iso (I.mapIso (E.unitIso.app P).symm) hP
  have hFP : Langlands.Renard.IsNoetherianObject (F.obj P) :=
    Langlands.Renard.noetherianObject_of_functor (E.inverse ⋙ I) (F.obj P) hEP
  have hN : IsNoetherian (LevelHeckeAlgebra ℂ K.toSubgroup)
      (fixedVectors (smallFixedVectorGenerator.{uG,uV} K).representation K.toSubgroup) :=
    (Langlands.Renard.ModuleNoetherian.object_iff _ (F.obj P)).mp hFP
  let _ := hN
  exact isNoetherian_of_linearEquiv (fixedVectorHeckeRegularEquiv K).symm

end Langlands.Jacquet

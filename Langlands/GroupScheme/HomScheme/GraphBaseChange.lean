import Langlands.GroupScheme.HomScheme.Graph
import Langlands.GroupScheme.HomScheme.Universal
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.Torus.Products

/-! # Actual relative graphs and their base-change compatibility -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (H G : GroupScheme S)

@[reassoc (attr := simp)]
theorem baseChangeTensorIso_hom_fst :
    (baseChangeTensorIso b H G).hom ≫
        fst ((baseChange b).obj H) ((baseChange b).obj G) =
      (baseChange b).map (fst H G) := by
  exact Functor.OplaxMonoidal.δ_fst (baseChange b) H G

@[reassoc (attr := simp)]
theorem baseChangeTensorIso_hom_snd :
    (baseChangeTensorIso b H G).hom ≫
        snd ((baseChange b).obj H) ((baseChange b).obj G) =
      (baseChange b).map (snd H G) := by
  exact Functor.OplaxMonoidal.δ_snd (baseChange b) H G

@[reassoc (attr := simp)]
theorem baseChangeTensorIso_inv_map_fst :
    (baseChangeTensorIso b H G).inv ≫ (baseChange b).map (fst H G) =
      fst ((baseChange b).obj H) ((baseChange b).obj G) := by
  exact Functor.Monoidal.μ_fst (baseChange b) H G

@[reassoc (attr := simp)]
theorem baseChangeTensorIso_inv_map_snd :
    (baseChangeTensorIso b H G).inv ≫ (baseChange b).map (snd H G) =
      snd ((baseChange b).obj H) ((baseChange b).obj G) := by
  exact Functor.Monoidal.μ_snd (baseChange b) H G

namespace HomScheme

variable {H G}

/-- The actual product comparison carries a pulled-back graph to the graph of
the pulled-back homomorphism. -/
theorem baseChange_graphHom (f : H ⟶ G) :
    (baseChange b).map (graphHom f) ≫ (baseChangeTensorIso b H G).hom =
      graphHom ((baseChange b).map f) := by
  apply hom_ext <;> simp [← Functor.map_comp]

variable {M T : Over S}

/-- The graph of a relative homomorphism, placed in the specified direct
pullback of the original product group scheme. -/
def relativeGraphHom (i : RelativeHom H G T) :
    (baseChange T.hom).obj H ⟶ (baseChange T.hom).obj (H ⊗ G) :=
  graphHom i ≫ (baseChangeTensorIso T.hom H G).inv

@[reassoc (attr := simp)]
theorem relativeGraphHom_fst (i : RelativeHom H G T) :
    relativeGraphHom i ≫ (baseChange T.hom).map (fst H G) = 𝟙 _ := by
  simp [relativeGraphHom]

@[reassoc (attr := simp)]
theorem relativeGraphHom_snd (i : RelativeHom H G T) :
    relativeGraphHom i ≫ (baseChange T.hom).map (snd H G) = i := by
  simp [relativeGraphHom]

/-- A relative graph is closed when the original target is separated. -/
theorem isClosedSubgroup_relativeGraphHom [IsSeparated G.X.hom]
    (i : RelativeHom H G T) : IsClosedSubgroup (relativeGraphHom i) := by
  let : IsSeparated ((baseChange T.hom).obj G).X.hom := by
    change IsSeparated (pullback.snd G.X.hom T.hom)
    infer_instance
  let : IsClosedImmersion (graphHom i).hom.hom.left := isClosedImmersion_graphHom i
  change IsClosedImmersion
    ((graphHom i).hom.hom.left ≫ (baseChangeTensorIso T.hom H G).inv.hom.hom.left)
  infer_instance

/-- The graph as a subgroup functor in the specified direct pullback ambient
group. -/
def relativeGraph (i : RelativeHom H G T) :
    SubgroupFunctor ((baseChange T.hom).obj (H ⊗ G)) :=
  SubgroupFunctor.range (relativeGraphHom i)

/-- Graphs with split-torus source are admissible for actual torus-subgroup
moduli. -/
theorem isAdmissible_relativeGraph [IsSeparated G.X.hom]
    (hH : IsSplitTorus H) (i : RelativeHom H G T) :
    TorusSubgroupModuli.IsAdmissible (relativeGraph i) :=
  TorusSubgroupModuli.isAdmissible_range _ (isClosedSubgroup_relativeGraphHom i)
    (RelativeTorus.IsTorus.of_isSplitTorus (hH.baseChange T.hom))

/-- The actual graph inclusion commutes with evaluation, with its source and
ambient pullback comparisons both explicit. -/
theorem familyHom_relativeGraphHom (i : RelativeHom H G M) (a : T ⟶ M) :
    TorusSubgroupModuli.familyHom (relativeGraphHom i) a =
      (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) H).hom ≫
        relativeGraphHom (evaluate a i) := by
  apply (cancel_mono (baseChangeTensorIso T.hom H G).hom).mp
  apply hom_ext
  · simp only [Category.assoc, baseChangeTensorIso_hom_fst]
    rw [TorusSubgroupModuli.familyHom, Category.assoc,
      ← Descent.pullbackComparison_naturality, ← Category.assoc,
      ← Functor.map_comp, relativeGraphHom_fst, CategoryTheory.Functor.map_id, Category.id_comp,
      relativeGraphHom_fst, Category.comp_id]
  · simp only [Category.assoc, baseChangeTensorIso_hom_snd]
    rw [TorusSubgroupModuli.familyHom, Category.assoc,
      ← Descent.pullbackComparison_naturality, ← Category.assoc,
      ← Functor.map_comp, relativeGraphHom_snd, relativeGraphHom_snd]
    simp [evaluate, Descent.pullHom]

/-- Pulling back the actual graph family gives literally the graph subgroup
functor of the evaluated homomorphism on every test scheme. -/
theorem evaluate_relativeGraphHom (i : RelativeHom H G M) (a : T ⟶ M) :
    TorusSubgroupModuli.evaluate (relativeGraphHom i) a =
      relativeGraph (evaluate a i) := by
  rw [TorusSubgroupModuli.evaluate, familyHom_relativeGraphHom]
  exact SubgroupFunctor.range_iso_comp
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) H) _

end HomScheme
end Langlands.GroupScheme

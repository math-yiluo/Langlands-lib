import Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
import Langlands.GroupScheme.Descent.DisjointGroupAssembly
import Langlands.GroupScheme.Descent.PullHomCoherence

/-! # Actual term and vector-layer groups over the finite affine cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.DisjointGroupAssembly

variable {I : Type u} [Finite I] {S : Scheme.{u}} {Z : I → Scheme.{u}}
  (p : ∀ i, Z i ⟶ S) [IsIso (Sigma.desc p)]
  (A B : ∀ i, GroupScheme (Z i)) (f : ∀ i, A i ⟶ B i)

/-- Assemble actual component homomorphisms between the assembled groups. -/
def homOfFamily : group p A ⟶ group p B :=
  DisjointComponents.groupHom p (fun i =>
    (componentIso p A i).hom ≫ f i ≫ (componentIso p B i).inv)

/-- The assembled map recovers each prescribed actual component map. -/
theorem homOfFamily_component (i : I) :
    (baseChange (p i)).map (homOfFamily p A B f) ≫ (componentIso p B i).hom =
      (componentIso p A i).hom ≫ f i := by
  rw [homOfFamily, DisjointComponents.map_groupHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Langlands.GroupScheme.Descent.DisjointGroupAssembly

namespace Langlands.GroupScheme.RelativeLevi

open LocalSplitCell

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom] {p : H ⟶ G}

local instance {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace AffineParabolicFaceChart

variable {s : S} (C : AffineParabolicFaceChart p s)

local instance : Fintype C.coordinateType := C.coordinateFintype
local instance : Fintype C.rootType := C.rootFintype
local instance chartAmbientAffine : IsAffine ((baseChange C.projection).obj G).X.left :=
  isAffine_of_isAffineHom ((baseChange C.projection).obj G).X.hom

/-- The actual original weighted term on this chart. -/
abbrev termGroup (d : ℕ) : GroupScheme (Spec C.ring) := C.chart.weights.groupScheme d

/-- The actual vector group for the exact face-weight layer on this chart. -/
abbrev layerGroup (d : ℕ) : GroupScheme (Spec C.ring) :=
  VectorGroup.groupScheme (CommRingCat.of C.ring) (Nat.card (C.chart.weights.exactSupport d))

/-- The original ambient inclusion on this chart. -/
def termInclusion (d : ℕ) : C.termGroup d ⟶ (baseChange C.projection).obj G :=
  C.chart.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter C.torus C.chart.cocharacter)

/-- The original inclusion of consecutive chart terms. -/
def termStep (d : ℕ) : C.termGroup (d + 1) ⟶ C.termGroup d := C.chart.weights.step d

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
/-- The original full fppf chart quotient map. -/
def layerProjection (d : ℕ) : C.termGroup d ⟶ C.layerGroup d := C.chart.weights.quotientMap d
end

/-- Consecutive chart inclusions retain the original ambient maps. -/
theorem termStep_comp_inclusion (d : ℕ) :
    C.termStep d ≫ C.termInclusion d = C.termInclusion (d + 1) := by
  change (C.chart.weights.step d) ≫ (C.chart.weights.inclusion d ≫ _) = _
  rw [← Category.assoc, C.chart.weights.step_comp_inclusion]
  rfl

instance affine_termGroup (d : ℕ) : IsAffine (C.termGroup d).X.left := by
  have : IsAffineHom (C.termGroup d).X.hom := C.chart.weights.isAffineHom_groupScheme d
  exact isAffine_of_isAffineHom (C.termGroup d).X.hom

instance affine_layerGroup (d : ℕ) : IsAffine (C.layerGroup d).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial
    (Fin (Nat.card (C.chart.weights.exactSupport d))) C.ring)))
  infer_instance

end AffineParabolicFaceChart

namespace FiniteParabolicFaceCover

open Descent DisjointGroupAssembly

variable (D : FiniteParabolicFaceCover p)

/-- Component indices in the universe of the base schemes. -/
abbrev Index : Type u := ULift.{u} (Fin D.count)

/-- The actual affine cover source with its indices in the ambient universe. -/
def groupsSpace : Scheme.{u} := ∐ (fun a : D.Index => Spec (D.charts a.down).2.ring)

/-- The actual cover map for the assembled groups. -/
def groupsBaseMap : D.groupsSpace ⟶ S :=
  Sigma.desc (fun a : D.Index => (D.charts a.down).2.projection)

instance affine_groupsSpace : IsAffine D.groupsSpace := by
  dsimp only [groupsSpace]
  infer_instance

instance etale_groupsBaseMap : Etale D.groupsBaseMap := by
  apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
  intro a
  exact (D.charts a.down).2.etale

instance surjective_groupsBaseMap : Surjective D.groupsBaseMap := by
  constructor
  intro s
  obtain ⟨a, y, hy⟩ := D.covers s
  let X := fun a : D.Index => Spec (D.charts a.down).2.ring
  refine ⟨Sigma.ι X ⟨a⟩ y, ?_⟩
  have he : Sigma.ι X ⟨a⟩ ≫ D.groupsBaseMap = (D.charts a).2.projection :=
    Sigma.ι_comp_desc _ _
  have hv := congrArg (fun f => f y) he
  rw [Scheme.Hom.comp_apply] at hv
  exact hv.trans hy

/-- Inclusion of an actual affine chart component in the finite cover. -/
def componentMap (a : D.Index) : Spec (D.charts a.down).2.ring ⟶ D.groupsSpace :=
  Sigma.ι (fun a : D.Index => Spec (D.charts a.down).2.ring) a

local instance component_decomposition : IsIso (Sigma.desc D.componentMap) := by
  change IsIso (Sigma.desc (Sigma.ι (fun a : D.Index => Spec (D.charts a.down).2.ring)))
  rw [Sigma.desc_ι]
  infer_instance

/-- The actual assembled weighted term over the affine cover source. -/
def termGroup (d : ℕ) : GroupScheme D.groupsSpace :=
  DisjointGroupAssembly.group D.componentMap (fun a => (D.charts a.down).2.termGroup d)

/-- The actual assembled vector layer over the affine cover source. -/
def layerGroup (d : ℕ) : GroupScheme D.groupsSpace :=
  DisjointGroupAssembly.group D.componentMap (fun a => (D.charts a.down).2.layerGroup d)

/-- Pullback to a component recovers its original actual term. -/
def termComponentIso (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).obj (D.termGroup d) ≅ (D.charts a.down).2.termGroup d :=
  DisjointGroupAssembly.componentIso D.componentMap _ a

/-- Pullback to a component recovers its original actual vector group. -/
def layerComponentIso (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).obj (D.layerGroup d) ≅ (D.charts a.down).2.layerGroup d :=
  DisjointGroupAssembly.componentIso D.componentMap _ a

/-- The actual iterated ambient pullback agrees with the original chart pullback. -/
def ambientComponentIso (a : D.Index) :
    (baseChange (D.componentMap a)).obj ((baseChange D.groupsBaseMap).obj G) ≅
      (baseChange (D.charts a.down).2.projection).obj G :=
  Descent.pullbackComparison D.groupsBaseMap (D.componentMap a) (D.charts a.down).2.projection
    (by simp only [componentMap, groupsBaseMap, Sigma.ι_comp_desc]) G

/-- The actual inclusion of the assembled term into the original pulled-back ambient group. -/
def termInclusion (d : ℕ) : D.termGroup d ⟶ (baseChange D.groupsBaseMap).obj G :=
  DisjointComponents.groupHom D.componentMap (fun a =>
    (D.termComponentIso d a).hom ≫ (D.charts a.down).2.termInclusion d ≫
      (D.ambientComponentIso a).inv)

/-- The ambient map recovers the ORIGINAL chart inclusion under the actual comparisons. -/
theorem termInclusion_component (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).map (D.termInclusion d) ≫ (D.ambientComponentIso a).hom =
      (D.termComponentIso d a).hom ≫ (D.charts a.down).2.termInclusion d := by
  rw [termInclusion, DisjointComponents.map_groupHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual assembled inclusion of consecutive terms. -/
def termStep (d : ℕ) : D.termGroup (d + 1) ⟶ D.termGroup d :=
  DisjointGroupAssembly.homOfFamily D.componentMap
    (fun a => (D.charts a.down).2.termGroup (d + 1)) (fun a => (D.charts a.down).2.termGroup d)
    (fun a => (D.charts a.down).2.termStep d)

/-- Consecutive maps recover the prescribed original chart maps. -/
theorem termStep_component (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).map (D.termStep d) ≫ (D.termComponentIso d a).hom =
      (D.termComponentIso (d + 1) a).hom ≫ (D.charts a.down).2.termStep d :=
  DisjointGroupAssembly.homOfFamily_component _ _ _ _ _

/-- The actual assembled projection to the vector layer. -/
def layerProjection (d : ℕ) : D.termGroup d ⟶ D.layerGroup d :=
  DisjointGroupAssembly.homOfFamily D.componentMap
    (fun a => (D.charts a.down).2.termGroup d) (fun a => (D.charts a.down).2.layerGroup d)
    (fun a => (D.charts a.down).2.layerProjection d)

/-- The projection recovers each original actual quotient homomorphism. -/
theorem layerProjection_component (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).map (D.layerProjection d) ≫ (D.layerComponentIso d a).hom =
      (D.termComponentIso d a).hom ≫ (D.charts a.down).2.layerProjection d :=
  DisjointGroupAssembly.homOfFamily_component _ _ _ _ _

/-- The assembled successive maps preserve the actual original ambient inclusions. -/
theorem termStep_comp_inclusion (d : ℕ) :
    D.termStep d ≫ D.termInclusion d = D.termInclusion (d + 1) := by
  apply DisjointComponents.groupHom_ext D.componentMap
  intro a
  apply (cancel_mono (D.ambientComponentIso a).hom).mp
  rw [Functor.map_comp, Category.assoc, D.termInclusion_component,
    ← Category.assoc, D.termStep_component, Category.assoc,
    (D.charts a.down).2.termStep_comp_inclusion, D.termInclusion_component]

instance affine_termGroup (d : ℕ) : IsAffine (D.termGroup d).X.left := by
  dsimp only [termGroup]
  infer_instance

instance affine_layerGroup (d : ℕ) : IsAffine (D.layerGroup d).X.left := by
  dsimp only [layerGroup]
  infer_instance

end FiniteParabolicFaceCover
end Langlands.GroupScheme.RelativeLevi

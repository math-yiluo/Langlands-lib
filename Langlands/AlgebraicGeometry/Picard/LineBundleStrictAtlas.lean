import Langlands.AlgebraicGeometry.Modules.CommonSourceTransitionTransport
import Langlands.AlgebraicGeometry.Picard.OpenPairLineBundleGluing
import Langlands.CategoryTheory.StrictCocycleAtlas

/-! # Strict atlases of actual line bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules.CommonSourceCocycle

/-- A fixed small family of actual line bundles on open charts. -/
structure LineBundleChartFamily (X : Scheme.{u}) where
  Index : Type u
  source : Index → Scheme.{u}
  map : ∀ i, source i ⟶ X
  isOpen : ∀ i, IsOpenImmersion (map i)
  bundle : ∀ i, LineBundle (source i)

attribute [instance] LineBundleChartFamily.isOpen

namespace LineBundleChartFamily

variable {X : Scheme.{u}} (F : LineBundleChartFamily X)

/-- The actual module identification on an ambient overlap. -/
def Transition (i j : F.Index) :=
  (Scheme.Modules.pullback (pullback.fst (F.map i) (F.map j))).obj (F.bundle i).obj ≅
    (Scheme.Modules.pullback (pullback.snd (F.map i) (F.map j))).obj (F.bundle j).obj

/-- Equal ambient composites are already equal over a monomorphic source. -/
lemma factor_condition {V A B W : Scheme.{u}} (v : V ⟶ X) [Mono v]
    (a : A ⟶ V) (b : B ⟶ V) (f : A ⟶ X) (g : B ⟶ X)
    (ha : a ≫ v = f) (hb : b ≫ v = g) (p : W ⟶ A) (q : W ⟶ B)
    (hpq : p ≫ f = q ≫ g) : p ≫ a = q ≫ b := by
  apply (cancel_mono v).1
  simpa only [Category.assoc, ha, hb] using hpq

/-- A common actual module realizing an arbitrary selection of charts. -/
structure CommonSource (A : Set F.Index) where
  space : Scheme.{u}
  into : space ⟶ X
  mono : Mono into
  module : space.Modules
  chart : ∀ i : A, F.source i ⟶ space
  fac : ∀ i : A, chart i ≫ into = F.map i
  comparison : ∀ i : A, (Scheme.Modules.pullback (chart i)).obj module ≅ (F.bundle i).obj

attribute [instance] CommonSource.mono

namespace CommonSource

variable {F} {A : Set F.Index} (R : F.CommonSource A)

/-- The ambient overlap transition induced by the common source. -/
def transition (i j : A) : F.Transition i j :=
  Langlands.Scheme.Modules.CommonSourceCocycle.transition
    (pullback.fst (F.map i) (F.map j)) (pullback.snd (F.map i) (F.map j))
    (R.chart i) (R.chart j)
    (factor_condition R.into _ _ _ _ (R.fac i) (R.fac j) _ _ pullback.condition)
    R.module (R.comparison i) (R.comparison j)

end CommonSource

/-- A common actual module for three charts, with all their factorizations. -/
structure TripleSource (i j k : F.Index) where
  space : Scheme.{u}
  into : space ⟶ X
  mono : Mono into
  module : space.Modules
  a : F.source i ⟶ space
  b : F.source j ⟶ space
  c : F.source k ⟶ space
  ha : a ≫ into = F.map i
  hb : b ≫ into = F.map j
  hc : c ≫ into = F.map k
  ea : (Scheme.Modules.pullback a).obj module ≅ (F.bundle i).obj
  eb : (Scheme.Modules.pullback b).obj module ≅ (F.bundle j).obj
  ec : (Scheme.Modules.pullback c).obj module ≅ (F.bundle k).obj

attribute [instance] TripleSource.mono

namespace TripleSource

variable {F} {i j k : F.Index} (R : F.TripleSource i j k)

def first : F.Transition i j :=
  Langlands.Scheme.Modules.CommonSourceCocycle.transition _ _ R.a R.b
    (factor_condition R.into _ _ _ _ R.ha R.hb _ _ pullback.condition)
    R.module R.ea R.eb

def second : F.Transition j k :=
  Langlands.Scheme.Modules.CommonSourceCocycle.transition _ _ R.b R.c
    (factor_condition R.into _ _ _ _ R.hb R.hc _ _ pullback.condition)
    R.module R.eb R.ec

def third : F.Transition i k :=
  Langlands.Scheme.Modules.CommonSourceCocycle.transition _ _ R.a R.c
    (factor_condition R.into _ _ _ _ R.ha R.hc _ _ pullback.condition)
    R.module R.ea R.ec

end TripleSource

/-- Every triple of actual transitions is realized from one actual module. -/
def TripleCompatible (i j k : F.Index)
    (eij : F.Transition i j) (ejk : F.Transition j k) (eik : F.Transition i k) : Prop :=
  ∃ R : F.TripleSource i j k, eij = R.first ∧ ejk = R.second ∧ eik = R.third

lemma CommonSource.tripleCompatible {A : Set F.Index} (R : F.CommonSource A) (i j k : A) :
    F.TripleCompatible i j k (R.transition i j) (R.transition j k) (R.transition i k) := by
  exact ⟨{
    space := R.space
    into := R.into
    mono := R.mono
    module := R.module
    a := R.chart i
    b := R.chart j
    c := R.chart k
    ha := R.fac i
    hb := R.fac j
    hc := R.fac k
    ea := R.comparison i
    eb := R.comparison j
    ec := R.comparison k }, rfl, rfl, rfl⟩

/-- The open region covered by the selected charts. -/
def region (A : Set F.Index) : X.Opens := ⨆ i : A, (F.map i).opensRange

lemma range_le_region {A : Set F.Index} (i : A) : Set.range (F.map i) ⊆ F.region A :=
  le_iSup (fun i : A ↦ (F.map i).opensRange) i

/-- The selected chart factored through its open region. -/
def factor {A : Set F.Index} (i : A) : F.source i ⟶ (F.region A).toScheme :=
  OpenUnion.lift (F.map i) _ (F.range_le_region i)

instance {A : Set F.Index} (i : A) : IsOpenImmersion (F.factor i) := by
  unfold factor
  infer_instance

@[reassoc (attr := simp)]
lemma factor_ι {A : Set F.Index} (i : A) : F.factor i ≫ (F.region A).ι = F.map i :=
  OpenUnion.lift_ι _ _ _

/-- The selected charts form an actual open cover of their region. -/
abbrev regionCover (A : Set F.Index) : (F.region A).toScheme.OpenCover.{u} where
  I₀ := A
  X i := F.source i
  f i := F.factor i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x.1 ∈ F.region A := x.2
    simp only [region, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, y, hy⟩ := hx
    refine ⟨i, y, ?_⟩
    apply Subtype.ext
    change (F.factor i ≫ (F.region A).ι) y = x.1
    rw [factor_ι]
    exact hy

/-- Transport an ambient transition to the overlap over a containing open. -/
def regionTransition {A : Set F.Index} (i j : A) (φ : F.Transition i j) :
    (Scheme.Modules.pullback (pullback.fst (F.factor i) (F.factor j))).obj (F.bundle i).obj ≅
      (Scheme.Modules.pullback (pullback.snd (F.factor i) (F.factor j))).obj (F.bundle j).obj :=
  OpenUnion.overlap (F.map i) (F.map j) (F.region A)
    (F.range_le_region i) (F.range_le_region j) (F.bundle i).obj (F.bundle j).obj φ

/-- Restricting an induced transition to the region retains the common source. -/
lemma regionTransition_transition {A : Set F.Index} (i j : A) {V : Scheme.{u}}
    (a : F.source i ⟶ V) (b : F.source j ⟶ V)
    (h : pullback.fst (F.map i) (F.map j) ≫ a =
      pullback.snd (F.map i) (F.map j) ≫ b)
    (h' : pullback.fst (F.factor i) (F.factor j) ≫ a =
      pullback.snd (F.factor i) (F.factor j) ≫ b)
    (N : V.Modules)
    (ea : (Scheme.Modules.pullback a).obj N ≅ (F.bundle i).obj)
    (eb : (Scheme.Modules.pullback b).obj N ≅ (F.bundle j).obj) :
    F.regionTransition i j (transition _ _ a b h N ea eb) =
      transition _ _ a b h' N ea eb := by
  exact transport_transition
    (OpenUnion.overlapIso (F.map i) (F.map j) (F.region A)
      (F.range_le_region i) (F.range_le_region j)).hom _ _ _ _
    (OpenUnion.overlapIso_hom_fst _ _ _ _ _)
    (OpenUnion.overlapIso_hom_snd _ _ _ _ _) a b h h' N ea eb

/-- The two region-overlap maps agree after composition with the ambient maps. -/
lemma factor_overlap {A : Set F.Index} (i j : A) :
    pullback.fst (F.factor i) (F.factor j) ≫ F.map i =
      pullback.snd (F.factor i) (F.factor j) ≫ F.map j := by
  rw [← F.factor_ι i, ← F.factor_ι j, ← Category.assoc,
    pullback.condition, Category.assoc]

/-- Triple common-source witnesses give the actual region-cover cocycle. -/
lemma region_cocycle {A : Set F.Index} (t : ∀ i j : A, F.Transition i j)
    (ht : ∀ i j k : A, F.TripleCompatible i j k (t i j) (t j k) (t i k)) :
    Langlands.Scheme.Modules.OpenCoverModuleGluing.CocycleCondition (F.regionCover A)
      (fun i : A ↦ (F.bundle i).obj) (fun i j ↦ F.regionTransition i j (t i j)) := by
  intro i j k
  dsimp only [regionCover]
  obtain ⟨R, hij, hjk, hik⟩ := ht i j k
  rw [hij, hjk, hik]
  dsimp only [TripleSource.first, TripleSource.second, TripleSource.third]
  rw [F.regionTransition_transition i j R.a R.b _ (factor_condition R.into _ _ _ _
      R.ha R.hb _ _ (F.factor_overlap i j)),
    F.regionTransition_transition j k R.b R.c _ (factor_condition R.into _ _ _ _
      R.hb R.hc _ _ (F.factor_overlap j k)),
    F.regionTransition_transition i k R.a R.c _ (factor_condition R.into _ _ _ _
      R.ha R.hc _ _ (F.factor_overlap i k))]
  apply Langlands.Scheme.Modules.OpenCoverModuleGluing.CompEq4.of_eq
  apply transition_cocycle

/-- The actual line-bundle descent datum of a compatible partial atlas. -/
def gluingData {A : Set F.Index} (t : ∀ i j : A, F.Transition i j)
    (ht : ∀ i j k : A, F.TripleCompatible i j k (t i j) (t j k) (t i k)) :
    LineBundleGluingData (F.regionCover A) where
  bundle i := F.bundle (i : A)
  transition i j := F.regionTransition i j (t i j)
  cocycle := F.region_cocycle t ht

/-- The change from the ambient overlap to the region overlap is injective. -/
lemma regionTransition_injective {A : Set F.Index} (i j : A) :
    Function.Injective (F.regionTransition i j) := by
  exact transport_injective
    (OpenUnion.overlapIso (F.map i) (F.map j) (F.region A)
      (F.range_le_region i) (F.range_le_region j)).hom _ _ _ _
    (OpenUnion.overlapIso_hom_fst _ _ _ _ _)
    (OpenUnion.overlapIso_hom_snd _ _ _ _ _)

/-- The glued module and its comparisons recover the region transition exactly. -/
lemma gluingData_transition {A : Set F.Index} (t : ∀ i j : A, F.Transition i j)
    (ht : ∀ i j k : A, F.TripleCompatible i j k (t i j) (t j k) (t i k))
    (i j : A) :
    transition _ _ (F.factor i) (F.factor j) pullback.condition
      (F.gluingData t ht).gluedModule
      ((F.gluingData t ht).moduleIso i) ((F.gluingData t ht).moduleIso j) =
        F.regionTransition i j (t i j) := by
  ext1
  rw [← cancel_epi ((Scheme.Modules.pullback (pullback.fst (F.factor i) (F.factor j))).map
    ((F.gluingData t ht).moduleIso i).hom)]
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc _ ((F.gluingData t ht).moduleIso i).hom,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((F.gluingData t ht).moduleIso_compatible i j).symm

/-- The actual line bundle realizing a compatible atlas on its region. -/
def glue {A : Set F.Index} (t : ∀ i j : A, F.Transition i j)
    (ht : ∀ i j k : A, F.TripleCompatible i j k (t i j) (t j k) (t i k)) :
    LineBundle (F.region A).toScheme :=
  (F.gluingData t ht).glue

/-- A realization of all selected charts by the actual glued module. -/
def realization {A : Set F.Index} (t : ∀ i j : A, F.Transition i j)
    (ht : ∀ i j k : A, F.TripleCompatible i j k (t i j) (t j k) (t i k)) :
    F.CommonSource A where
  space := (F.region A).toScheme
  into := (F.region A).ι
  mono := inferInstance
  module := (F.glue t ht).obj
  chart := F.factor
  fac := F.factor_ι
  comparison := (F.gluingData t ht).moduleIso

/-- Realization recovers every specified ambient transition as an actual isomorphism. -/
lemma realization_transition {A : Set F.Index} (t : ∀ i j : A, F.Transition i j)
    (ht : ∀ i j k : A, F.TripleCompatible i j k (t i j) (t j k) (t i k))
    (i j : A) : (F.realization t ht).transition i j = t i j := by
  apply F.regionTransition_injective i j
  dsimp only [CommonSource.transition, realization]
  rw [F.regionTransition_transition i j (F.factor i) (F.factor j) _
    pullback.condition]
  exact F.gluingData_transition t ht i j

/-- Labels recording charts and actual ambient transitions. -/
abbrev AtlasLabel := Langlands.CategoryTheory.StrictCocycleAtlas.Label F.Transition

/-- A strict partial atlas with common-module witnesses for every triple. -/
abbrev GoodAtlas (i₀ : F.Index) (S : Set F.AtlasLabel) : Prop :=
  Langlands.CategoryTheory.StrictCocycleAtlas.Good F.TripleCompatible i₀ S

/-- The actual common module realizing a good strict atlas. -/
def atlasRealization {i₀ : F.Index} {S : Set F.AtlasLabel} (h : F.GoodAtlas i₀ S) :
    F.CommonSource (Langlands.CategoryTheory.StrictCocycleAtlas.domain S) :=
  F.realization (Langlands.CategoryTheory.StrictCocycleAtlas.transition h)
    (Langlands.CategoryTheory.StrictCocycleAtlas.transition_cocycle h)

/-- The realization retains the exact transition labels of the good atlas. -/
lemma atlasRealization_transition {i₀ : F.Index} {S : Set F.AtlasLabel}
    (h : F.GoodAtlas i₀ S) (i j : Langlands.CategoryTheory.StrictCocycleAtlas.domain S) :
    (F.atlasRealization h).transition i j =
      Langlands.CategoryTheory.StrictCocycleAtlas.transition h i j :=
  F.realization_transition _ _ i j

end LineBundleChartFamily

end Langlands.AlgebraicGeometry.Picard

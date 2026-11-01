import Langlands.AlgebraicGeometry.Picard.LineBundleStrictAtlas

/-! # Enlarging a strict line-bundle atlas -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundleChartFamily

open Langlands.Scheme.Modules.CommonSourceCocycle

variable {X : Scheme.{u}} {F : LineBundleChartFamily X}

namespace CommonSource

variable {A : Set F.Index} (R : F.CommonSource A)

/-- Replace a common module by an identified pullback from a larger source. -/
def changeSource {W : Scheme.{u}} (w : W ⟶ X) [Mono w]
    (h : R.space ⟶ W) (hw : h ≫ w = R.into) (K : W.Modules)
    (e : (Scheme.Modules.pullback h).obj K ≅ R.module) : F.CommonSource A where
  space := W
  into := w
  mono := inferInstance
  module := K
  chart i := R.chart i ≫ h
  fac i := by rw [Category.assoc, hw, R.fac]
  comparison i := sourceComparison (R.chart i) h R.module K e (R.comparison i)

/-- Changing the common source preserves the actual ambient transition. -/
lemma changeSource_transition {W : Scheme.{u}} (w : W ⟶ X) [Mono w]
    (h : R.space ⟶ W) (hw : h ≫ w = R.into) (K : W.Modules)
    (e : (Scheme.Modules.pullback h).obj K ≅ R.module) (i j : A) :
    (R.changeSource w h hw K e).transition i j = R.transition i j := by
  apply transition_changeSource

/-- One chart factor and its identification with the common module. -/
structure ChartData (i : F.Index) where
  chart : F.source i ⟶ R.space
  fac : chart ≫ R.into = F.map i
  comparison : (Scheme.Modules.pullback chart).obj R.module ≅ (F.bundle i).obj

/-- Add an identified chart while retaining the old chart data as a whole. -/
def insertData (j : F.Index) (b : F.source j ⟶ R.space)
    (hb : b ≫ R.into = F.map j)
    (eb : (Scheme.Modules.pullback b).obj R.module ≅ (F.bundle j).obj)
    (i : ↥(Set.insert j A)) : R.ChartData i := by
  classical
  exact if h : i.val ∈ A then
    ⟨R.chart ⟨i.val, h⟩, R.fac ⟨i.val, h⟩, R.comparison ⟨i.val, h⟩⟩
  else by
    rcases i with ⟨i, hi⟩
    have hij : i = j := (Set.mem_insert_iff.mp hi).resolve_right h
    subst i
    exact ⟨b, hb, eb⟩

@[simp]
lemma insertData_old (j : F.Index) (b : F.source j ⟶ R.space)
    (hb : b ≫ R.into = F.map j)
    (eb : (Scheme.Modules.pullback b).obj R.module ≅ (F.bundle j).obj) (i : A) :
    R.insertData j b hb eb ⟨i.val, Set.mem_insert_of_mem j i.property⟩ =
      ⟨R.chart i, R.fac i, R.comparison i⟩ := by
  classical
  simp only [insertData, dite_eq_left i.property]

/-- Insert a chart whose bundle is already identified with the common module. -/
def insert (j : F.Index) (b : F.source j ⟶ R.space) (hb : b ≫ R.into = F.map j)
    (eb : (Scheme.Modules.pullback b).obj R.module ≅ (F.bundle j).obj) :
    F.CommonSource (Set.insert j A) where
  space := R.space
  into := R.into
  mono := R.mono
  module := R.module
  chart i := (R.insertData j b hb eb i).chart
  fac i := (R.insertData j b hb eb i).fac
  comparison i := (R.insertData j b hb eb i).comparison

/-- Inserting a chart preserves the old transitions as actual isomorphisms. -/
lemma insert_transition (j : F.Index) (b : F.source j ⟶ R.space)
    (hb : b ≫ R.into = F.map j)
    (eb : (Scheme.Modules.pullback b).obj R.module ≅ (F.bundle j).obj) (i k : A) :
    (R.insert j b hb eb).transition
      ⟨i.val, Set.mem_insert_of_mem j i.property⟩
      ⟨k.val, Set.mem_insert_of_mem j k.property⟩ = R.transition i k := by
  dsimp only [LineBundleChartFamily.Transition, CommonSource.transition, insert]
  have h := congrArg₂ (fun (di : R.ChartData i.val) (dk : R.ChartData k.val) ↦
    Langlands.Scheme.Modules.CommonSourceCocycle.transition
      (pullback.fst (F.map i) (F.map k)) (pullback.snd (F.map i) (F.map k))
      di.chart dk.chart
      (factor_condition R.into _ _ _ _ di.fac dk.fac _ _ pullback.condition)
      R.module di.comparison dk.comparison)
    (R.insertData_old j b hb eb i) (R.insertData_old j b hb eb k)
  exact h

/-- Glue one more open chart to a line-bundle common source. -/
def enlarge [IsOpenImmersion R.into] (hR : IsLocallyFreeRankOne R.module)
    (j : F.Index)
    (φ : (Scheme.Modules.pullback (pullback.fst R.into (F.map j))).obj R.module ≅
      (Scheme.Modules.pullback (pullback.snd R.into (F.map j))).obj (F.bundle j).obj) :
    F.CommonSource (Set.insert j A) :=
  let L : LineBundle R.space := ⟨R.module, hR⟩
  let K := OpenUnion.glue R.into (F.map j) L (F.bundle j) φ
  let R' := R.changeSource (R.into.opensRange ⊔ (F.map j).opensRange).ι
    (OpenUnion.left R.into (F.map j)) (OpenUnion.left_ι _ _) K.obj
    (OpenUnion.leftModuleIso R.into (F.map j) L (F.bundle j) φ)
  R'.insert j (OpenUnion.right R.into (F.map j)) (OpenUnion.right_ι _ _)
    (OpenUnion.rightModuleIso R.into (F.map j) L (F.bundle j) φ)

/-- Enlargement retains every old ambient transition exactly. -/
lemma enlarge_transition [IsOpenImmersion R.into] (hR : IsLocallyFreeRankOne R.module)
    (j : F.Index)
    (φ : (Scheme.Modules.pullback (pullback.fst R.into (F.map j))).obj R.module ≅
      (Scheme.Modules.pullback (pullback.snd R.into (F.map j))).obj (F.bundle j).obj)
    (i k : A) :
    (R.enlarge hR j φ).transition
      ⟨i.val, Set.mem_insert_of_mem j i.property⟩
      ⟨k.val, Set.mem_insert_of_mem j k.property⟩ = R.transition i k := by
  dsimp only [enlarge]
  rw [insert_transition, changeSource_transition]

end CommonSource

open Langlands.CategoryTheory.StrictCocycleAtlas

/-- A chart compatible with the realized bundle of a maximal atlas is already present. -/
lemma maximal_contains_chart {i₀ : F.Index} {S : Set F.AtlasLabel}
    (hm : Maximal (F.GoodAtlas i₀) S) (j : F.Index)
    (φ : (Scheme.Modules.pullback
        (pullback.fst (F.atlasRealization hm.1).into (F.map j))).obj
          (F.atlasRealization hm.1).module ≅
      (Scheme.Modules.pullback
        (pullback.snd (F.atlasRealization hm.1).into (F.map j))).obj (F.bundle j).obj) :
    j ∈ domain S := by
  let R := F.atlasRealization hm.1
  have : IsOpenImmersion R.into := by
    dsimp only [R, atlasRealization, realization]
    infer_instance
  have hR : IsLocallyFreeRankOne R.module := (F.glue _ _).property
  let E := R.enlarge hR j φ
  have hdom : Set.insert j (domain S) = domain S :=
    maximal_domain hm (fun _ hi ↦ Set.mem_insert_of_mem j hi) E.transition
      (fun i k ↦ (R.enlarge_transition hR j φ i k).trans
        (F.atlasRealization_transition hm.1 i k)) E.tripleCompatible
  rw [← hdom]
  exact Set.mem_insert j _

end Langlands.AlgebraicGeometry.Picard.LineBundleChartFamily

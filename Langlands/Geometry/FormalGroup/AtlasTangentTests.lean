import Langlands.Geometry.FormalGroup.AtlasTangentChart
import Langlands.Geometry.FormalGroup.AtlasTangentOrder

/-! # Test algebra maps on compatible tangent vectors -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open _root_.CategoryTheory

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {I : Type} [Finite I] (X : BasicAtlas O R I)
variable {A B C : CommAlgCat.{v} R}

/-- Evaluate a compatible family in any specified chart test. -/
def tangentTestEvaluation (z : X.tangentSubmodule A) (t : X.ChartTest A) : I → t.algebra :=
  fun i => (X.testFactor t).hom (z.val t.chart i)

/-- Evaluation commutes with the actual test coefficient map. -/
theorem tangentTestEvaluation_map (z : X.tangentSubmodule A) (t : X.ChartTest A)
    (f : t.algebra ⟶ B) (h : IsUnit (algebraMap R B t.chart.val)) :
    (fun i => f.hom (X.tangentTestEvaluation z t i)) =
      X.tangentTestEvaluation z ⟨B, t.map ≫ f, t.chart, h⟩ :=
  funext fun i => congrArg (fun g : X.localAlgebra A t.chart ⟶ B => g.hom (z.val t.chart i))
    (X.testFactor_comp t f h)

/-- Evaluation in the universal chart localization recovers that component of the family. -/
@[simp]
theorem tangentTestEvaluation_localTest (z : X.tangentSubmodule A) (a : X.opens) :
    X.tangentTestEvaluation z (X.localTest A a) = z.val a :=
  funext fun i => congrArg (fun g : X.localAlgebra A a ⟶ X.localAlgebra A a => g.hom (z.val a i))
    (X.testFactor_localTest A a)

/-- Compatible vectors in a simultaneous chart test are related by the actual derivative transition. -/
theorem tangentTestEvaluation_transition (z : X.tangentSubmodule A) (f : A ⟶ B)
    (a b : X.opens) (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    X.transitionTangent B a b ha hb (X.tangentTestEvaluation z ⟨B, f, a, ha⟩) =
      X.tangentTestEvaluation z ⟨B, f, b, hb⟩ := by
  let S := X.overlapAlgebra A a b
  let g := X.overlapFactor f a b ha hb
  let l := X.overlapFromLeft A a b
  let r := X.overlapFromRight A a b
  let x : I → S := fun i => l.hom (z.val a i)
  let y : I → S := fun i => r.hom (z.val b i)
  have h : X.transitionTangent S a b (X.overlapUnitLeft A a b)
      (X.overlapUnitRight A a b) x = y := (X.mem_tangentSubmodule A z.val).mp z.property a b
  have hg := congrArg (fun v : I → S => fun i => g.hom (v i)) h
  rw [X.transitionTangent_natural g a b _ _ ha hb x] at hg
  have hl : (fun i => g.hom (x i)) = X.tangentTestEvaluation z ⟨B, f, a, ha⟩ :=
    funext fun i => congrArg (fun q : X.localAlgebra A a ⟶ B => q.hom (z.val a i))
      (X.overlapFromLeft_factor f a b ha hb)
  have hr : (fun i => g.hom (y i)) = X.tangentTestEvaluation z ⟨B, f, b, hb⟩ :=
    funext fun i => congrArg (fun q : X.localAlgebra A b ⟶ B => q.hom (z.val b i))
      (X.overlapFromRight_factor f a b ha hb)
  rw [hl, hr] at hg
  exact hg

/-- The induced test map between the chart localizations over two test rings. -/
def tangentLocalizedTestMap (f : A ⟶ B) (a : X.opens) :
    X.localAlgebra A a ⟶ X.localAlgebra B a :=
  X.testFactor ⟨X.localAlgebra B a, f ≫ X.localizationMap B a, a, X.localUnit B a⟩

@[reassoc]
theorem localizationMap_tangentLocalizedTestMap (f : A ⟶ B) (a : X.opens) :
    X.localizationMap A a ≫ X.tangentLocalizedTestMap f a = f ≫ X.localizationMap B a :=
  X.localizationMap_testFactor ⟨X.localAlgebra B a, f ≫ X.localizationMap B a, a, X.localUnit B a⟩

private theorem tangentMap_mem (f : A ⟶ B) (z : X.tangentSubmodule A) :
    (fun a i => (X.tangentLocalizedTestMap f a).hom (z.val a i)) ∈ X.tangentSubmodule B := by
  apply (X.mem_tangentSubmodule B _).mpr
  intro a b
  let S := X.overlapAlgebra B a b
  let ha := X.overlapUnitLeft B a b
  let hb := X.overlapUnitRight B a b
  let q := f ≫ X.overlapMap B a b
  let t : X.ChartTest A := ⟨X.localAlgebra B a, f ≫ X.localizationMap B a, a, X.localUnit B a⟩
  let u : X.ChartTest A := ⟨X.localAlgebra B b, f ≫ X.localizationMap B b, b, X.localUnit B b⟩
  let l := X.overlapFromLeft B a b
  let r := X.overlapFromRight B a b
  have hl : t.map ≫ l = q := by
    rw [show t.map = f ≫ X.localizationMap B a from rfl, Category.assoc]
    exact congrArg (fun k : B ⟶ S => f ≫ k)
      (X.localizationMap_testFactor ⟨S, X.overlapMap B a b, a, ha⟩)
  have hr : u.map ≫ r = q := by
    rw [show u.map = f ≫ X.localizationMap B b from rfl, Category.assoc]
    exact congrArg (fun k : B ⟶ S => f ≫ k)
      (X.localizationMap_testFactor ⟨S, X.overlapMap B a b, b, hb⟩)
  have hleft : (fun i => l.hom (X.tangentTestEvaluation z t i)) =
      X.tangentTestEvaluation z ⟨S, q, a, ha⟩ := by
    rw [X.tangentTestEvaluation_map z t l ha, hl]
  have hright : (fun i => r.hom (X.tangentTestEvaluation z u i)) =
      X.tangentTestEvaluation z ⟨S, q, b, hb⟩ := by
    rw [X.tangentTestEvaluation_map z u r hb, hr]
  change X.transitionTangent S a b ha hb
      (fun i => l.hom (X.tangentTestEvaluation z t i)) =
    fun i => r.hom (X.tangentTestEvaluation z u i)
  rw [hleft, hright]
  exact X.tangentTestEvaluation_transition z q a b ha hb

/-- Extend compatible tangent vectors along a coefficient map, semilinearly over the test rings. -/
def tangentMap (f : A ⟶ B) : X.tangentSubmodule A →ₛₗ[f.hom.toRingHom] X.tangentSubmodule B where
  toFun z := ⟨fun a i => (X.tangentLocalizedTestMap f a).hom (z.val a i), X.tangentMap_mem f z⟩
  map_add' z w := Subtype.ext (funext fun a => funext fun i =>
    map_add (X.tangentLocalizedTestMap f a).hom (z.val a i) (w.val a i))
  map_smul' c z := by
    apply Subtype.ext
    funext a i
    let k := X.tangentLocalizedTestMap f a
    change k.hom (c • z.val a i) = (f.hom c) • k.hom (z.val a i)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * k.hom (z.val a i))
      (congrArg (fun q : A ⟶ X.localAlgebra B a => q.hom c)
        (X.localizationMap_tangentLocalizedTestMap f a))

@[simp]
theorem tangentMap_apply (f : A ⟶ B) (z : X.tangentSubmodule A) (a : X.opens) (i : I) :
    (X.tangentMap f z).val a i = (X.tangentLocalizedTestMap f a).hom (z.val a i) := rfl

/-- Evaluation after extension to another test agrees with evaluation on the composite test. -/
theorem tangentTestEvaluation_tangentMap (f : A ⟶ B) (z : X.tangentSubmodule A)
    (t : X.ChartTest B) :
    X.tangentTestEvaluation (X.tangentMap f z) t =
      X.tangentTestEvaluation z ⟨t.algebra, f ≫ t.map, t.chart, t.isUnit⟩ := by
  let a := t.chart
  let k : X.ChartTest A := ⟨X.localAlgebra B a, f ≫ X.localizationMap B a, a, X.localUnit B a⟩
  have hk : k.map ≫ X.testFactor t = f ≫ t.map := by
    change (f ≫ X.localizationMap B a) ≫ X.testFactor t = _
    rw [Category.assoc, X.localizationMap_testFactor t]
  change (fun i => (X.testFactor t).hom (X.tangentTestEvaluation z k i)) = _
  rw [X.tangentTestEvaluation_map z k (X.testFactor t) t.isUnit, hk]

@[simp]
theorem tangentMap_id (z : X.tangentSubmodule A) : X.tangentMap (𝟙 A) z = z := by
  apply Subtype.ext
  funext a
  have h := X.tangentTestEvaluation_tangentMap (𝟙 A) z (X.localTest A a)
  rw [Category.id_comp] at h
  exact (X.tangentTestEvaluation_localTest (X.tangentMap (𝟙 A) z) a).symm.trans
    (h.trans (X.tangentTestEvaluation_localTest z a))

/-- Successive coefficient extensions act as their composite. -/
theorem tangentMap_comp (f : A ⟶ B) (g : B ⟶ C) (z : X.tangentSubmodule A) :
    X.tangentMap (f ≫ g) z = X.tangentMap g (X.tangentMap f z) := by
  apply Subtype.ext
  funext a
  let t := X.localTest C a
  have h : X.tangentTestEvaluation (X.tangentMap (f ≫ g) z) t =
      X.tangentTestEvaluation (X.tangentMap g (X.tangentMap f z)) t := by
    rw [X.tangentTestEvaluation_tangentMap (f ≫ g) z t,
      X.tangentTestEvaluation_tangentMap g (X.tangentMap f z) t,
      X.tangentTestEvaluation_tangentMap f z, Category.assoc]
  exact (X.tangentTestEvaluation_localTest (X.tangentMap (f ≫ g) z) a).symm.trans
    (h.trans (X.tangentTestEvaluation_localTest _ a))

/-- Evaluation in a chart respects the full order action. -/
theorem OrderAction.tangentTestEvaluation_action {D : Type w} [Ring D] [Algebra O D]
    (E : OrderAction D X) (z : X.tangentSubmodule A) (t : X.ChartTest A) (d : D) :
    X.tangentTestEvaluation (E.tangentAction A d z) t =
      E.chartTangent t.algebra t.chart t.isUnit d (X.tangentTestEvaluation z t) :=
  E.chartTangent_natural (X.testFactor t) t.chart (X.localUnit A t.chart) t.isUnit d
    (z.val t.chart)

/-- Coefficient extension between test rings respects the action of the full order. -/
theorem OrderAction.tangentMap_action {D : Type w} [Ring D] [Algebra O D]
    (E : OrderAction D X) (f : A ⟶ B) (d : D) (z : X.tangentSubmodule A) :
    X.tangentMap f (E.tangentAction A d z) = E.tangentAction B d (X.tangentMap f z) := by
  apply Subtype.ext
  funext a
  exact OrderAction.tangentTestEvaluation_action X E z
    ⟨X.localAlgebra B a, f ≫ X.localizationMap B a, a, X.localUnit B a⟩ d

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

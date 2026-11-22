import Langlands.Geometry.FormalGroup.AtlasTangentModule

/-! # Chart evaluation of the compatible formal tangent module -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {I : Type} [Finite I] (X : BasicAtlas O R I)

/-- Coefficient extension of the derivative follows from that of the formal transition. -/
theorem transitionTangent_natural {A B : CommAlgCat.{v} R} (f : A ⟶ B) (a b : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (ha' : IsUnit (algebraMap R B a.val)) (hb' : IsUnit (algebraMap R B b.val)) (x : I → A) :
    (fun i => f.hom (X.transitionTangent A a b ha hb x i)) =
      X.transitionTangent B a b ha' hb' (fun i => f.hom (x i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let q := (X.transition A a b ha hb).hom.toHom.toCoordinateMap
  let r := (X.transition B a b ha' hb').hom.toHom.toCoordinateMap
  funext i
  change f.hom (q.linearPart x i) = r.linearPart (fun j => f.hom (x j)) i
  have he : q.map f.hom.toRingHom = r := X.transition_natural f a b ha hb ha' hb'
  rw [← he]
  simp only [CoordinateMap.linearPart_apply, CoordinateMap.linearCoeff_map, map_sum, map_mul]
  rfl

variable (A : CommAlgCat.{v} R) (a : X.opens) (ha : IsUnit (algebraMap R A a.val))

private def tangentFromChartFamily : (I → A) →ₗ[A] X.LocalizedTangent A :=
  LinearMap.pi fun b =>
    let C := X.localAlgebra A b
    let h := BasicAtlas.unit_map (X.localizationMap A b) ha
    ((X.transitionTangent C a b h (X.localUnit A b)).toLinearMap.restrictScalars A).comp
      (LinearMap.pi fun i => (Algebra.linearMap A C).comp (LinearMap.proj i))

private theorem tangentFromChartFamily_mem (x : I → A) :
    X.tangentFromChartFamily A a ha x ∈ X.tangentSubmodule A := by
  apply (X.mem_tangentSubmodule A _).mpr
  intro b c
  let C := X.overlapAlgebra A b c
  let f := X.overlapMap A b c
  let l := X.overlapFromLeft A b c
  let r := X.overlapFromRight A b c
  let hb := X.localUnit A b
  let hc := X.localUnit A c
  let hbl := X.overlapUnitLeft A b c
  let hcr := X.overlapUnitRight A b c
  let haz := BasicAtlas.unit_map f ha
  let hab := BasicAtlas.unit_map (X.localizationMap A b) ha
  let hac := BasicAtlas.unit_map (X.localizationMap A c) ha
  let x_b : I → X.localAlgebra A b := fun i => (X.localizationMap A b).hom (x i)
  let x_c : I → X.localAlgebra A c := fun i => (X.localizationMap A c).hom (x i)
  let x_z : I → C := fun i => f.hom (x i)
  change X.transitionTangent C b c hbl hcr
      (fun i => l.hom (X.transitionTangent (X.localAlgebra A b) a b hab hb x_b i)) =
    fun i => r.hom (X.transitionTangent (X.localAlgebra A c) a c hac hc x_c i)
  rw [X.transitionTangent_natural l a b hab hb haz hbl x_b,
    X.transitionTangent_natural r a c hac hc haz hcr x_c]
  have hl : (fun i => l.hom (x_b i)) = x_z :=
    funext fun i => congrArg (fun g : A ⟶ C => g.hom (x i))
      (X.localizationMap_testFactor ⟨C, f, b, hbl⟩)
  have hr : (fun i => r.hom (x_c i)) = x_z :=
    funext fun i => congrArg (fun g : A ⟶ C => g.hom (x i))
      (X.localizationMap_testFactor ⟨C, f, c, hcr⟩)
  rw [hl, hr]
  exact LinearEquiv.congr_fun (X.transitionTangent_cocycle C a b c haz hbl hcr) x_z

/-- A tangent vector in a chart extends to all its actual overlapping chart coordinates. -/
def tangentFromChart : (I → A) →ₗ[A] X.tangentSubmodule A :=
  (X.tangentFromChartFamily A a ha).codRestrict _ (X.tangentFromChartFamily_mem A a ha)

private def tangentChartFactor : X.localAlgebra A a ⟶ A :=
  X.testFactor ⟨A, 𝟙 A, a, ha⟩

private theorem tangentChartFactor_comp : X.localizationMap A a ≫ X.tangentChartFactor A a ha = 𝟙 A :=
  X.localizationMap_testFactor ⟨A, 𝟙 A, a, ha⟩

/-- Evaluate a compatible tangent vector in a chart containing the whole test algebra. -/
def tangentChartEvaluation : X.tangentSubmodule A →ₗ[A] (I → A) where
  toFun z i := (X.tangentChartFactor A a ha).hom (z.val a i)
  map_add' z w := funext fun i => map_add (X.tangentChartFactor A a ha).hom (z.val a i) (w.val a i)
  map_smul' r z := by
    funext i
    let g := X.tangentChartFactor A a ha
    change g.hom (r • z.val a i) = r • g.hom (z.val a i)
    rw [Algebra.smul_def, smul_eq_mul, map_mul]
    exact congrArg (· * g.hom (z.val a i)) (congrArg (fun j : A ⟶ A => j.hom r)
      (X.tangentChartFactor_comp A a ha))

private theorem tangentChartEvaluation_from (x : I → A) :
    X.tangentChartEvaluation A a ha (X.tangentFromChart A a ha x) = x := by
  let h := X.localUnit A a
  let k := X.localizationMap A a
  let g := X.tangentChartFactor A a ha
  let y : I → X.localAlgebra A a := fun i => k.hom (x i)
  change (fun i => g.hom (X.transitionTangent (X.localAlgebra A a) a a h h y i)) = x
  rw [X.transitionTangent_self]
  exact funext fun i => congrArg (fun j : A ⟶ A => j.hom (x i)) (X.tangentChartFactor_comp A a ha)

private theorem tangentFromChart_evaluation (z : X.tangentSubmodule A) :
    X.tangentFromChart A a ha (X.tangentChartEvaluation A a ha z) = z := by
  apply Subtype.ext
  funext b
  let C := X.overlapAlgebra A a b
  let F := X.localAlgebra A b
  let k := X.localizationMap A b
  let g := X.tangentChartFactor A a ha
  let l := X.overlapFromLeft A a b
  let r := X.overlapFromRight A a b
  let hal := X.overlapUnitLeft A a b
  let hbr := X.overlapUnitRight A a b
  let haq := BasicAtlas.unit_map k ha
  let hb := X.localUnit A b
  let m := X.overlapFactor k a b haq hb
  let x_l : I → C := fun i => l.hom (z.val a i)
  let x_r : I → C := fun i => r.hom (z.val b i)
  have hz : X.transitionTangent C a b hal hbr x_l = x_r :=
    (X.mem_tangentSubmodule A z.val).mp z.property a b
  have h := congrArg (fun x : I → C => fun i => m.hom (x i)) hz
  rw [X.transitionTangent_natural m a b hal hbr haq hb x_l] at h
  have hl : l ≫ m = g ≫ k := by
    rw [X.overlapFromLeft_factor]
    have ht := X.testFactor_comp ⟨A, 𝟙 A, a, ha⟩ k haq
    rw [Category.id_comp] at ht
    exact ht.symm
  have hr : r ≫ m = 𝟙 F :=
    (X.overlapFromRight_factor k a b haq hb).trans (X.testFactor_localTest A b)
  have hleft : (fun i => m.hom (x_l i)) = fun i => k.hom (g.hom (z.val a i)) :=
    funext fun i => congrArg (fun j : X.localAlgebra A a ⟶ F => j.hom (z.val a i)) hl
  have hright : (fun i => m.hom (x_r i)) = z.val b :=
    funext fun i => congrArg (fun j : F ⟶ F => j.hom (z.val b i)) hr
  rw [hleft, hright] at h
  exact h

/-- On a test algebra lying in a chart, the compatible tangent module is the coordinate module. -/
def tangentChartEquiv : X.tangentSubmodule A ≃ₗ[A] (I → A) :=
  LinearEquiv.ofLinearMap (X.tangentChartEvaluation A a ha) (X.tangentFromChart A a ha)
    (LinearMap.ext (X.tangentChartEvaluation_from A a ha))
    (LinearMap.ext (X.tangentFromChart_evaluation A a ha))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

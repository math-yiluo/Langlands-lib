import Langlands.GroupScheme.RelativeUnipotent.LinearLiftedModuleDatum
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality

/-! # Local reflection of scalar compatibility for original lifted point charts -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

namespace ModulePointCharts

variable {S : Scheme.{u}} {V : GroupScheme S} {M N : S.Modules}
  (C : ModulePointCharts V M) (D : ModulePointCharts V N)

/-- Scalar multiplication as an operation on the original represented points. -/
def scaledPoint (T : Over S) (r : Γ(T.left, ⊤)) (x : T ⟶ V.X) : T ⟶ V.X :=
  (C.equiv T).symm (Multiplicative.ofAdd (r • (C.equiv T x).toAdd))

lemma scaledPoint_equiv (T : Over S) (r : Γ(T.left, ⊤)) (x : T ⟶ V.X) :
    (C.equiv T (C.scaledPoint T r x)).toAdd = r • (C.equiv T x).toAdd := by
  rw [scaledPoint, MulEquiv.apply_symm_apply]
  rfl

/-- Agreement of the two actual scalar operations gives linearity of the
original point-chart transition. -/
lemma isLinear_of_scaledPoint_eq
    (h : ∀ (T : Over S) (r : Γ(T.left, ⊤)) (x : T ⟶ V.X),
      C.scaledPoint T r x = D.scaledPoint T r x) : C.IsLinear D := by
  intro T r s
  let z := (C.equiv T).symm (Multiplicative.ofAdd s)
  have hz : (C.equiv T z).toAdd = s :=
    congrArg Multiplicative.toAdd ((C.equiv T).apply_symm_apply _)
  have H := congrArg (fun w => (D.equiv T w).toAdd) (h T r z)
  rw [D.scaledPoint_equiv] at H
  change (D.equiv T ((C.equiv T).symm
    (Multiplicative.ofAdd (r • (C.equiv T z).toAdd)))).toAdd =
      r • (D.equiv T z).toAdd at H
  rw [hz] at H
  exact H

end ModulePointCharts

namespace LiftedModuleCharts

open NaturalModuleTransformations

variable {S X : Scheme.{u}} {p : X ⟶ S} {V : GroupScheme S} {F : X.Modules}
  (C : LiftedModuleCharts p V F)

/-- The scalar operation on original group points prescribed by one actual lift. -/
def scaledPoint (T : Over S) (a : T.left ⟶ X) (ha : a ≫ p = T.hom)
    (r : Γ(T.left, ⊤)) (x : T ⟶ V.X) : T ⟶ V.X :=
  (C.equiv T a ha).symm (Multiplicative.ofAdd (r • (C.equiv T a ha x).toAdd))

lemma scaledPoint_equiv (T : Over S) (a : T.left ⟶ X) (ha : a ≫ p = T.hom)
    (r : Γ(T.left, ⊤)) (x : T ⟶ V.X) :
    (C.equiv T a ha (C.scaledPoint T a ha r x)).toAdd =
      r • (C.equiv T a ha x).toAdd := by
  rw [scaledPoint, MulEquiv.apply_symm_apply]
  rfl

/-- Ordinary actual pullback of sections is semilinear for the original map
on global functions. -/
lemma pullbackSection_smul_actual {Y Z : Scheme.{u}} (b : Z ⟶ Y) (M : Y.Modules)
    (r : Γ(Y, ⊤)) (x : GlobalSections M) :
    pullbackSection b M (r • x) = b.appTop r • pullbackSection b M x := by
  simp only [pullbackSection_eq_sectionPullback, LinearMap.map_smulₛₗ]
  rfl

/-- The original scalar operation is natural under arbitrary test maps and
any specified composite lift. -/
lemma scaledPoint_natural_comp (T W : Over S) (b : W ⟶ T)
    (a : T.left ⟶ X) (ha : a ≫ p = T.hom)
    (a' : W.left ⟶ X) (ha' : a' ≫ p = W.hom) (h : b.left ≫ a = a')
    (r : Γ(T.left, ⊤)) (x : T ⟶ V.X) :
    C.scaledPoint W a' ha' (b.left.appTop r) (b ≫ x) =
      b ≫ C.scaledPoint T a ha r x := by
  apply (C.equiv W a' ha').injective
  apply Multiplicative.toAdd.injective
  rw [C.scaledPoint_equiv, C.natural_comp T W b a ha a' ha' h,
    C.natural_comp T W b a ha a' ha' h, C.scaledPoint_equiv,
    pullbackSection_smul_actual, Scheme.Modules.Hom.app_smul]

/-- The canonical module composition comparison is linear on its actual sections. -/
lemma baseChangeSectionEquiv_smul {Y : Scheme.{u}} (a : Y ⟶ X) (T : Over Y)
    (r : Γ(T.left, ⊤))
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj
      ((Scheme.Modules.pullback a).obj F))) :
    baseChangeSectionEquiv a F T (r • x) = r • baseChangeSectionEquiv a F T x :=
  (baseChangeLinearEquiv a F T).map_smul r x

/-- Fixed-lift normalization retains exactly the original scalar operation on points. -/
lemma scaledPoint_atLift {Y : Scheme.{u}} (f : Y ⟶ S)
    (a : Y ⟶ X) (ha : a ≫ p = f) (T : Over Y)
    (r : Γ(T.left, ⊤)) (x : T ⟶ ((GroupScheme.baseChange f).obj V).X) :
    baseChangePointsEquiv f V T ((C.atLift f a ha).scaledPoint T r x) =
      C.scaledPoint ((Over.map f).obj T) (T.hom ≫ a)
        (by rw [Category.assoc, ha]; rfl) r (baseChangePointsEquiv f V T x) := by
  apply (C.equiv ((Over.map f).obj T) (T.hom ≫ a) _).injective
  apply Multiplicative.toAdd.injective
  rw [C.scaledPoint_equiv]
  have H := congrArg (baseChangeSectionEquiv a F T)
    ((C.atLift f a ha).scaledPoint_equiv T r x)
  rw [C.atLift_apply, baseChangeSectionEquiv_smul, C.atLift_apply] at H
  exact H

/-- Independence of the actual scalar operation from the chosen original lift. -/
def ScalarIndependent : Prop :=
  ∀ (T : Over S) (a c : T.left ⟶ X) (ha : a ≫ p = T.hom) (hc : c ≫ p = T.hom)
    (r : Γ(T.left, ⊤)) (x : T ⟶ V.X),
    C.scaledPoint T a ha r x = C.scaledPoint T c hc r x

/-- Independence of the original scalar operation supplies the scalar-linearity
input of actual module-datum reconstruction. -/
lemma hasLinearTransitions_of_scalarIndependent (h : C.ScalarIndependent) :
    C.HasLinearTransitions := by
  intro Y f a c ha hc
  apply ModulePointCharts.isLinear_of_scaledPoint_eq
  intro T r x
  apply (baseChangePointsEquiv f V T).injective
  rw [C.scaledPoint_atLift, C.scaledPoint_atLift]
  exact h ((Over.map f).obj T) (T.hom ≫ a) (T.hom ≫ c) _ _ r
    (baseChangePointsEquiv f V T x)

/-- Equality of the original scalar operations is reflected by any open cover
of an arbitrary scheme test. -/
lemma scaledPoint_eq_of_openCover (T : Over S) (𝒰 : T.left.OpenCover.{u})
    (a c : T.left ⟶ X) (ha : a ≫ p = T.hom) (hc : c ≫ p = T.hom)
    (r : Γ(T.left, ⊤)) (x : T ⟶ V.X)
    (h : ∀ i,
      C.scaledPoint (SubgroupFunctor.coverObj 𝒰 i) (𝒰.f i ≫ a)
          (by rw [Category.assoc, ha]; rfl) ((𝒰.f i).appTop r)
          (SubgroupFunctor.coverMap 𝒰 i ≫ x) =
        C.scaledPoint (SubgroupFunctor.coverObj 𝒰 i) (𝒰.f i ≫ c)
          (by rw [Category.assoc, hc]; rfl) ((𝒰.f i).appTop r)
          (SubgroupFunctor.coverMap 𝒰 i ≫ x)) :
    C.scaledPoint T a ha r x = C.scaledPoint T c hc r x := by
  apply Over.OverMorphism.ext
  apply 𝒰.hom_ext
  intro i
  have H := (C.scaledPoint_natural_comp T _ (SubgroupFunctor.coverMap 𝒰 i) a ha
      (𝒰.f i ≫ a) _ rfl r x).symm.trans ((h i).trans
    (C.scaledPoint_natural_comp T _ (SubgroupFunctor.coverMap 𝒰 i) c hc
      (𝒰.f i ≫ c) _ rfl r x))
  exact congrArg (fun q => q.left) H

/-- The local scalar comparison on literal affine tests whose two lifts each
factor through one prescribed member of the original covering scheme. -/
def SpecComponentIndependent (𝒰 : X.OpenCover.{u}) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S) (a c : Spec A ⟶ X)
    (ha : a ≫ p = f) (hc : c ≫ p = f),
    (∃ i, ∃ b : Spec A ⟶ 𝒰.X i, b ≫ 𝒰.f i = a) →
    (∃ j, ∃ b : Spec A ⟶ 𝒰.X j, b ≫ 𝒰.f j = c) →
    ∀ (r : Γ(Spec A, ⊤)) (x : Over.mk f ⟶ V.X),
      C.scaledPoint (Over.mk f) a ha r x = C.scaledPoint (Over.mk f) c hc r x

/-- Scalar agreement on arbitrary common affine component parameters reflects
to every lift on every scheme test. Empty refinements are allowed. -/
lemma scalarIndependent_of_specComponents (𝒰 : X.OpenCover.{u})
    (h : C.SpecComponentIndependent 𝒰) : C.ScalarIndependent := by
  intro T a c ha hc r x
  let 𝒜 := 𝒰.pullback₁ a
  apply C.scaledPoint_eq_of_openCover T 𝒜 a c ha hc r x
  intro i
  let T1 := SubgroupFunctor.coverObj (T := T) 𝒜 i
  let c1 := 𝒜.f i ≫ c
  let ℬ := 𝒰.pullback₁ c1
  apply C.scaledPoint_eq_of_openCover T1 ℬ
  intro j
  let T2 := SubgroupFunctor.coverObj (T := T1) ℬ j
  apply C.scaledPoint_eq_of_openCover T2 T2.left.affineBasisCover
  intro k
  apply h (T2.left.affineBasisCoverRing k)
  · refine ⟨i, T2.left.affineBasisCover.f k ≫ ℬ.f j ≫
        pullback.snd a (𝒰.f i), ?_⟩
    change (T2.left.affineBasisCover.f k ≫ ℬ.f j ≫
      pullback.snd a (𝒰.f i)) ≫ 𝒰.f i =
        T2.left.affineBasisCover.f k ≫ (ℬ.f j ≫ (𝒜.f i ≫ a))
    simp only [Category.assoc]
    exact congrArg (fun v => T2.left.affineBasisCover.f k ≫ ℬ.f j ≫ v)
      (pullback.condition (f := a) (g := 𝒰.f i)).symm
  · refine ⟨j, T2.left.affineBasisCover.f k ≫
        pullback.snd c1 (𝒰.f j), ?_⟩
    change (T2.left.affineBasisCover.f k ≫ pullback.snd c1 (𝒰.f j)) ≫ 𝒰.f j =
      T2.left.affineBasisCover.f k ≫ (ℬ.f j ≫ c1)
    simp only [Category.assoc]
    exact congrArg (fun v => T2.left.affineBasisCover.f k ≫ v)
      (pullback.condition (f := c1) (g := 𝒰.f j)).symm

end LiftedModuleCharts
end Langlands.GroupScheme.RelativeUnipotent

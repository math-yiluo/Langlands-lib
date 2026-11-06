import Langlands.GroupScheme.HomScheme.TorusSubgroupCharts
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Transport of actual torus-subgroup charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- The exact chart-cover property for one actual group scheme. -/
def HasChartCover (G : GroupScheme S) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (K : ∀ k, GroupScheme (U k).left)
    (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj G),
    (∀ k, IsOpenChart (j k)) ∧ CoversFieldPoints j

/-- Equal all-test ranges stay equal under ambient postcomposition. -/
theorem range_postcomp_congr {K L : GroupScheme S} (i : K ⟶ G) (j : L ⟶ G)
    (p : G ⟶ H) (h : SubgroupFunctor.range i = SubgroupFunctor.range j) :
    SubgroupFunctor.range (i ≫ p) = SubgroupFunctor.range (j ≫ p) := by
  have step {A B : GroupScheme S} (a : A ⟶ G) (b : B ⟶ G)
      (hab : SubgroupFunctor.range a = SubgroupFunctor.range b)
      (T : Over S) (x : T ⟶ H.X)
      (hx : x ∈ (SubgroupFunctor.range (a ≫ p)).carrier T) :
      x ∈ (SubgroupFunctor.range (b ≫ p)).carrier T := by
    obtain ⟨y, hy⟩ := hx
    have hm : y ≫ a.hom.hom ∈ (SubgroupFunctor.range b).carrier T := by
      rw [← hab]
      exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hm
    change y ≫ (a ≫ p).hom.hom = x at hy
    change z ≫ b.hom.hom = y ≫ a.hom.hom at hz
    refine ⟨z, ?_⟩
    change z ≫ (b ≫ p).hom.hom = x
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc,
      ← Grp.comp_hom_hom]
    exact hy
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  exact ⟨step i j h T x, step j i h.symm T x⟩

/-- An ambient isomorphism preserves and reflects equality of all-test ranges. -/
theorem range_postcomp_eq_iff {K L : GroupScheme S} (e : G ≅ H)
    (i : K ⟶ G) (j : L ⟶ G) :
    SubgroupFunctor.range (i ≫ e.hom) = SubgroupFunctor.range (j ≫ e.hom) ↔
      SubgroupFunctor.range i = SubgroupFunctor.range j :=
  SubgroupFunctor.range_comp_iso_eq_iff i j e

/-- Evaluation commutes with ambient postcomposition. -/
theorem familyHom_postcomp {U T : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) (a : T ⟶ U) (p : G ⟶ H) :
    familyHom (j ≫ (baseChange U.hom).map p) a =
      familyHom j a ≫ (baseChange T.hom).map p := by
  simp only [familyHom, Functor.map_comp, Category.assoc]
  rw [Descent.pullbackComparison_naturality]

/-- View a family over a changed base as a family over the original base. -/
def pushFamily (f : S' ⟶ S) {U : Over S'} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G)) :
    K ⟶ (baseChange ((Over.map f).obj U).hom).obj G :=
  j ≫ (Descent.pullbackComparison f U.hom (U.hom ≫ f) rfl G).hom

/-- Pushing a family preserves its closed subgroup inclusion. -/
theorem isClosedSubgroup_pushFamily (f : S' ⟶ S) {U : Over S'}
    {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G))
    (hj : IsClosedSubgroup j) : IsClosedSubgroup (pushFamily f j) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  change IsClosedImmersion (j.hom.hom.left ≫
    (Descent.pullbackComparison f U.hom (U.hom ≫ f) rfl G).hom.hom.hom.left)
  infer_instance

/-- The actual inclusion comparison for a pushed family. -/
theorem familyHom_pushFamily (f : S' ⟶ S) {U T : Over S'}
    {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj ((baseChange f).obj G)) (a : T ⟶ U) :
    familyHom (pushFamily f j) ((Over.map f).map a) =
      familyHom j a ≫
        (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G).hom := by
  have h₁ := familyHom_original (S := S) (G := G)
    (M := (Over.map f).obj U) (T := (Over.map f).obj T) (K := K)
    (pushFamily (G := G) f j) ((Over.map f).map a)
  have h₂ := familyHom_original (S := S') (G := (baseChange f).obj G)
    (M := U) (T := T) (K := K) j a
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (familyHom (pushFamily f j) ((Over.map f).map a)).hom.hom.left ≫
        pullback.fst G.X.hom (T.hom ≫ f) =
      (familyHom j a).hom.hom.left ≫
        (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G).hom.hom.hom.left ≫
          pullback.fst G.X.hom (T.hom ≫ f)
    calc
      _ = pullback.fst K.X.hom a.left ≫ (pushFamily f j).hom.hom.left ≫
          pullback.fst G.X.hom (U.hom ≫ f) :=
        h₁
      _ = pullback.fst K.X.hom a.left ≫ j.hom.hom.left ≫
          pullback.fst ((baseChange f).obj G).X.hom U.hom ≫
            pullback.fst G.X.hom f := by
        simp only [pushFamily, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
          Descent.pullbackComparison_hom_fst]
      _ = (familyHom j a).hom.hom.left ≫
          pullback.fst ((baseChange f).obj G).X.hom T.hom ≫
            pullback.fst G.X.hom f :=
        (congrArg (fun k => k ≫ pullback.fst G.X.hom f) h₂).symm
      _ = _ := by
        rw [Descent.pullbackComparison_hom_fst f T.hom (T.hom ≫ f) rfl G]
  · change (familyHom (pushFamily f j) ((Over.map f).map a)).hom.hom.left ≫
        pullback.snd G.X.hom (T.hom ≫ f) = _
    exact (Over.w (familyHom (S := S) (G := G)
      (M := (Over.map f).obj U) (T := (Over.map f).obj T) (K := K)
      (pushFamily (G := G) f j) ((Over.map f).map a)).hom.hom).trans
      (Over.w (familyHom (S := S') (G := (baseChange f).obj G)
        (M := U) (T := T) (K := K) j a ≫
        (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G).hom).hom.hom).symm

end Langlands.GroupScheme.TorusSubgroupModuli

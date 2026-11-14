import Langlands.GroupScheme.HomScheme.AdmissibleClosedRepresentability
import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Effective descent of compatible closed subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Absolute subgroup membership as a sieve on the ambient scheme. -/
def schemeSieve (F : SubgroupFunctor G) : Sieve G.X.left where
  arrows _ x := F.schemeCondition x
  downward_closed hx a := F.schemeCondition_comp _ a hx

/-- Membership represented by a monomorphism descends along fppf covering sieves. -/
theorem IsRepresentedBy.isClosed_schemeSieve {F : SubgroupFunctor G}
    {H : GroupScheme S} {j : H ⟶ G} (hj : F.IsRepresentedBy j) :
    Scheme.fppfTopology.IsClosed F.schemeSieve := by
  have : Mono j.hom.hom := hj.1
  intro T x hx
  apply (F.schemeCondition_iff_exists_of_isRepresentedBy hj x).mpr
  apply Langlands.AlgebraicGeometry.FppfClosedLocusDescent.exists_lift_of_covering
    Scheme.fppfTopology j.hom.hom.left x (F.schemeSieve.pullback x) hx
  intro T' a ha
  exact (F.schemeCondition_iff_exists_of_isRepresentedBy hj (a ≫ x)).mp ha

variable (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))

/-- Matching under every comparison of relative test schemes. -/
def IsMatchingEtale : Prop :=
  ∀ (i j : 𝒰.I₀) (V : Over (𝒰.X i)) (W : Over (𝒰.X j))
    (a : (Over.map (𝒰.f i)).obj V ⟶ (Over.map (𝒰.f j)).obj W)
    (x : W ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X),
    x ∈ (F j).carrier W →
      (baseChangePointsEquiv (𝒰.f i) G V).symm
        (a ≫ baseChangePointsEquiv (𝒰.f j) G W x) ∈ (F i).carrier V

/-- The subgroup satisfying the local conditions after every restriction. -/
def etaleDescentSubgroup : SubgroupFunctor G where
  carrier T :=
    { carrier := {x | ∀ (i : 𝒰.I₀) (V : Over (𝒰.X i))
          (a : (Over.map (𝒰.f i)).obj V ⟶ T),
        (baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ x) ∈ (F i).carrier V}
      one_mem' := by
        intro i V a
        simpa only [MonObj.comp_one, map_one] using (F i).carrier V |>.one_mem
      mul_mem' := by
        intro x y hx hy i V a
        simpa only [MonObj.comp_mul, map_mul] using
          (F i).carrier V |>.mul_mem (hx i V a) (hy i V a)
      inv_mem' := by
        intro x hx i V a
        simpa only [GrpObj.comp_inv, map_inv] using
          (F i).carrier V |>.inv_mem (hx i V a) }
  comp_mem a x hx := by
    intro i V b
    simpa only [Category.assoc] using hx i V (b ≫ a)

/-- The descended subgroup has the prescribed local base changes. -/
theorem baseChange_etaleDescentSubgroup (hF : IsMatchingEtale 𝒰 F) (i : 𝒰.I₀) :
    (etaleDescentSubgroup 𝒰 F).baseChange (𝒰.f i) = F i := by
  ext V x
  change (∀ (j : 𝒰.I₀) (W : Over (𝒰.X j))
      (a : (Over.map (𝒰.f j)).obj W ⟶ (Over.map (𝒰.f i)).obj V),
    (baseChangePointsEquiv (𝒰.f j) G W).symm
      (a ≫ baseChangePointsEquiv (𝒰.f i) G V x) ∈ (F j).carrier W) ↔ _
  constructor
  · intro hx
    simpa only [Category.id_comp, MulEquiv.symm_apply_apply] using hx i V (𝟙 _)
  · intro hx j W a
    exact hF j i W V a x hx

/-- Absolute membership in the descended group is the universal local condition. -/
theorem schemeCondition_etaleDescentSubgroup_iff {Y : Scheme.{u}}
    (x : Y ⟶ G.X.left) :
    (etaleDescentSubgroup 𝒰 F).schemeCondition x ↔
      ∀ (i : 𝒰.I₀) (Z : Scheme.{u}) (a : Z ⟶ Y)
        (z : Z ⟶ ((GroupScheme.baseChange (𝒰.f i)).obj G).X.left),
        z ≫ pullback.fst G.X.hom (𝒰.f i) = a ≫ x →
          (F i).schemeCondition z := by
  let T : Over S := Over.mk (x ≫ G.X.hom)
  let p : T ⟶ G.X := Over.homMk x rfl
  change p ∈ (etaleDescentSubgroup 𝒰 F).carrier T ↔ _
  constructor
  · intro hx i Z a z hz
    let V : Over (𝒰.X i) := Over.mk (z ≫ pullback.snd G.X.hom (𝒰.f i))
    let q : V ⟶ ((GroupScheme.baseChange (𝒰.f i)).obj G).X := Over.homMk z rfl
    let b : (Over.map (𝒰.f i)).obj V ⟶ T := Over.homMk a (by
      change a ≫ (x ≫ G.X.hom) =
        (z ≫ pullback.snd G.X.hom (𝒰.f i)) ≫ 𝒰.f i
      rw [← Category.assoc, ← hz, Category.assoc, pullback.condition, ← Category.assoc])
    have hq : (baseChangePointsEquiv (𝒰.f i) G V).symm (b ≫ p) = q := by
      apply (baseChangePointsEquiv (𝒰.f i) G V).injective
      rw [MulEquiv.apply_symm_apply]
      apply Over.OverMorphism.ext
      exact hz.symm
    exact ((F i).schemeCondition_iff_mem q).mpr (hq ▸ hx i V b)
  · intro hx i V a
    let q := (baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ p)
    have hq : q.left ≫ pullback.fst G.X.hom (𝒰.f i) = a.left ≫ x := by
      exact congrArg CommaMorphism.left
        ((baseChangePointsEquiv (𝒰.f i) G V).apply_symm_apply (a ≫ p))
    exact ((F i).schemeCondition_iff_mem q).mp (hx i V.left a.left q.left hq)

/-- Fppf locality of the local subgroup conditions gives fppf locality globally. -/
theorem isClosed_schemeSieve_etaleDescentSubgroup
    (hF : ∀ i, Scheme.fppfTopology.IsClosed (F i).schemeSieve) :
    Scheme.fppfTopology.IsClosed (etaleDescentSubgroup 𝒰 F).schemeSieve := by
  intro Y x hx
  apply (schemeCondition_etaleDescentSubgroup_iff 𝒰 F x).mpr
  intro i Z a z hz
  apply hF i z
  apply Scheme.fppfTopology.superset_covering ?_
    (Scheme.fppfTopology.pullback_stable a hx)
  intro W b hb
  change (F i).schemeCondition (b ≫ z)
  have hb' : (etaleDescentSubgroup 𝒰 F).schemeCondition ((b ≫ a) ≫ x) := hb
  apply (schemeCondition_etaleDescentSubgroup_iff 𝒰 F _).mp hb'
    i W (𝟙 W) (b ≫ z)
  simp only [Category.assoc, hz, Category.id_comp]

/-- Compatible étale-local closed subgroups have an actual closed subgroup
representative over the original arbitrary base. -/
theorem isClosedRepresentable_etaleDescentSubgroup
    (hF : IsMatchingEtale 𝒰 F) (h : ∀ i, (F i).IsClosedRepresentable) :
    (etaleDescentSubgroup 𝒰 F).IsClosedRepresentable := by
  choose H j hjr hjc using h
  let D := etaleDescentSubgroup 𝒰 F
  have hD : Scheme.fppfTopology.IsClosed D.schemeSieve :=
    isClosed_schemeSieve_etaleDescentSubgroup 𝒰 F
      (fun i => (hjr i).isClosed_schemeSieve)
  let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) G.X.left :=
    𝒰.pullback₁ G.X.hom
  have hcover : Sieve.generate (Presieve.ofArrows 𝒱.X 𝒱.f) ∈
      Scheme.fppfTopology G.X.left := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ⟨𝒱.idx x, 𝒱.covers x⟩, fun i => ?_⟩
    have : Etale (𝒱.f i) := 𝒱.map_prop i
    exact ⟨inferInstance, inferInstance⟩
  have hchart (i : 𝒰.I₀) {Y : Scheme.{u}}
      (z : Y ⟶ ((GroupScheme.baseChange (𝒰.f i)).obj G).X.left) :
      D.schemeCondition (z ≫ pullback.fst G.X.hom (𝒰.f i)) ↔
        ∃ a : Y ⟶ (H i).X.left, a ≫ (j i).hom.hom.left = z := by
    rw [schemeCondition_baseChange_iff]
    change ((etaleDescentSubgroup 𝒰 F).baseChange (𝒰.f i)).schemeCondition z ↔ _
    rw [baseChange_etaleDescentSubgroup 𝒰 F hF i]
    exact (F i).schemeCondition_iff_exists_of_isRepresentedBy (hjr i) z
  have hloc : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ G.X.left),
      Sieve.generate (Presieve.ofArrows 𝒱.X 𝒱.f) f →
      ∃ (Z : Scheme.{u}) (c : Z ⟶ Y), IsClosedImmersion c ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y),
          (∃ k : T ⟶ Z, k ≫ c = g) ↔ D.schemeCondition (g ≫ f) := by
    intro Y f hf
    obtain ⟨_, m, _, ⟨i⟩, hm⟩ := hf
    have : IsClosedImmersion (j i).hom.hom.left := hjc i
    refine ⟨pullback (j i).hom.hom.left m,
      pullback.snd (j i).hom.hom.left m, inferInstance, ?_⟩
    intro T g
    change (∃ k, k ≫ pullback.snd (j i).hom.hom.left m = g) ↔
      D.schemeCondition (g ≫ f)
    rw [← hm, ← Category.assoc]
    change (∃ k, k ≫ pullback.snd (j i).hom.hom.left m = g) ↔
      D.schemeCondition ((g ≫ m) ≫ pullback.fst G.X.hom (𝒰.f i))
    rw [hchart i]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k ≫ pullback.fst (j i).hom.hom.left m, by
        rw [Category.assoc, pullback.condition, ← Category.assoc]⟩
    · rintro ⟨a, ha⟩
      exact ⟨pullback.lift a g ha, pullback.lift_snd _ _ _⟩
  obtain ⟨Z, c, hc, hfac⟩ :=
    Langlands.AlgebraicGeometry.fppfClosedLocusDescent G.X.left D.schemeSieve hD
      ⟨_, hcover, hloc⟩
  have : IsClosedImmersion c := hc
  apply D.isClosedRepresentable_of_schemeCondition c
  exact fun Y x => (hfac x).symm

end Langlands.GroupScheme.SubgroupFunctor

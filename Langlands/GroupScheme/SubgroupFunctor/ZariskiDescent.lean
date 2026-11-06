import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality

/-! # Descent of local subgroups of the actual point functor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Membership is detected on open covers of every actual test scheme. -/
def IsZariskiLocal (F : SubgroupFunctor G) : Prop :=
  ∀ (T : Over S) (𝒱 : Scheme.OpenCover.{u} T.left) (x : T ⟶ G.X),
    x ∈ F.carrier T ↔ ∀ k, coverMap 𝒱 k ≫ x ∈ F.carrier (coverObj 𝒱 k)

/-- A monomorphically represented subgroup is Zariski local. -/
theorem IsRepresentedBy.isZariskiLocal {F : SubgroupFunctor G}
    {H : GroupScheme S} {j : H ⟶ G} (hj : F.IsRepresentedBy j) :
    IsZariskiLocal F := by
  let : Mono j.hom.hom := hj.1
  rw [← hj.2]
  exact fun T 𝒱 x => mem_range_iff_openCover j 𝒱 x

variable (𝒰 : Scheme.OpenCover.{u} S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))

/-- Local subgroup conditions agree under every comparison of relative tests.
This is the all-test matching condition, expressed by the pullback point
adjunction rather than a choice of iterated pullback identifications. -/
def IsMatching : Prop :=
  ∀ (i j : 𝒰.I₀) (V : Over (𝒰.X i)) (W : Over (𝒰.X j))
    (a : (Over.map (𝒰.f i)).obj V ⟶ (Over.map (𝒰.f j)).obj W)
    (x : W ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X),
    x ∈ (F j).carrier W →
      (baseChangePointsEquiv (𝒰.f i) G V).symm
        (a ≫ baseChangePointsEquiv (𝒰.f j) G W x) ∈ (F i).carrier V

/-- A point is in the descended subgroup when it satisfies every local
subgroup condition after every restriction to a member of the base cover. -/
def descentSubgroup : SubgroupFunctor G where
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

/-- The descended condition restricts to each matching local subgroup. -/
theorem baseChange_descentSubgroup (hF : IsMatching 𝒰 F) (i : 𝒰.I₀) :
    (descentSubgroup 𝒰 F).baseChange (𝒰.f i) = F i := by
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

/-- Descent of Zariski-local subgroup conditions is itself Zariski local. -/
theorem isZariskiLocal_descentSubgroup (hF : ∀ i, IsZariskiLocal (F i)) :
    IsZariskiLocal (descentSubgroup 𝒰 F) := by
  intro T 𝒱 x
  constructor
  · intro hx k
    exact (descentSubgroup 𝒰 F).comp_mem (coverMap 𝒱 k) hx
  · intro hx i V a
    let 𝒲 := 𝒱.pullback₁ a.left
    let y := (baseChangePointsEquiv (𝒰.f i) G V).symm (a ≫ x)
    apply (hF i V 𝒲 y).mpr
    intro k
    let W : Over (𝒰.X i) := Over.mk (pullback.fst a.left (𝒱.f k) ≫ V.hom)
    let p : W ⟶ V := Over.homMk (pullback.fst a.left (𝒱.f k)) rfl
    let b : (Over.map (𝒰.f i)).obj W ⟶ coverObj 𝒱 k :=
      Over.homMk (pullback.snd a.left (𝒱.f k)) (by
        change pullback.snd a.left (𝒱.f k) ≫ (𝒱.f k ≫ T.hom) =
          (pullback.fst a.left (𝒱.f k) ≫ V.hom) ≫ 𝒰.f i
        rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w a]
        rfl)
    have hb : (Over.map (𝒰.f i)).map p ≫ a = b ≫ coverMap 𝒱 k := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have hk := hx k i W b
    have hy : p ≫ y = (baseChangePointsEquiv (𝒰.f i) G W).symm
        (b ≫ (coverMap 𝒱 k ≫ x)) := by
      apply (baseChangePointsEquiv (𝒰.f i) G W).injective
      simp only [y, baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]
      rw [← Category.assoc, hb, Category.assoc]
    change p ≫ y ∈ (F i).carrier W
    rw [hy]
    exact hk

end Langlands.GroupScheme.SubgroupFunctor

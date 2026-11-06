import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Gluing

/-! # Zariski locality of represented subgroup membership -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H K : GroupScheme S}

/-- A member of a cover of a relative test scheme, regarded over the original
base. -/
abbrev coverObj {T : Over S} (𝒰 : Scheme.OpenCover.{v} T.left) (k : 𝒰.I₀) :
    Over S :=
  Over.mk (𝒰.f k ≫ T.hom)

/-- The relative inclusion of a member of a test scheme's open cover. -/
def coverMap {T : Over S} (𝒰 : Scheme.OpenCover.{v} T.left) (k : 𝒰.I₀) :
    coverObj 𝒰 k ⟶ T :=
  Over.homMk (𝒰.f k) rfl

/-- A point factors through a monomorphic group-scheme inclusion if it does
so on every member of an arbitrary open cover of the test scheme. -/
theorem mem_range_iff_openCover (i : H ⟶ G) [Mono i.hom.hom]
    {T : Over S} (𝒰 : Scheme.OpenCover.{v} T.left) (x : T ⟶ G.X) :
    x ∈ (range i).carrier T ↔
      ∀ k : 𝒰.I₀, coverMap 𝒰 k ≫ x ∈ (range i).carrier (coverObj 𝒰 k) := by
  constructor
  · intro hx k
    exact (range i).comp_mem (coverMap 𝒰 k) hx
  · intro hx
    choose y hy using fun k => mem_range.mp (hx k)
    have hy' (k : 𝒰.I₀) :
        (y k).left ≫ i.hom.hom.left = 𝒰.f k ≫ x.left :=
      congrArg (fun f => f.left) (hy k)
    have hc (k l : 𝒰.I₀) :
        pullback.fst (𝒰.f k) (𝒰.f l) ≫ (y k).left =
          pullback.snd (𝒰.f k) (𝒰.f l) ≫ (y l).left := by
      apply (cancel_mono i.hom.hom.left).mp
      simp only [Category.assoc, hy']
      exact pullback.condition_assoc (f := 𝒰.f k) (g := 𝒰.f l) x.left
    let d := 𝒰.glueMorphisms (fun k => (y k).left) hc
    have hd (k : 𝒰.I₀) : 𝒰.f k ≫ d = (y k).left :=
      𝒰.ι_glueMorphisms _ hc k
    have hw : d ≫ H.X.hom = T.hom := by
      apply 𝒰.hom_ext
      intro k
      rw [← Category.assoc, hd]
      exact Over.w (y k)
    refine mem_range.mpr ⟨Over.homMk d hw, ?_⟩
    apply Over.OverMorphism.ext
    apply 𝒰.hom_ext
    intro k
    change 𝒰.f k ≫ (d ≫ i.hom.hom.left) = 𝒰.f k ≫ x.left
    rw [← Category.assoc, hd, hy']

/-- Containment in a monomorphically represented subgroup can be checked on
an arbitrary Zariski cover of the base. -/
theorem le_range_iff_baseChange_openCover (𝒰 : Scheme.OpenCover.{v} S)
    {F : SubgroupFunctor G} (i : H ⟶ G) [Mono i.hom.hom] :
    F ≤ range i ↔
      ∀ k : 𝒰.I₀, F.baseChange (𝒰.f k) ≤ (range i).baseChange (𝒰.f k) := by
  constructor
  · intro h k U x hx
    exact h _ hx
  · intro h U x hx
    apply (mem_range_iff_openCover i (𝒰.pullback₁ U.hom) x).mpr
    intro k
    let V : Over (𝒰.X k) := Over.mk (pullback.snd U.hom (𝒰.f k))
    let q : (Over.map (𝒰.f k)).obj V ⟶ U :=
      Over.homMk (pullback.fst U.hom (𝒰.f k)) pullback.condition
    let x' := (baseChangePointsEquiv (𝒰.f k) G V).symm (q ≫ x)
    have hx' : x' ∈ (F.baseChange (𝒰.f k)).carrier V := by
      rw [mem_baseChange]
      change baseChangePointsEquiv (𝒰.f k) G V
        ((baseChangePointsEquiv (𝒰.f k) G V).symm (q ≫ x)) ∈ F.carrier _
      rw [MulEquiv.apply_symm_apply]
      exact F.comp_mem q hx
    have hi := h k V hx'
    rw [mem_baseChange] at hi
    have hi' : q ≫ x ∈ (range i).carrier ((Over.map (𝒰.f k)).obj V) := by
      simpa only [x', MulEquiv.apply_symm_apply] using hi
    let r : coverObj (𝒰.pullback₁ U.hom) k ⟶ (Over.map (𝒰.f k)).obj V :=
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (pullback.snd U.hom (𝒰.f k) ≫ 𝒰.f k) =
          pullback.fst U.hom (𝒰.f k) ≫ U.hom
        simpa only [Category.id_comp] using
          (pullback.condition (f := U.hom) (g := 𝒰.f k)).symm)
    have hr : r ≫ q = coverMap (𝒰.pullback₁ U.hom) k := by
      apply Over.OverMorphism.ext
      exact Category.id_comp _
    simpa only [← Category.assoc, hr] using (range i).comp_mem r hi'

/-- Equality of two monomorphically represented subgroup functors is
Zariski local on the base, without any finiteness assumption on the cover. -/
theorem range_eq_iff_baseChange_openCover (𝒰 : Scheme.OpenCover.{v} S)
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom] :
    range i = range j ↔
      ∀ k : 𝒰.I₀, (range i).baseChange (𝒰.f k) =
        (range j).baseChange (𝒰.f k) := by
  constructor
  · intro h k
    rw [h]
  · intro h
    apply le_antisymm
    · exact (le_range_iff_baseChange_openCover 𝒰 j).mpr fun k => (h k).le
    · exact (le_range_iff_baseChange_openCover 𝒰 i).mpr fun k => (h k).ge

/-- The same equality criterion for explicit representatives of subgroup
functors. -/
theorem eq_iff_isRepresentedBy_baseChange_openCover
    (𝒰 : Scheme.OpenCover.{v} S) {F F' : SubgroupFunctor G}
    {i : H ⟶ G} {j : K ⟶ G} (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j) :
    F = F' ↔ ∀ k : 𝒰.I₀, F.baseChange (𝒰.f k) = F'.baseChange (𝒰.f k) := by
  let : Mono i.hom.hom := hi.1
  let : Mono j.hom.hom := hj.1
  rw [← hi.2, ← hj.2]
  exact range_eq_iff_baseChange_openCover 𝒰 i j

end Langlands.GroupScheme.SubgroupFunctor

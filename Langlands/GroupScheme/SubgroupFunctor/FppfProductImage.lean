import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Actual fppf images of represented subgroup products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G Q : GroupScheme B}

/-- A point lifts to a source subgroup after one actual fppf relative cover. -/
def FppfLocallyInImage (F : SubgroupFunctor G) (q : G ⟶ Q)
    {T : Over B} (x : T ⟶ Q.X) : Prop :=
  ∃ (V : Over B) (v : V ⟶ T),
    Flat v.left ∧ Surjective v.left ∧ LocallyOfFinitePresentation v.left ∧
      ∃ y : V ⟶ G.X, y ∈ F.carrier V ∧ v ≫ x = y ≫ q.hom.hom

namespace IsFppfImage

variable {F : SubgroupFunctor G} {E : SubgroupFunctor Q} {q : G ⟶ Q}

/-- The actual fppf image predicate supplies fppf local lifts of every point
on every relative test scheme. -/
theorem fppfLocallyInImage_of_mem (h : IsFppfImage F E q)
    {T : Over B} {x : T ⟶ Q.X} (hx : x ∈ E.carrier T) :
    FppfLocallyInImage F q x := by
  obtain ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩ := h
  let : Flat p.hom.hom.left := hpf
  let : Surjective p.hom.hom.left := hps
  let : LocallyOfFinitePresentation p.hom.hom.left := hpl
  rw [← hj.2] at hx
  obtain ⟨y, hy⟩ := mem_range.mp hx
  let V : Over B := Over.mk (pullback.fst y.left p.hom.hom.left ≫ T.hom)
  let a : V ⟶ T := Over.homMk (pullback.fst y.left p.hom.hom.left) rfl
  let z : V ⟶ H.X := Over.homMk (pullback.snd y.left p.hom.hom.left) (by
    rw [← Over.w p.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  have haz : a ≫ y = z ≫ p.hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have haf : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have has : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have hal : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  refine ⟨V, a, haf, has, hal, z ≫ i.hom.hom, ?_, ?_⟩
  · rw [← hi.2]
    exact mem_range.mpr ⟨z, rfl⟩
  · rw [← hy, ← Category.assoc, haz, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hp]

/-- Local liftability into the source subgroup characterizes membership in
its actual fppf image. -/
theorem mem_iff_fppfLocallyInImage (h : IsFppfImage F E q)
    {T : Over B} (x : T ⟶ Q.X) :
    x ∈ E.carrier T ↔ FppfLocallyInImage F q x := by
  constructor
  · exact h.fppfLocallyInImage_of_mem
  · rintro ⟨V, v, hf, hs, hl, y, hy, he⟩
    obtain ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩ := h
    let : Mono j.hom.hom := hj.1
    have hmap : F.map q ≤ E := (show IsFppfImage F E q from
      ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩).map_le
    rw [← hj.2]
    apply isFppfLocal_range j T V v hf hs hl x
    rw [hj.2, he]
    exact hmap V ⟨y, hy, rfl⟩

/-- The actual fppf image lies in any fppf-local target subgroup that contains
the ordinary image of the source subgroup. -/
theorem le_of_map_le (h : IsFppfImage F E q) {A : SubgroupFunctor Q}
    (hA : A.IsFppfLocal) (hmap : F.map q ≤ A) : E ≤ A := by
  intro T x hx
  obtain ⟨V, v, hf, hs, hl, y, hy, he⟩ := h.fppfLocallyInImage_of_mem hx
  apply hA T V v hf hs hl x
  rw [he]
  exact hmap V ⟨y, hy, rfl⟩

end IsFppfImage

namespace IsFppfProduct

variable {F N : SubgroupFunctor G} {E M : SubgroupFunctor Q}
    {P R : GroupScheme B} {i : P ⟶ G} {j : R ⟶ Q} {q : G ⟶ Q}

/-- If the two factors and their represented product have actual fppf images,
the image of the product represents the fppf-local product of the images. -/
theorem of_fppfImages (hprod : IsFppfProduct F N i)
    (hF : IsFppfImage F E q) (hN : IsFppfImage N M q)
    (hP : IsFppfImage (range i) (range j) q) (hj : IsClosedSubgroup j) :
    IsFppfProduct E M j := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  refine ⟨hj, fun T x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨V, v, hvf, hvs, hvl, y, hy, he⟩ := hP.fppfLocallyInImage_of_mem hx
    obtain ⟨W, w, hwf, hws, hwl, a, b, ha, hb, hab⟩ :=
      (hprod.mem_range_iff V y).mp hy
    let : Flat v.left := hvf
    let : Surjective v.left := hvs
    let : LocallyOfFinitePresentation v.left := hvl
    let : Flat w.left := hwf
    let : Surjective w.left := hws
    let : LocallyOfFinitePresentation w.left := hwl
    have hcf : Flat (w ≫ v).left := by change Flat (w.left ≫ v.left); infer_instance
    have hcs : Surjective (w ≫ v).left := by
      change Surjective (w.left ≫ v.left)
      infer_instance
    have hcl : LocallyOfFinitePresentation (w ≫ v).left := by
      change LocallyOfFinitePresentation (w.left ≫ v.left)
      infer_instance
    refine ⟨W, w ≫ v, hcf, hcs, hcl, a ≫ q.hom.hom, b ≫ q.hom.hom,
      hF.map_le W ⟨a, ha, rfl⟩, hN.map_le W ⟨b, hb, rfl⟩, ?_⟩
    rw [Category.assoc, he, ← Category.assoc, hab, MonObj.mul_comp]
  · intro hx
    apply hx.mem_range_of_le j
    · apply hF.le_of_map_le (isFppfLocal_range j)
      rintro T x ⟨y, hy, rfl⟩
      exact hP.map_le T ⟨y, hprod.left_le T hy, rfl⟩
    · apply hN.le_of_map_le (isFppfLocal_range j)
      rintro T x ⟨y, hy, rfl⟩
      exact hP.map_le T ⟨y, hprod.right_le T hy, rfl⟩

end IsFppfProduct

end Langlands.GroupScheme.SubgroupFunctor

import Langlands.GroupScheme.Torus.SplitSolvableProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Pulling back and joining represented split-solvable series -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupPreimage

variable {S : Scheme.{u}} {N G Q H V : GroupScheme S}
    (q : G ⟶ Q) (j : H ⟶ Q)

/-- A homomorphism killed by `q` maps to the inverse image of any subgroup of `Q`. -/
def kernelInclusion (i : N ⟶ G) (h : i ≫ q = 0) :
    N ⟶ groupScheme q j :=
  pullback.lift i 0 (by simpa using h)

@[reassoc (attr := simp)]
theorem kernelInclusion_comp_inclusion (i : N ⟶ G) (h : i ≫ q = 0) :
    kernelInclusion q j i h ≫ inclusion q j = i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem kernelInclusion_comp_projection (i : N ⟶ G) (h : i ≫ q = 0) :
    kernelInclusion q j i h ≫ projection q j = 0 :=
  pullback.lift_snd _ _ _

/-- A monomorphic kernel representative stays monomorphic in the inverse image. -/
theorem kernelInclusion_mono (i : N ⟶ G) (h : i ≫ q = 0)
    [Mono i.hom.hom] : Mono (kernelInclusion q j i h).hom.hom := by
  have he : (kernelInclusion q j i h).hom.hom ≫ (inclusion q j).hom.hom =
      i.hom.hom := by
    change (kernelInclusion q j i h ≫ inclusion q j).hom.hom = _
    rw [kernelInclusion_comp_inclusion]
  have : Mono ((kernelInclusion q j i h).hom.hom ≫ (inclusion q j).hom.hom) := by
    rw [he]
    infer_instance
  exact mono_of_mono (kernelInclusion q j i h).hom.hom (inclusion q j).hom.hom

/-- The fppf kernel condition is preserved by the actual inverse-image square. -/
theorem isFppfQuotient_projection (i : N ⟶ G) (h : i ≫ q = 0)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelInclusion q j i h)) (projection q j) := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  refine ⟨flat_projection q j, surjective_projection q j,
    MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance, ?_⟩
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_range]
  constructor
  · intro hx
    have hxq : (x ≫ (inclusion q j).hom.hom) ≫ q.hom.hom = 1 := by
      rw [Category.assoc, (isPullback q j).w, ← Category.assoc, hx]
      exact MonObj.one_comp _
    have hxi : x ≫ (inclusion q j).hom.hom ∈
        (SubgroupFunctor.range i).carrier T := by
      rw [← hq.2.2.2, mem_range_kernelι_iff]
      exact hxq
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxi
    refine ⟨y, (isPullback q j).hom_ext ?_ ?_⟩
    · rw [Category.assoc]
      change y ≫ (kernelInclusion q j i h ≫ inclusion q j).hom.hom = _
      rw [kernelInclusion_comp_inclusion]
      exact hy
    · rw [hx]
      rw [Category.assoc]
      change y ≫ (kernelInclusion q j i h ≫ projection q j).hom.hom = 1
      rw [kernelInclusion_comp_projection]
      exact MonObj.comp_one _
  · rintro ⟨y, rfl⟩
    rw [Category.assoc]
    change y ≫ (kernelInclusion q j i h ≫ projection q j).hom.hom = 1
    rw [kernelInclusion_comp_projection]
    exact MonObj.comp_one _

/-- Composing two specified fppf quotients has as kernel the actual inverse image
of the second specified kernel, on every scheme test. -/
theorem isFppfQuotient_comp (i : N ⟶ G) (r : Q ⟶ V)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) r) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (inclusion q j)) (q ≫ r) := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let : Flat r.hom.hom.left := hr.1
  let : Surjective r.hom.hom.left := hr.2.1
  let : LocallyOfFinitePresentation r.hom.hom.left := hr.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (q.hom.hom.left ≫ r.hom.hom.left)
    infer_instance
  · change Surjective (q.hom.hom.left ≫ r.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation (q.hom.hom.left ≫ r.hom.hom.left)
    infer_instance
  · rw [range_inclusion]
    ext T x
    rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap, ← hr.2.2.2,
      mem_range_kernelι_iff]
    change x ≫ (q.hom.hom ≫ r.hom.hom) = 1 ↔
      (x ≫ q.hom.hom) ≫ r.hom.hom = 1
    rw [Category.assoc]

/-- A smooth, geometrically connected quotient has connected inverse images of
connected subgroups. -/
theorem connectedSpace_of_geometricallyConnected
    [Smooth q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    [ConnectedSpace H.X.left] : ConnectedSpace (groupScheme q j).X.left := by
  let : Smooth (projection q j).hom.hom.left := smooth_projection q j
  let : GeometricallyConnected (projection q j).hom.hom.left :=
    MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance
  exact GeometricallyConnected.connectedSpace
    (f := (projection q j).hom.hom.left) (projection q j).hom.hom.left.isOpenMap

end SubgroupPreimage

namespace SplitSolvable

variable {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    {i : N ⟶ G} {q : G ⟶ Q}

/-- A representative of a specified fppf kernel is killed by the quotient map. -/
theorem kernel_comp_eq_zero
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    i ≫ q = 0 := by
  apply (Grp.forget _).map_injective
  change i.hom.hom ≫ q.hom.hom = 1
  apply (mem_range_kernelι_iff q i.hom.hom).mp
  rw [hq.2.2.2, SubgroupFunctor.mem_range]
  exact ⟨𝟙 _, Category.id_comp _⟩

/-- Join a represented kernel series to a quotient series by taking actual
inverse images. Smoothness and geometric connectedness refer to the quotient
map, and are retained explicitly here. -/
theorem HasSeries.of_extension {n m : ℕ}
    [Mono i.hom.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    [Smooth q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    (hN : HasSeries n N) (hQ : HasSeries m Q) :
    HasSeries (n + m) G := by
  induction m generalizing G Q with
  | zero =>
    have hrange : SubgroupFunctor.range (𝟙 G) = SubgroupFunctor.range i := by
      ext T x
      constructor
      · intro _
        rw [← hq.2.2.2, mem_range_kernelι_iff]
        have hx : x ≫ q.hom.hom ∈ (SubgroupFunctor.range (𝟙 Q)).carrier T :=
          SubgroupFunctor.mem_range.mpr ⟨x ≫ q.hom.hom, Category.comp_id _⟩
        rw [hQ, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
        exact hx
      · intro _
        exact SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id _⟩
    let hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
    let hid : (SubgroupFunctor.range i).IsRepresentedBy (𝟙 G) :=
      ⟨inferInstance, hrange⟩
    exact hN.of_iso (hi.isoOfIsRepresentedBy hid)
  | succ m ih =>
    obtain ⟨H, V, j, r, hj, hs, hc, hn, hr, hV, hH⟩ := hQ
    let P := SubgroupPreimage.groupScheme q j
    let p := SubgroupPreimage.projection q j
    let a := SubgroupPreimage.kernelInclusion q j i (kernel_comp_eq_zero hq)
    let : Mono a.hom.hom :=
      SubgroupPreimage.kernelInclusion_mono q j i (kernel_comp_eq_zero hq)
    let : Smooth H.X.hom := hs
    let : ConnectedSpace H.X.left := hc
    let : Smooth p.hom.hom.left := SubgroupPreimage.smooth_projection q j
    let : GeometricallyConnected p.hom.hom.left :=
      MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j) inferInstance
    have hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range a) p :=
      SubgroupPreimage.isFppfQuotient_projection q j i (kernel_comp_eq_zero hq) hq
    exact HasSeries.succ (SubgroupPreimage.inclusion q j) (q ≫ r)
      (SubgroupPreimage.isClosedSubgroup q j hj) (SubgroupPreimage.smooth q j)
      (SubgroupPreimage.connectedSpace_of_geometricallyConnected q j)
      (SubgroupPreimage.isNormal q j hn)
      (SubgroupPreimage.isFppfQuotient_comp q j i r hq hr) hV
      (ih hp hH)

end SplitSolvable

end Langlands.GroupScheme

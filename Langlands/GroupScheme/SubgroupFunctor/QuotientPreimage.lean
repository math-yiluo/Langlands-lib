import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Exact subgroup inverse images in fpqc quotient squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {B G BQ Q : GroupScheme S}
    (i : B ⟶ G) [Mono i.hom.hom] (q : G ⟶ Q)
    (qB : B ⟶ BQ) (iQ : BQ ⟶ Q)
    [Flat qB.hom.hom.left] [Surjective qB.hom.hom.left]
    [QuasiCompact qB.hom.hom.left]
    (hsquare : i ≫ q = qB ≫ iQ)
    (hkernel : range (kernelι q) ≤ range i)

include hsquare hkernel in
/-- In a commuting square, an fpqc quotient of the subgroup and containment
of the ambient kernel give the exact inverse image on every test scheme. -/
theorem comap_range_eq_of_fpqc_square :
    (range iQ).comap q = range i := by
  apply le_antisymm
  · intro T x hx
    change x ≫ q.hom.hom ∈ (range iQ).carrier T at hx
    obtain ⟨y, hy⟩ := mem_range.mp hx
    let V : Over S :=
      Over.mk (pullback.fst y.left qB.hom.hom.left ≫ T.hom)
    let p : V ⟶ T :=
      Over.homMk (pullback.fst y.left qB.hom.hom.left) rfl
    let b : V ⟶ B.X :=
      Over.homMk (pullback.snd y.left qB.hom.hom.left) (by
        rw [← Over.w qB.hom.hom, ← Category.assoc, ← pullback.condition,
          Category.assoc, Over.w y]
        rfl)
    have hp : p ≫ y = b ≫ qB.hom.hom :=
      Over.OverMorphism.ext pullback.condition
    have : EffectiveEpi p.left := by
      change EffectiveEpi (pullback.fst y.left qB.hom.hom.left)
      infer_instance
    apply mem_range_of_comp_mem_range i p
    have he : (p ≫ x) ≫ q.hom.hom =
        (b ≫ i.hom.hom) ≫ q.hom.hom := by
      have hs : i.hom.hom ≫ q.hom.hom =
          qB.hom.hom ≫ iQ.hom.hom :=
        congrArg (fun f => f.hom.hom) hsquare
      calc
        _ = p ≫ (y ≫ iQ.hom.hom) := by rw [Category.assoc, hy]
        _ = (b ≫ qB.hom.hom) ≫ iQ.hom.hom := by
          rw [← Category.assoc, hp]
        _ = _ := by rw [Category.assoc, ← hs, ← Category.assoc]
    have hd : (p ≫ x)⁻¹ * (b ≫ i.hom.hom) ∈ (range i).carrier V := by
      apply hkernel V
      rw [mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, he,
        inv_mul_cancel]
    have hb : b ≫ i.hom.hom ∈ (range i).carrier V :=
      mem_range.mpr ⟨b, rfl⟩
    have hinv := ((range i).carrier V).mul_mem hd
      (((range i).carrier V).inv_mem hb)
    have hxinv : (p ≫ x)⁻¹ ∈ (range i).carrier V := by
      simpa only [mul_inv_cancel_right] using hinv
    simpa only [inv_inv] using ((range i).carrier V).inv_mem hxinv
  · intro T x hx
    obtain ⟨b, rfl⟩ := mem_range.mp hx
    change (b ≫ i.hom.hom) ≫ q.hom.hom ∈ (range iQ).carrier T
    apply mem_range.mpr
    refine ⟨b ≫ qB.hom.hom, ?_⟩
    have hs : i.hom.hom ≫ q.hom.hom =
        qB.hom.hom ≫ iQ.hom.hom :=
      congrArg (fun f => f.hom.hom) hsquare
    rw [Category.assoc, ← hs, ← Category.assoc]

/-- The actual subgroup point above any point whose quotient image belongs
to the quotient subgroup. -/
def quotientPreimagePoint {T : Over S} (x : T ⟶ G.X)
    (hx : x ≫ q.hom.hom ∈ (range iQ).carrier T) : T ⟶ B.X :=
  Classical.choose (mem_range.mp
    ((comap_range_eq_of_fpqc_square i q qB iQ hsquare hkernel).le T hx))

/-- The descended point has exactly the original ambient image. -/
theorem quotientPreimagePoint_comp {T : Over S} (x : T ⟶ G.X)
    (hx : x ≫ q.hom.hom ∈ (range iQ).carrier T) :
    quotientPreimagePoint i q qB iQ hsquare hkernel x hx ≫ i.hom.hom = x :=
  Classical.choose_spec (mem_range.mp
    ((comap_range_eq_of_fpqc_square i q qB iQ hsquare hkernel).le T hx))

end Langlands.GroupScheme.SubgroupFunctor

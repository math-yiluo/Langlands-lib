import Langlands.GroupScheme.Torus.ClosedFibreWeylBound
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Full Weyl images and containment of normalizer points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {T : CommGroupScheme S} {H G : GroupScheme S}
  (i : T.toGrp ⟶ H) (f : H ⟶ G)

/-- If the entire torus centralizer is contained in the subgroup, so are its
centralizing base points. -/
theorem centralizerPoints_le_range_of_torusCentralizer_le
    (hZ : torusCentralizer (i ≫ f) ≤ SubgroupFunctor.range f) :
    centralizerPoints (i ≫ f) ≤ (SubgroupFunctor.range f).carrier (Over.mk (𝟙 S)) :=
  fun _ hn => hZ _ (centralizerPoints_le_torusCentralizer (i ≫ f) hn)

variable [Mono i.hom.hom.left] [Mono (i ≫ f).hom.hom.left]

/-- Ambient homomorphisms include the full character images for the same torus. -/
theorem weylImage_le_postcomp : weylImage i ≤ weylImage (i ≫ f) := by
  rintro a ⟨n, rfl⟩
  exact ⟨normalizerPointsMap i f (i ≫ f) rfl n,
    weylAction_normalizerPointsMap i f (i ≫ f) rfl n⟩

/-- Equal full character images and containment of the centralizer force
containment of the entire normalizer on base points. -/
theorem normalizerPoints_le_range_of_weylImage_eq
    (hT : IsSplitTorus T.toGrp)
    (hW : weylImage i = weylImage (i ≫ f))
    (hZ : centralizerPoints (i ≫ f) ≤
      (SubgroupFunctor.range f).carrier (Over.mk (𝟙 S))) :
    normalizerPoints (i ≫ f) ≤ (SubgroupFunctor.range f).carrier (Over.mk (𝟙 S)) := by
  intro n hn
  let n' : normalizerPoints (i ≫ f) := ⟨n, hn⟩
  have hw : weylAction (i ≫ f) n' ∈ weylImage i := by
    rw [hW]
    exact ⟨n', rfl⟩
  obtain ⟨m, hm⟩ := hw
  let m' := normalizerPointsMap i f (i ≫ f) rfl m
  have hm' : weylAction (i ≫ f) m' = weylAction (i ≫ f) n' :=
    (weylAction_normalizerPointsMap i f (i ≫ f) rfl m).trans hm
  have hker : n' * m'⁻¹ ∈ (weylAction (i ≫ f)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm', mul_inv_cancel]
  rw [hT.weylAction_ker (i ≫ f)] at hker
  have hcentral : (n' * m'⁻¹).val ∈ centralizerPoints (i ≫ f) := hker
  have hmrange : m'.val ∈ (SubgroupFunctor.range f).carrier (Over.mk (𝟙 S)) :=
    SubgroupFunctor.mem_range.mpr ⟨m.val, rfl⟩
  have hh := ((SubgroupFunctor.range f).carrier _).mul_mem (hZ hcentral) hmrange
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using hh

end Base

section Field

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ H) (f : H ⟶ G)
  [Mono i.hom.hom.left] [Mono (i ≫ f).hom.hom.left]

/-- The character image and actual normalizer modulo centralizer quotient
have equal order for every split torus. -/
theorem IsSplitTorus.natCard_weylImage (hT : IsSplitTorus T.toGrp) :
    Nat.card (weylImage i) = Nat.card (relativeWeylGroup i) := by
  unfold relativeWeylGroup
  rw [← hT.weylAction_ker i]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (weylAction i)).toEquiv).symm

/-- A reverse order bound identifies the nested full Weyl images when the
ambient image is finite. -/
theorem weylImage_eq_postcomp_of_natCard_le (hT : IsSplitTorus T.toGrp)
    [Finite (weylImage (i ≫ f))]
    (hcard : Nat.card (relativeWeylGroup (i ≫ f)) ≤ Nat.card (relativeWeylGroup i)) :
    weylImage i = weylImage (i ≫ f) := by
  apply Subgroup.eq_of_le_of_card_ge (weylImage_le_postcomp i f)
  rwa [hT.natCard_weylImage (i ≫ f), hT.natCard_weylImage i]

/-- The compatible equivalence of the actual full Weyl images supplied by a
reverse order bound. -/
def weylImagePostcompEquivOfNatCardLe (hT : IsSplitTorus T.toGrp)
    [Finite (weylImage (i ≫ f))]
    (hcard : Nat.card (relativeWeylGroup (i ≫ f)) ≤ Nat.card (relativeWeylGroup i)) :
    weylImage i ≃* weylImage (i ≫ f) :=
  MulEquiv.subgroupCongr (weylImage_eq_postcomp_of_natCard_le i f hT hcard)

@[simp]
theorem weylImagePostcompEquivOfNatCardLe_val (hT : IsSplitTorus T.toGrp)
    [Finite (weylImage (i ≫ f))]
    (hcard : Nat.card (relativeWeylGroup (i ≫ f)) ≤ Nat.card (relativeWeylGroup i))
    (w : weylImage i) :
    (weylImagePostcompEquivOfNatCardLe i f hT hcard w).val = w.val := rfl

/-- For a closed split torus in an affine algebraic ambient group, a reverse
Weyl-order bound and centralizer containment imply normalizer containment. -/
theorem normalizerPoints_le_range_of_natCard_le
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup (i ≫ f))
    (hcard : Nat.card (relativeWeylGroup (i ≫ f)) ≤ Nat.card (relativeWeylGroup i))
    (hZ : torusCentralizer (i ≫ f) ≤ SubgroupFunctor.range f) :
    normalizerPoints (i ≫ f) ≤ (SubgroupFunctor.range f).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  let : Finite (weylImage (i ≫ f)) := splitTorusWeylImageFinite k G T hT (i ≫ f) hi
  exact normalizerPoints_le_range_of_weylImage_eq i f hT
    (weylImage_eq_postcomp_of_natCard_le i f hT hcard)
    (centralizerPoints_le_range_of_torusCentralizer_le i f hZ)

end Field

end Langlands.GroupScheme

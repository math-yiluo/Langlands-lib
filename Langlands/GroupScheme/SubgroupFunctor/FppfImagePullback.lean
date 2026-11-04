import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Cartesian restriction of fppf morphisms to represented subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G Q H K : GroupScheme B}
    {F : SubgroupFunctor G} {E : SubgroupFunctor Q}
    {i : H ⟶ G} {j : K ⟶ Q}

namespace IsRepresentedBy

/-- An ambient homomorphism carrying `F` into `E` induces monoid homomorphisms
on their points over every test scheme. -/
def mapPointsHom (q : G ⟶ Q) (hF : F ≤ E.comap q) (T : Over B) :
    F.carrier T →* E.carrier T where
  toFun x := ⟨x.val ≫ q.hom.hom, hF T x.property⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _)

/-- Restrict an actual ambient homomorphism to supplied subgroup
representatives using all-test containment and Yoneda lifting. -/
def restrictionHom (hi : F.IsRepresentedBy i) (hj : E.IsRepresentedBy j)
    (q : G ⟶ Q) (hF : F ≤ E.comap q) : H ⟶ K :=
  hi.lift hj (mapPointsHom q hF) (fun _ _ => Category.assoc _ _ _)

/-- The induced restriction homomorphism commutes with the original inclusions. -/
theorem restrictionHom_comp (hi : F.IsRepresentedBy i) (hj : E.IsRepresentedBy j)
    (q : G ⟶ Q) (hF : F ≤ E.comap q) :
    hi.restrictionHom hj q hF ≫ j = i ≫ q :=
  hi.lift_comp_eq hj (mapPointsHom q hF) (fun _ _ => Category.assoc _ _ _)
    (fun _ _ => rfl)

/-- An equality of full inverse-image subgroup functors makes every compatible
square of their actual representatives cartesian. -/
theorem isPullback_of_comap_eq (hi : F.IsRepresentedBy i) (hj : E.IsRepresentedBy j)
    (q : G ⟶ Q) (p : H ⟶ K) (hsq : i ≫ q = p ≫ j) (hF : E.comap q = F) :
    IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom := by
  let : Mono i.hom.hom := hi.1
  let : Mono j.hom.hom := hj.1
  have hs : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) hsq
  have hmem (c : PullbackCone q.hom.hom j.hom.hom) : c.fst ∈ F.carrier c.pt := by
    rw [← hF]
    change c.fst ≫ q.hom.hom ∈ E.carrier c.pt
    rw [c.condition, ← hj.2]
    exact mem_range.mpr ⟨c.snd, rfl⟩
  let liftPoint := fun (c : PullbackCone q.hom.hom j.hom.hom) =>
    (hi.pointsEquiv c.pt).symm ⟨c.fst, hmem c⟩
  have hfst (c : PullbackCone q.hom.hom j.hom.hom) :
      liftPoint c ≫ i.hom.hom = c.fst :=
    hi.pointsEquiv_symm_comp ⟨c.fst, hmem c⟩
  refine ⟨⟨hs⟩, ⟨PullbackCone.IsLimit.mk _ liftPoint hfst ?_ ?_⟩⟩
  · intro c
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, ← hs, ← Category.assoc, hfst, c.condition]
  · intro c m hm _hn
    apply (cancel_mono i.hom.hom).mp
    exact hm.trans (hfst c).symm

/-- A full inverse-image equality restricts an fppf homomorphism to an fppf
homomorphism between the supplied subgroup representatives. -/
theorem isFppfImage_of_comap_eq (hi : F.IsRepresentedBy i) (hj : E.IsRepresentedBy j)
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] (hF : E.comap q = F) :
    IsFppfImage F E q := by
  have hle : F ≤ E.comap q := hF.ge
  let p := hi.restrictionHom hj q hle
  have hsq : i ≫ q = p ≫ j := (hi.restrictionHom_comp hj q hle).symm
  have hpb := (hi.isPullback_of_comap_eq hj q p hsq hF).map (Over.forget B)
  have hflat : Flat p.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Flat q.hom.hom.left)
  have hsurj : Surjective p.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Surjective q.hom.hom.left)
  have hlfp : LocallyOfFinitePresentation p.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : LocallyOfFinitePresentation q.hom.hom.left)
  exact ⟨H, K, i, j, p, hi, hj, hsq, hflat, hsurj, hlfp⟩

end IsRepresentedBy

/-- For represented subgroups and an fppf ambient homomorphism, an exact
inverse-image identity is equivalent to an fppf subgroup image together with
containment of the entire actual kernel. -/
theorem comap_eq_iff_isFppfImage_and_kernel_le
    (hi : F.IsRepresentedBy i) (hj : E.IsRepresentedBy j)
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] :
    E.comap q = F ↔ IsFppfImage F E q ∧ range (kernelι q) ≤ F := by
  constructor
  · intro hF
    refine ⟨hi.isFppfImage_of_comap_eq hj q hF, ?_⟩
    intro T x hx
    rw [← hF]
    change x ≫ q.hom.hom ∈ E.carrier T
    rw [(mem_range_kernelι_iff q x).mp hx]
    exact (E.carrier T).one_mem
  · rintro ⟨hImage, hker⟩
    exact hImage.comap_eq_of_kernel_le hker

end Langlands.GroupScheme.SubgroupFunctor

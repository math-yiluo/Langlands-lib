import Langlands.GroupScheme.CentralIsogeny.Pullback
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Restricting a central product to a subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {Z D P G : GroupScheme S}

/-- Keep the central coordinate and include the intersection in the other factor. -/
def productIntersectionProjection (Z : GroupScheme S) (d : D ⟶ G) (i : P ⟶ G) :
    Z ⊗ subgroupIntersection d i ⟶ Z ⊗ D :=
  lift (fst Z (subgroupIntersection d i))
    (snd Z (subgroupIntersection d i) ≫ subgroupIntersectionFst d i)

@[reassoc (attr := simp)]
theorem productIntersectionProjection_fst (Z : GroupScheme S) (d : D ⟶ G) (i : P ⟶ G) :
    productIntersectionProjection Z d i ≫ fst Z D = fst Z (subgroupIntersection d i) := by
  simp [productIntersectionProjection]

@[reassoc (attr := simp)]
theorem productIntersectionProjection_snd (Z : GroupScheme S) (d : D ⟶ G) (i : P ⟶ G) :
    productIntersectionProjection Z d i ≫ snd Z D =
      snd Z (subgroupIntersection d i) ≫ subgroupIntersectionFst d i := by
  simp [productIntersectionProjection]

/-- Factor the central product through a monic subgroup containing the central factor. -/
def centralProductIntersectionFactor (z : Z ⟶ G) (hz : IsCentral z)
    (d : D ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i) :
    Z ⊗ subgroupIntersection d i ⟶ P :=
  (show (SubgroupFunctor.range i).IsRepresentedBy i from ⟨inferInstance, rfl⟩).factorHom
    (prodHom z (subgroupIntersectionHom d i) (hz.commute_values _)) (by
      intro U x hx
      obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [comp_prodHom]
      apply (SubgroupFunctor.range i).carrier U |>.mul_mem
      · exact hzi U (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)
      · refine SubgroupFunctor.mem_range.mpr
          ⟨(productPointsEquiv Z (subgroupIntersection d i) U p).2 ≫
            (subgroupIntersectionSnd d i).hom.hom, ?_⟩
        rw [Category.assoc]
        congr 1
        exact congrArg (fun f : subgroupIntersection d i ⟶ G => f.hom.hom)
          (subgroupIntersection_condition d i).symm)

@[reassoc (attr := simp)]
theorem centralProductIntersectionFactor_comp (z : Z ⟶ G) (hz : IsCentral z)
    (d : D ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i) :
    centralProductIntersectionFactor z hz d i hzi ≫ i =
      prodHom z (subgroupIntersectionHom d i) (hz.commute_values _) :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The restriction square commutes as a square of group schemes. -/
theorem centralProductIntersectionFactor_square (z : Z ⟶ G) (hz : IsCentral z)
    (d : D ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i) :
    centralProductIntersectionFactor z hz d i hzi ≫ i =
      productIntersectionProjection Z d i ≫ prodHom z d (hz.commute_values _) := by
  rw [centralProductIntersectionFactor_comp]
  apply hom_ext_points
  intro U p
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom, comp_prodHom]
  congr 1
  · simp [productPointsEquiv, homEquivToProd, productIntersectionProjection]
  · simp [productPointsEquiv, homEquivToProd, productIntersectionProjection,
      subgroupIntersectionHom, Category.assoc]

/-- The restricted central product is the pullback of the original product
along the subgroup embedding. -/
theorem centralProductIntersectionFactor_isPullback (z : Z ⟶ G) (hz : IsCentral z)
    (d : D ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i) :
    IsPullback (centralProductIntersectionFactor z hz d i hzi).hom.hom
      (productIntersectionProjection Z d i).hom.hom i.hom.hom
      (prodHom z d (hz.commute_values _)).hom.hom := by
  let k : Z ⟶ P :=
    (show (SubgroupFunctor.range i).IsRepresentedBy i from ⟨inferInstance, rfl⟩).factorHom
      z hzi
  have hk : k.hom.hom ≫ i.hom.hom = z.hom.hom :=
    congrArg (fun f : Z ⟶ G => f.hom.hom)
      (SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _)
  let hpb := subgroupIntersection_isPullback d i
  have : Mono (subgroupIntersectionFst d i).hom.hom := hpb.mono_fst_of_mono
  have he := congrArg (fun f : Z ⊗ subgroupIntersection d i ⟶ G => f.hom.hom)
    (centralProductIntersectionFactor_square z hz d i hzi)
  change (centralProductIntersectionFactor z hz d i hzi).hom.hom ≫ i.hom.hom =
    (productIntersectionProjection Z d i).hom.hom ≫
      (prodHom z d (hz.commute_values _)).hom.hom at he
  let L := fun s : PullbackCone i.hom.hom (prodHom z d (hz.commute_values _)).hom.hom =>
    lift (s.snd ≫ fst Z.X D.X)
      (hpb.lift (s.snd ≫ snd Z.X D.X)
        ((s.snd ≫ fst Z.X D.X ≫ k.hom.hom)⁻¹ * s.fst) (by
          simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hk]
          apply eq_inv_mul_iff_mul_eq.mpr
          simpa only [comp_prodHom, productPointsEquiv_fst, productPointsEquiv_snd,
            Category.assoc] using s.condition.symm))
  have hLv (s : PullbackCone i.hom.hom (prodHom z d (hz.commute_values _)).hom.hom) :
      L s ≫ (productIntersectionProjection Z d i).hom.hom = s.snd := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [L, productIntersectionProjection]
    · simp [L, productIntersectionProjection]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ he) ?_
  refine PullbackCone.IsLimit.mk he L ?_ hLv ?_
  · intro s
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, he, ← Category.assoc, hLv]
    exact s.condition.symm
  · intro s m _ hmv
    apply CartesianMonoidalCategory.hom_ext
    · have hm := congrArg (fun f => f ≫ fst Z.X D.X) hmv
      simpa [L, productIntersectionProjection] using hm
    · apply (cancel_mono (subgroupIntersectionFst d i).hom.hom).mp
      have hm := congrArg (fun f => f ≫ snd Z.X D.X) hmv
      simpa [L, productIntersectionProjection, Category.assoc] using hm

/-- A central isogeny product restricts to a central isogeny onto every
monic subgroup containing its central factor. -/
theorem isCentralIsogeny_centralProductIntersectionFactor
    (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i) :
    IsCentralIsogeny (centralProductIntersectionFactor z hz d i hzi) :=
  hprod.of_isPullback (centralProductIntersectionFactor_isPullback z hz d i hzi)

end Langlands.GroupScheme

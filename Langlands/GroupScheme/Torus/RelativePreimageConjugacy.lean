import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.GroupScheme.Derived.CentralIntersectionReduction

/-! # Torus preimages, conjugacy, and fppf locality -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Every base section of the target of an fppf homomorphism lifts after
one actual fppf change of the base. -/
theorem exists_fppf_baseChange_section_lift {S : Scheme.{u}} {G Q : GroupScheme S}
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (g : Over.mk (𝟙 S) ⟶ Q.X) :
    ∃ (U : Scheme.{u}) (b : U ⟶ S), Flat b ∧ Surjective b ∧
      LocallyOfFinitePresentation b ∧
      ∃ x : Over.mk (𝟙 U) ⟶ ((baseChange b).obj G).X,
        x ≫ ((baseChange b).map q).hom.hom = baseChangeBasePoint b Q g := by
  let U := pullback g.left q.hom.hom.left
  let b : U ⟶ S := pullback.fst g.left q.hom.hom.left
  let y : Over.mk b ⟶ G.X := Over.homMk
    (pullback.snd g.left q.hom.hom.left) (by
      rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w g]
      exact Category.comp_id b)
  let x := (baseChangeBasePointsEquiv b G).symm y
  refine ⟨U, b, inferInstance, inferInstance, inferInstance, x, ?_⟩
  apply (baseChangeBasePointsEquiv b Q).injective
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left]
  change (x.left ≫ ((Over.pullback b).map q.hom.hom).left) ≫ pullback.fst Q.X.hom b = _
  rw [Category.assoc]
  simp only [Over.pullback_map_left, pullback.lift_fst]
  rw [← Category.assoc, ← baseChangeBasePointsEquiv_left]
  have hx : baseChangeBasePointsEquiv b G x = y :=
    (baseChangeBasePointsEquiv b G).apply_symm_apply y
  rw [hx, baseChangeBasePoint_fst]
  exact pullback.condition.symm

namespace SubgroupPreimage

/-- Relative-torus status of an actual subgroup preimage descends from the
corresponding actual preimages over an fppf base cover. -/
theorem isRelativeTorus_of_fppfCover {S : Scheme.{u}} {G Q H : GroupScheme S}
    (q : G ⟶ Q) (j : H ⟶ Q)
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (h : ∀ a, RelativeTorus.IsTorus
      (groupScheme ((baseChange (𝒰.f a)).map q) ((baseChange (𝒰.f a)).map j))) :
    RelativeTorus.IsTorus (groupScheme q j) := by
  apply RelativeTorus.IsTorus.of_fppfCover 𝒰
  intro a
  exact RelativeTorus.IsTorus.of_iso (subgroupIntersectionBaseChangeIso (𝒰.f a) q j) (h a)

/-- Compatible ambient isomorphisms transport a known torus preimage to a
torus preimage of the transported target subgroup. -/
theorem isRelativeTorus_of_conjugate_image {S : Scheme.{u}}
    {G Q H A B : GroupScheme S} (q : G ⟶ Q)
    (t : H ⟶ G) (j : A ⟶ Q) (j' : B ⟶ Q)
    (hT : RelativeTorus.IsTorus H) (ht : IsClosedSubgroup t)
    (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j')
    (hpre : (SubgroupFunctor.range j).comap q = SubgroupFunctor.range t)
    (eG : G ≅ G) (eQ : Q ≅ Q)
    (hsq : eG.hom ≫ q = q ≫ eQ.hom)
    (hconj : SubgroupFunctor.range (j ≫ eQ.hom) = SubgroupFunctor.range j') :
    RelativeTorus.IsTorus (groupScheme q j') := by
  let : IsClosedImmersion t.hom.hom.left := ht
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion (inclusion q j').hom.hom.left := isClosedSubgroup q j' hj'
  have htrep : (SubgroupFunctor.range t).IsRepresentedBy t :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hinv : eG.inv ≫ q = q ≫ eQ.inv := by
    have hh := congrArg (fun f => eG.inv ≫ f ≫ eQ.inv) hsq
    simpa only [← Category.assoc, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm
  have hr : SubgroupFunctor.range (t ≫ eG.hom) =
      (SubgroupFunctor.range j').comap q := by
    rw [(htrep.comp_iso eG).2, ← hconj, (hjrep.comp_iso eQ).2,
      ← SubgroupFunctor.comap_comp, ← hinv, SubgroupFunctor.comap_comp, hpre]
  have htconj : ((SubgroupFunctor.range j').comap q).IsRepresentedBy (t ≫ eG.hom) :=
    ⟨(htrep.comp_iso eG).1, hr⟩
  have hprep : ((SubgroupFunctor.range j').comap q).IsRepresentedBy (inclusion q j') :=
    ⟨Over.mono_of_mono_left _, range_inclusion q j'⟩
  exact RelativeTorus.IsTorus.of_iso (hprep.isoOfIsRepresentedBy htconj) hT


/-- The complete proposition proved by the supplied helper, with every hypothesis explicit. -/
def RelativeTorusPreimageConjugacyStatement : Prop :=
  ∀ {S : Scheme.{u}}
    {G Q H A B : GroupScheme S} (q : G ⟶ Q)
    (t : H ⟶ G) (j : A ⟶ Q) (j' : B ⟶ Q)
    (_hT : RelativeTorus.IsTorus H) (_ht : IsClosedSubgroup t)
    (_hj : IsClosedSubgroup j) (_hj' : IsClosedSubgroup j')
    (_hpre : (SubgroupFunctor.range j).comap q = SubgroupFunctor.range t)
    (eG : G ≅ G) (eQ : Q ≅ Q)
    (_hsq : eG.hom ≫ q = q ≫ eQ.hom)
    (_hconj : SubgroupFunctor.range (j ≫ eQ.hom) = SubgroupFunctor.range j'),
    RelativeTorus.IsTorus (groupScheme q j')

/-- The retained helper proof establishes the named proposition. -/
theorem relativeTorusPreimageConjugacy : RelativeTorusPreimageConjugacyStatement.{u} := by
  unfold RelativeTorusPreimageConjugacyStatement
  exact @isRelativeTorus_of_conjugate_image.{u}

end SubgroupPreimage
end Langlands.GroupScheme

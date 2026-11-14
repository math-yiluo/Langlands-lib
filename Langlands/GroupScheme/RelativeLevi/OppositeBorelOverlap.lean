import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.RelativeLevi.BorelEtaleTransport
import Langlands.GroupScheme.RelativeLevi.OppositeBorelRelativeUniqueness
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Agreement of local opposite Borels on étale overlaps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The local opposite intersection transports through a further base change
and its canonical ambient comparison. -/
theorem oppositeBorel_intersection_baseChange_comparison
    {S U V : Scheme.{u}} {G B Z : GroupScheme S}
    (i : B ⟶ G) (t : Z ⟶ G)
    (b : U ⟶ S) (c : V ⟶ U) (r : V ⟶ S) (h : c ≫ b = r)
    {C : GroupScheme U} (j : C ⟶ (GroupScheme.baseChange b).obj G)
    (hinter : SubgroupFunctor.range j ⊓
        SubgroupFunctor.range ((GroupScheme.baseChange b).map i) =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map t)) :
    SubgroupFunctor.range ((GroupScheme.baseChange c).map j ≫
        (Descent.pullbackComparison b c r h G).hom) ⊓
        SubgroupFunctor.range ((GroupScheme.baseChange r).map i) =
      SubgroupFunctor.range ((GroupScheme.baseChange r).map t) := by
  have hbc := congrArg (fun F => F.baseChange c) hinter
  rw [SubgroupFunctor.inf_baseChange,
    ← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom] at hbc
  have htransport := congrArg
    (fun F => F.comap (Descent.pullbackComparison b c r h G).inv) hbc
  rw [SubgroupFunctor.comap_inf,
    ← SubgroupFunctor.range_comp_iso,
    ← SubgroupFunctor.range_comp_iso,
    ← SubgroupFunctor.range_comp_iso] at htransport
  rw [Descent.pullbackComparison_naturality,
    Descent.pullbackComparison_naturality,
    SubgroupFunctor.range_iso_comp,
    SubgroupFunctor.range_iso_comp] at htransport
  exact htransport

/-- Relative uniqueness makes two local opposite Borel choices agree on
their overlap, in the common direct ambient pullback. -/
theorem oppositeBorel_overlap_range_eq
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    {S : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (C : ∀ a : 𝒰.I₀, GroupScheme (𝒰.X a))
    (j : ∀ a : 𝒰.I₀, C a ⟶ (GroupScheme.baseChange (𝒰.f a)).obj G)
    (hB : ∀ a, IsRelativeBorelSubgroup (j a))
    (hinter : ∀ a, SubgroupFunctor.range (j a) ⊓
        SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map i) =
      SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map t))
    (a b : 𝒰.I₀) :
    let p := pullback.fst (𝒰.f a) (𝒰.f b)
    let q := pullback.snd (𝒰.f a) (𝒰.f b)
    let r := p ≫ 𝒰.f a
    SubgroupFunctor.range ((GroupScheme.baseChange p).map (j a) ≫
        (Descent.pullbackComparison (𝒰.f a) p r rfl G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange q).map (j b) ≫
        (Descent.pullbackComparison (𝒰.f b) q r pullback.condition.symm G).hom) := by
  let p := pullback.fst (𝒰.f a) (𝒰.f b)
  let q := pullback.snd (𝒰.f a) (𝒰.f b)
  let r := p ≫ 𝒰.f a
  let ea := Descent.pullbackComparison (𝒰.f a) p r rfl G
  let eb := Descent.pullbackComparison (𝒰.f b) q r pullback.condition.symm G
  have : Etale (𝒰.f a) := 𝒰.map_prop a
  have : Etale (𝒰.f b) := 𝒰.map_prop b
  have : Etale p := inferInstanceAs (Etale (pullback.fst (𝒰.f a) (𝒰.f b)))
  have : Etale q := inferInstanceAs (Etale (pullback.snd (𝒰.f a) (𝒰.f b)))
  have : Etale r := inferInstanceAs (Etale (p ≫ 𝒰.f a))
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom ((GroupScheme.baseChange (𝒰.f a)).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom (𝒰.f a) hG.isAffineHom
  have : IsAffineHom ((GroupScheme.baseChange (𝒰.f b)).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom (𝒰.f b) hG.isAffineHom
  have hGr : IsReductive ((GroupScheme.baseChange r).obj G) := hG.baseChange r
  have hTr : RelativeTorus.IsTorus ((CommGroupScheme.baseChange r).obj T).toGrp :=
    hT.baseChange r
  have htr : IsClosedSubgroup ((GroupScheme.baseChange r).map t) := ht.baseChange r
  have hmaxr : IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange r).obj T)
      ((GroupScheme.baseChange r).map t) := hmax.baseChange r
  have hir : IsRelativeBorelSubgroup ((GroupScheme.baseChange r).map i) :=
    hi.baseChange_of_etale r
  have hjap : IsRelativeBorelSubgroup ((GroupScheme.baseChange p).map (j a)) :=
    (hB a).baseChange_of_etale p
  have hjbq : IsRelativeBorelSubgroup ((GroupScheme.baseChange q).map (j b)) :=
    (hB b).baseChange_of_etale q
  have hjapr : IsRelativeBorelSubgroup
      ((GroupScheme.baseChange p).map (j a) ≫ ea.hom) := hjap.comp_iso ea
  have hjbqr : IsRelativeBorelSubgroup
      ((GroupScheme.baseChange q).map (j b) ≫ eb.hom) := hjbq.comp_iso eb
  apply oppositeRelativeBorel_range_eq
    (S := pullback (𝒰.f a) (𝒰.f b))
    (G := (GroupScheme.baseChange r).obj G)
    (T := (CommGroupScheme.baseChange r).obj T)
    ((GroupScheme.baseChange r).map t)
    ((GroupScheme.baseChange r).map i)
    ((GroupScheme.baseChange p).map (j a) ≫ ea.hom)
    ((GroupScheme.baseChange q).map (j b) ≫ eb.hom)
    hLie hGr hTr htr hmaxr hir hjapr hjbqr
  · exact oppositeBorel_intersection_baseChange_comparison i t (𝒰.f a) p r rfl
      (j a) (hinter a)
  · exact oppositeBorel_intersection_baseChange_comparison i t (𝒰.f b) q r
      pullback.condition.symm (j b) (hinter b)

end Langlands.GroupScheme

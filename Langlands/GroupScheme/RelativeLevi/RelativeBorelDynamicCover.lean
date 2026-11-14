import Langlands.GroupScheme.RelativeLevi.BorelDynamicCover

/-! # Refining a relative torus splitting cover by dynamic Borel neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeBorelDynamicPresentation

variable {S : Scheme.{u}} {G B : GroupScheme S}

/-- Bind a supplied family of actual dynamic Borel neighbourhoods to an
étale cover, keeping the neighbourhood family as explicit data. -/
def coverOfNeighbourhoods (i : B ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (D : ∀ (a : 𝒰.I₀) (s : 𝒰.X a),
      RelativeLevi.BorelDynamicNeighbourhoodData ((GroupScheme.baseChange (𝒰.f a)).map i)
        ((CommGroupScheme.baseChange (𝒰.f a)).obj T)
        ((GroupScheme.baseChange (𝒰.f a)).map t) s) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  𝒰.bind (fun a => Scheme.Cover.mkOfCovers (𝒰.X a)
    (fun s => (D a s).base) (fun s => (D a s).projection)
    (fun s => ⟨s, (D a s).contains.choose, (D a s).contains.choose_spec⟩)
    (fun s => by
      have : IsOpenImmersion (D a s).projection := (D a s).openImmersion
      infer_instance))

variable {S : Scheme.{u}} {G B : GroupScheme S}
    (i : B ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)

include hti in
/-- The original all-test containment is preserved by actual base change. -/
theorem torus_range_le_baseChange {U : Scheme.{u}} (b : U ⟶ S) :
    SubgroupFunctor.range ((GroupScheme.baseChange b).map t) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map i) := by
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
  exact fun V x hx => hti _ hx

include hG ht hmax hi hti in
/-- A dynamic Borel neighbourhood cover over one étale splitting chart. -/
def chartCover {U : Scheme.{u}} (b : U ⟶ S) [Etale b]
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) U := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  exact borelDynamicOpenCover
    ((GroupScheme.baseChange b).map i) ((CommGroupScheme.baseChange b).obj T)
    ((GroupScheme.baseChange b).map t) (hG.baseChange b) hsplit
    (ht.baseChange b) (hmax.baseChange b) (hi.baseChange_of_etale b)
    (torus_range_le_baseChange i T t hti b)

variable (hT : RelativeTorus.IsTorus T.toGrp)

/-- The original torus splitting cover. -/
def splittingCover : Scheme.Cover.{u} (Scheme.precoverage @Etale) S := hT.choose

/-- On each splitting chart, the given torus is split. -/
theorem splittingCover_split (a : (splittingCover T hT).I₀) :
    IsSplitTorus
      ((CommGroupScheme.baseChange ((splittingCover T hT).f a)).obj T).toGrp :=
  hT.choose_spec a

include hG ht hmax hi hti in
/-- The selected dynamic-neighbourhood cover of one splitting chart. -/
def splittingChartCover (a : (splittingCover T hT).I₀) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) ((splittingCover T hT).X a) := by
  have : Etale ((splittingCover T hT).f a) := (splittingCover T hT).map_prop a
  exact chartCover i T t hG ht hmax hi hti ((splittingCover T hT).f a)
    (splittingCover_split T hT a)

include hG ht hmax hi hti in
/-- The small étale cover obtained by refining every torus splitting chart
by its dynamic Borel neighbourhood cover. -/
def cover : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  (splittingCover T hT).bind (splittingChartCover i T t hG ht hmax hi hti hT)

end RelativeBorelDynamicPresentation

end Langlands.GroupScheme

import Langlands.GroupScheme.RelativeLevi.TorusLeviLocal
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.ParabolicMaximalTori
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.RelativeLevi.SplitTorusDynamicNeighbourhood

/-! # A prescribed-torus dynamic presentation cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.RelativeLevi

namespace TorusDynamicPresentation

/-- Express a presentation over an iterated pullback in the direct pullback,
keeping its cocharacter in the original prescribed torus. -/
def direct {S U V : Scheme.{u}} {G P : GroupScheme S}
    {T : CommGroupScheme S} (i : P ⟶ G) (t : T.toGrp ⟶ P)
    (b : U ⟶ S) (q : V ⟶ U)
    (d : TorusDynamicPresentation
      ((GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map i))
      (T := (CommGroupScheme.baseChange q).obj ((CommGroupScheme.baseChange b).obj T))
      ((GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map t))) :
    TorusDynamicPresentation ((GroupScheme.baseChange (q ≫ b)).map i)
      (T := (CommGroupScheme.baseChange (q ≫ b)).obj T)
      ((GroupScheme.baseChange (q ≫ b)).map t) where
  cocharacter := d.cocharacter ≫
    (Descent.pullbackComparison b q (q ≫ b) rfl T.toGrp).hom
  represents := by
    have heq :
        (d.cocharacter ≫ (Descent.pullbackComparison b q (q ≫ b) rfl T.toGrp).hom) ≫
            (GroupScheme.baseChange (q ≫ b)).map t ≫
            (GroupScheme.baseChange (q ≫ b)).map i =
          (d.cocharacter ≫
            (GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map t) ≫
            (GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map i)) ≫
              (Descent.pullbackComparison b q (q ≫ b) rfl G).hom := by
      simp only [Category.assoc]
      rw [← Descent.pullbackComparison_naturality_assoc,
        ← Descent.pullbackComparison_naturality]
    rw [heq]
    exact isRepresentedBy_dynamicParabolic_direct i b q _ d.represents

end TorusDynamicPresentation

namespace SplitTorusDynamicNeighbourhoodData

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P} {s : S}

/-- Package the retained cocharacter as a prescribed-torus presentation. -/
def presentation (D : SplitTorusDynamicNeighbourhoodData i T t s) :
    TorusDynamicPresentation ((GroupScheme.baseChange D.projection).map i)
      (T := (CommGroupScheme.baseChange D.projection).obj T)
      ((GroupScheme.baseChange D.projection).map t) :=
  ⟨D.cocharacter, D.presents⟩

/-- The point-indexed open cover from a family of dynamic neighbourhoods. -/
def cover (D : ∀ s : S, SplitTorusDynamicNeighbourhoodData i T t s) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  Scheme.Cover.mkOfCovers S (fun s => (D s).base) (fun s => (D s).projection)
    (fun s => ⟨s, (D s).contains.choose, (D s).contains.choose_spec⟩)
    (fun s => by
      have : IsOpenImmersion (D s).projection := (D s).openImmersion
      infer_instance)

end SplitTorusDynamicNeighbourhoodData

/-- Bind neighbourhood covers to a supplied cover and retain actual
prescribed-torus presentations in the direct pullbacks. -/
def torusDynamicCoverOfNeighbourhoods
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (D : ∀ (a : 𝒰.I₀) (s : 𝒰.X a),
      SplitTorusDynamicNeighbourhoodData ((GroupScheme.baseChange (𝒰.f a)).map i)
        ((CommGroupScheme.baseChange (𝒰.f a)).obj T)
        ((GroupScheme.baseChange (𝒰.f a)).map t) s) :
    Σ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒱.I₀,
        TorusDynamicPresentation ((GroupScheme.baseChange (𝒱.f a)).map i)
          (T := (CommGroupScheme.baseChange (𝒱.f a)).obj T)
          ((GroupScheme.baseChange (𝒱.f a)).map t) :=
  ⟨𝒰.bind (fun a => SplitTorusDynamicNeighbourhoodData.cover (D a)),
    fun a => (D a.1 a.2).presentation.direct i t (𝒰.f a.1) (D a.1 a.2).projection⟩

/-- Choose an étale cover and actual dynamic presentations through the
prescribed relative maximal torus of the parabolic. -/
def torusDynamicPresentationCover
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hT : RelativeTorus.IsTorus T.toGrp) (hmax : IsFibrewiseMaximalTorus t) :
    Σ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒱.I₀,
        TorusDynamicPresentation ((GroupScheme.baseChange (𝒱.f a)).map i)
          (T := (CommGroupScheme.baseChange (𝒱.f a)).obj T)
          ((GroupScheme.baseChange (𝒱.f a)).map t) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S := hT.choose
  have hsplit (a : 𝒰.I₀) :
      IsSplitTorus ((CommGroupScheme.baseChange (𝒰.f a)).obj T).toGrp :=
    hT.choose_spec a
  let D (a : 𝒰.I₀) (s : 𝒰.X a) :
      SplitTorusDynamicNeighbourhoodData ((GroupScheme.baseChange (𝒰.f a)).map i)
        ((CommGroupScheme.baseChange (𝒰.f a)).obj T)
        ((GroupScheme.baseChange (𝒰.f a)).map t) s := by
    have ham : IsFibrewiseMaximalTorus (T := T) (t ≫ i) :=
      hmax.comp_relativeParabolic i hi hG
    have hm : IsFibrewiseMaximalTorus
        (T := (CommGroupScheme.baseChange (𝒰.f a)).obj T)
        ((GroupScheme.baseChange (𝒰.f a)).map (t ≫ i)) :=
      ham.baseChange (T := T) (𝒰.f a)
    have hms : IsMaximalTorus
        (T := (CommGroupScheme.baseChange ((𝒰.X a).fromSpecResidueField s)).obj
          ((CommGroupScheme.baseChange (𝒰.f a)).obj T))
        ((GroupScheme.baseChange ((𝒰.X a).fromSpecResidueField s)).map
          ((GroupScheme.baseChange (𝒰.f a)).map t ≫
            (GroupScheme.baseChange (𝒰.f a)).map i)) := by
      simpa only [Functor.map_comp] using hm s
    exact splitTorusDynamicNeighbourhood (hG.baseChange (𝒰.f a))
      ((GroupScheme.baseChange (𝒰.f a)).map i) (hi.baseChange hG (𝒰.f a))
      ((CommGroupScheme.baseChange (𝒰.f a)).obj T)
      ((GroupScheme.baseChange (𝒰.f a)).map t) (hsplit a) s hms
  exact torusDynamicCoverOfNeighbourhoods i t 𝒰 D

end Langlands.GroupScheme.RelativeLevi

import Langlands.GroupScheme.RelativeIdentityComponentStatements
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Uniqueness and normality of relative identity-component representatives -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsRelativeIdentityComponent

variable {S : Scheme.{u}} {G H H' : GroupScheme S} {i : H ⟶ G} {j : H' ⟶ G}

/-- All representatives have the same subgroup functor on all test schemes. -/
theorem range_eq (hi : IsRelativeIdentityComponent G i)
    (hj : IsRelativeIdentityComponent G j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  ext T x
  exact (hi.factors_iff T x).trans (hj.factors_iff T x).symm

/-- Two representatives are canonically isomorphic over the ambient group scheme. -/
def iso (hi : IsRelativeIdentityComponent G i)
    (hj : IsRelativeIdentityComponent G j) : H ≅ H' := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : IsOpenImmersion j.hom.hom.left := hj.isOpenImmersion
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range i) ⟨inferInstance, rfl⟩
    ⟨inferInstance, (hi.range_eq hj).symm⟩

/-- The canonical comparison preserves the inclusions. -/
@[reassoc]
theorem iso_hom_comp (hi : IsRelativeIdentityComponent G i)
    (hj : IsRelativeIdentityComponent G j) : (hi.iso hj).hom ≫ j = i := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : IsOpenImmersion j.hom.hom.left := hj.isOpenImmersion
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (F := SubgroupFunctor.range i) ⟨inferInstance, rfl⟩
    ⟨inferInstance, (hi.range_eq hj).symm⟩

/-- Geometric connectedness transfers between representatives over the same base. -/
theorem geometricallyConnected (hi : IsRelativeIdentityComponent G i)
    (hj : IsRelativeIdentityComponent G j) [GeometricallyConnected H'.X.hom] :
    GeometricallyConnected H.X.hom := by
  let e : H.X ≅ H'.X := (Grp.forget (Over S)).mapIso (hi.iso hj)
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have hp : IsPullback e.hom.left H.X.hom H'.X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact e.hom.w⟩
  exact MorphismProperty.of_isPullback hp ‹GeometricallyConnected H'.X.hom›

end IsRelativeIdentityComponent

namespace RelativeIdentityComponent

section Conjugation

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)

/-- The actual conjugation map restricted in its second variable. -/
def conjOver : G.X ⊗ H.X ⟶ G.X :=
  (G.X ◁ i.hom.hom) ≫ GrpObj.conj G.X

/-- The restricted conjugation map has the expected effect on all test points. -/
theorem lift_conjOver {T : Over S} (g : T ⟶ G.X) (y : T ⟶ H.X) :
    lift g y ≫ conjOver i = g * (y ≫ i.hom.hom) * g⁻¹ := by
  rw [conjOver, lift_whiskerLeft_assoc, GrpObj.lift_conj_eq_mul_mul_inv]

end Conjugation

section Field

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
  [GeometricallyConnected H.X.hom]

/-- Conjugation of a geometrically connected group maps into the identity
component of the ambient group over a field. -/
theorem range_conjOver_subset_identitySet :
    Set.range (conjOver i).left ⊆ IdentityComponent.identitySet G := by
  rintro _ ⟨z, rfl⟩
  let p : (G.X ⊗ H.X).left ⟶ G.X.left := pullback.fst G.X.hom H.X.hom
  let s : G.X ⟶ G.X ⊗ H.X := lift (𝟙 _) (toUnit _ ≫ η[H.X])
  have hF : _root_.IsConnected (p ⁻¹' {p z}) :=
    Scheme.Hom.isConnected_preimage_singleton p (p z)
  have hs : s ≫ conjOver i = toUnit _ ≫ η[G.X] := by
    rw [lift_conjOver, Category.assoc, IsMonHom.one_hom,
      ← CategoryTheory.Hom.one_def]
    simp
  have hsz : s.left (p z) ∈ p ⁻¹' {p z} := by
    change (s ≫ fst _ _).left (p z) = p z
    rw [lift_fst]
    rfl
  have hconn : _root_.IsConnected ((conjOver i).left '' (p ⁻¹' {p z})) :=
    hF.image _ (conjOver i).left.continuous.continuousOn
  refine hconn.isPreconnected.subset_connectedComponent ⟨_, hsz, ?_⟩
    ⟨z, rfl, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs, Over.comp_left,
    Scheme.Hom.comp_apply, IdentityComponent.unit_left_apply]

end Field

section Normality

variable {S : Scheme.{u}} {G H : GroupScheme S} {i : H ⟶ G}

/-- A geometrically connected representative is normal on every test scheme. -/
theorem isNormal_of_geometricallyConnected (hi : IsRelativeIdentityComponent G i)
    [GeometricallyConnected H.X.hom] : (SubgroupFunctor.range i).IsNormal := by
  intro T g x _ hx
  rw [SubgroupFunctor.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  apply (hi.factors_iff T _).mpr
  intro s z hz
  obtain ⟨t, rfl⟩ := hz
  let b := S.fromSpecResidueField s
  let F := Over.pullback b
  let i' := (GroupScheme.baseChange b).map i
  let g' : F.obj T ⟶ ((GroupScheme.baseChange b).obj G).X := F.map g
  let y' : F.obj T ⟶ ((GroupScheme.baseChange b).obj H).X := F.map y
  have : GeometricallyConnected ((GroupScheme.baseChange b).obj H).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom b))
  have hm :
      F.map (g * (y ≫ i.hom.hom) * g⁻¹) =
        g' * (y' ≫ i'.hom.hom) * g'⁻¹ := by
    rw [Functor.map_mul, Functor.map_mul, Functor.map_inv', Functor.map_comp]
    rfl
  change (F.map (g * (y ≫ i.hom.hom) * g⁻¹)).left t ∈ _
  rw [hm]
  rw [← lift_conjOver i' g' y']
  exact range_conjOver_subset_identitySet i' ⟨(lift g' y').left t,
    (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- Smooth existence already implies the normality target for every supplied
representative, by uniqueness and transfer of geometric connectedness. -/
theorem smoothNormality_of_existence (hex : SmoothExistenceStatement.{u}) :
    SmoothNormalityStatement.{u} := by
  intro S G hG H i hi
  obtain ⟨H', j, hj, -, hconn⟩ := hex S G hG
  let : GeometricallyConnected H'.X.hom := hconn
  let : GeometricallyConnected H.X.hom := hi.geometricallyConnected hj
  exact isNormal_of_geometricallyConnected hi

end Normality

end RelativeIdentityComponent
end Langlands.GroupScheme

import Langlands.Shimura.Coefficients.Etale
import Langlands.CategoryTheory.EquivariantDiagramFunctor
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Actual base change of finite geometric etale torsors -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- Base change of actual small-etale objects by the scheme fiber product.
The morphism of bases is arbitrary. -/
abbrev etaleObjectPullback : X.Etale ⥤ Z.Etale :=
  MorphismProperty.Over.pullback (@Etale) ⊤ f

variable (G : Type u) [Group G]

/-- Base change of the cover, its deck action, and every equivariant morphism. -/
def etaleTorsorPullbackFunctor : Action X.Etale G ⥤ Action Z.Etale G :=
  (etaleObjectPullback f).mapAction G

variable {G} (Y : Action X.Etale G)

/-- The structure morphism of the new cover is the second fiber projection. -/
@[simp] theorem etaleTorsorPullbackFunctor_obj_hom :
    ((etaleTorsorPullbackFunctor f G).obj Y).V.hom = pullback.snd Y.V.hom f := rfl

/-- The deck action is the original action on the first fiber coordinate. -/
@[reassoc (attr := simp)] theorem etaleTorsorPullbackFunctor_ρ_fst (g : G) :
    (((etaleTorsorPullbackFunctor f G).obj Y).ρ g).left ≫ pullback.fst Y.V.hom f =
      pullback.fst Y.V.hom f ≫ (Y.ρ g).left := by
  simp [etaleTorsorPullbackFunctor, etaleObjectPullback]

/-- Every pulled-back deck map fixes the second fiber coordinate. -/
@[reassoc (attr := simp)] theorem etaleTorsorPullbackFunctor_ρ_snd (g : G) :
    (((etaleTorsorPullbackFunctor f G).obj Y).ρ g).left ≫ pullback.snd Y.V.hom f =
      pullback.snd Y.V.hom f := by
  simp [etaleTorsorPullbackFunctor, etaleObjectPullback]

variable {Y}

/-- Base change of an equivariant cover morphism on the first coordinate. -/
@[reassoc (attr := simp)] theorem etaleTorsorPullbackFunctor_map_fst
    {Y' : Action X.Etale G} (a : Y ⟶ Y') :
    (((etaleTorsorPullbackFunctor f G).map a).hom).left ≫ pullback.fst Y'.V.hom f =
      pullback.fst Y.V.hom f ≫ a.hom.left := by
  simp [etaleTorsorPullbackFunctor, etaleObjectPullback]

/-- Base change of a cover morphism retains its second coordinate. -/
@[reassoc (attr := simp)] theorem etaleTorsorPullbackFunctor_map_snd
    {Y' : Action X.Etale G} (a : Y ⟶ Y') :
    (((etaleTorsorPullbackFunctor f G).map a).hom).left ≫ pullback.snd Y'.V.hom f =
      pullback.snd Y.V.hom f := by
  simp [etaleTorsorPullbackFunctor, etaleObjectPullback]

variable (Y)

/-- The genuine finite geometric torsor condition survives arbitrary scheme
base change; the free-transitive assertion follows from the two fiber projections. -/
theorem IsFiniteGeometricTorsor.pullback (hY : IsFiniteGeometricTorsor X Y) :
    IsFiniteGeometricTorsor Z ((etaleTorsorPullbackFunctor f G).obj Y) := by
  let : IsFinite Y.V.hom := hY.2.1
  let : Surjective Y.V.hom := ⟨hY.2.2.1⟩
  refine ⟨hY.1, inferInstanceAs (IsFinite (pullback.snd Y.V.hom f)),
    (pullback.snd Y.V.hom f).surjective, ?_⟩
  intro Ω _ _ a b hab
  change a ≫ pullback.snd Y.V.hom f = b ≫ pullback.snd Y.V.hom f at hab
  have hab' : (a ≫ pullback.fst Y.V.hom f) ≫ Y.V.hom =
      (b ≫ pullback.fst Y.V.hom f) ≫ Y.V.hom := by
    simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc, hab, Category.assoc]
  obtain ⟨g, hg, hu⟩ := hY.2.2.2 Ω
    (a ≫ pullback.fst Y.V.hom f) (b ≫ pullback.fst Y.V.hom f) hab'
  refine ⟨g, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa only [Category.assoc, etaleTorsorPullbackFunctor_ρ_fst] using hg
    · simpa only [Category.assoc, etaleTorsorPullbackFunctor_ρ_snd] using hab
  · intro h hh
    apply hu h
    have he := congrArg (fun k => k ≫ pullback.fst Y.V.hom f) hh
    simpa only [Category.assoc, etaleTorsorPullbackFunctor_ρ_fst] using he

variable (G)

/-- The canonical iterated fiber-product comparison is equivariant. -/
def etaleTorsorPullbackComp {V : Scheme.{u}} (g : V ⟶ Z) :
    etaleTorsorPullbackFunctor (g ≫ f) G ≅
      etaleTorsorPullbackFunctor f G ⋙ etaleTorsorPullbackFunctor g G :=
  Functor.mapActionCongr G (MorphismProperty.Over.pullbackComp g f) ≪≫
    Functor.mapActionComp G (etaleObjectPullback f) (etaleObjectPullback g)

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ GrpCat.{u})

/-- Base change of an entire varying-group cover diagram, preserving its
original group diagram and every transition. -/
def etaleTorsorDiagramPullback :
    EquivariantDiagram D X.Etale ⥤ EquivariantDiagram D Z.Etale :=
  EquivariantDiagram.mapFunctor (etaleObjectPullback f)

/-- At each index, diagram base change is the same constructed cover action. -/
@[simp] theorem etaleTorsorDiagramPullback_action
    (Y : EquivariantDiagram D X.Etale) (i : I) :
    ((etaleTorsorDiagramPullback f D).obj Y).action i =
      (etaleTorsorPullbackFunctor f (D.obj i)).obj (Y.action i) := rfl

/-- Every original equivariant cover transition is pulled back geometrically. -/
@[simp] theorem etaleTorsorDiagramPullback_transition_hom
    (Y : EquivariantDiagram D X.Etale) {i j : I} (a : i ⟶ j) :
    (((etaleTorsorDiagramPullback f D).obj Y).transition a).hom =
      (etaleObjectPullback f).map (Y.transition a).hom := rfl

/-- Every finite geometric torsor in the original diagram stays a finite
geometric torsor, with no restriction on the base morphism. -/
theorem etaleTorsorDiagramPullback_isFiniteGeometricTorsor
    (Y : EquivariantDiagram D X.Etale)
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) (i : I) :
    IsFiniteGeometricTorsor Z (((etaleTorsorDiagramPullback f D).obj Y).action i) :=
  (hY i).pullback f (Y.action i)

end Langlands.Shimura.Coefficients

import Langlands.Geometry.Analytic.EquivariantSitePullbacksReduction
import Langlands.Geometry.Analytic.QuasiEtaleBaseChangeReduction
import Langlands.Geometry.Analytic.RestrictionSiteMorphismReduction
import Langlands.Geometry.Analytic.SpacesWithOperators
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Pullback of equivariant analytic site objects along a morphism with operators -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G]

namespace GSpace

variable {A B X P : GSpace.{u, v, v} K G}

/-- An analytic pullback with a quasi-étale first leg has equivariant projections
from a Hausdorff space carrying the continuous diagonal action. -/
theorem exists_analyticPullback_of_quasiEtale (f : A ⟶ X) (g : B ⟶ X) (hf : quasiEtale f) :
    ∃ (Q : GSpace.{u, v, v} K G) (p : Q ⟶ A) (q : Q ⟶ B),
      IsPullback (forget.map p) (forget.map q) (forget.map f) (forget.map g) := by
  obtain ⟨Q, p, q, hQ⟩ := exists_localizedPullback_of_quasiEtale (forget.map f) (forget.map g) hf
  exact ⟨pullbackOfForget f g hQ hf, pullbackOfForgetFst f g hQ hf,
    pullbackOfForgetSnd f g hQ hf, hQ⟩

instance quasiEtale_hasPullbacks : (quasiEtale (K := K) (G := G)).HasPullbacks where
  hasPullback {A B X f} g hf := by
    obtain ⟨Q, p, q, hQ⟩ := exists_analyticPullback_of_quasiEtale f g hf
    exact (hQ.of_map_of_faithful forget).hasPullback

/-- Pullbacks of `G`-spaces along a quasi-étale first leg are computed in the
underlying analytic category. -/
theorem isPullback_forget_of_quasiEtale {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    (h : IsPullback p q f g) (hf : quasiEtale f) :
    IsPullback (forget.map p) (forget.map q) (forget.map f) (forget.map g) := by
  obtain ⟨Q, p', q', hQ⟩ := exists_analyticPullback_of_quasiEtale f g hf
  have h' : IsPullback p' q' f g := hQ.of_map_of_faithful forget
  let : PreservesLimit (cospan f g) (forget (K := K) (G := G)) :=
    preservesLimit_of_preserves_limit_cone h'.isLimit
      ((isLimitMapConePullbackConeEquiv forget h'.w).symm hQ.isLimit)
  exact h.map forget

instance quasiEtale_isStableUnderBaseChange :
    (quasiEtale (K := K) (G := G)).IsStableUnderBaseChange where
  of_isPullback {X Y P S f g p q} h hf := by
    let : T2Space (localizedSpaceFunctor.obj (forget.obj Y)) := Y.2.1
    exact quasiEtale_of_isPullback_of_t2Space (isPullback_forget_of_quasiEtale h hf) hf

instance etale_hasPullbacks : (etale (K := K) (G := G)).HasPullbacks where
  hasPullback g hf := MorphismProperty.hasPullback (P := quasiEtale) g (etale_le_quasiEtale _ hf)

instance etale_isStableUnderBaseChange :
    (etale (K := K) (G := G)).IsStableUnderBaseChange where
  of_isPullback h hf :=
    (localizedEtaleBaseChange (K := K)).of_isPullback
      (isPullback_forget_of_quasiEtale h (etale_le_quasiEtale _ hf)) hf

end GSpace

namespace SpaceWithOperators

variable {Y X : SpaceWithOperators.{u, v, v, z} K}

/-- A morphism with operators becomes equivariant for the source group after
restriction of the target action. -/
def restrictedHom (f : Y ⟶ X) : Y.space ⟶ (GSpace.res f.groupHom).obj X.space :=
  GSpace.homOfForget f.hom f.comm

@[simp] theorem forget_map_restrictedHom (f : Y ⟶ X) :
    GSpace.forget.map (restrictedHom f) = f.hom := rfl

/-- Pullback of étale site objects along a fixed-field morphism with operators. -/
def etalePullbackFunctor (f : Y ⟶ X) :
    EquivariantEtaleSite X.space ⥤ EquivariantEtaleSite Y.space :=
  EquivariantEtaleSite.res f.groupHom ⋙
    MorphismProperty.Over.pullback GSpace.etale ⊤ (restrictedHom f)

/-- Pullback of quasi-étale site objects along a fixed-field morphism with operators. -/
def quasiEtalePullbackFunctor (f : Y ⟶ X) :
    EquivariantQuasiEtaleSite X.space ⥤ EquivariantQuasiEtaleSite Y.space :=
  EquivariantQuasiEtaleSite.res f.groupHom ⋙
    MorphismProperty.Over.pullback GSpace.quasiEtale ⊤ (restrictedHom f)

/-- First projection of the pullback of an equivariant étale site object. -/
def etalePullbackProjection (f : Y ⟶ X) (U : EquivariantEtaleSite X.space) :
    ((etalePullbackFunctor f).obj U).left ⟶ (GSpace.res f.groupHom).obj U.left :=
  pullback.fst ((EquivariantEtaleSite.res f.groupHom).obj U).hom (restrictedHom f)

/-- First projection of the pullback of an equivariant quasi-étale site object. -/
def quasiEtalePullbackProjection (f : Y ⟶ X) (U : EquivariantQuasiEtaleSite X.space) :
    ((quasiEtalePullbackFunctor f).obj U).left ⟶ (GSpace.res f.groupHom).obj U.left :=
  pullback.fst ((EquivariantQuasiEtaleSite.res f.groupHom).obj U).hom (restrictedHom f)

/-- The étale base-change square is an analytic pullback. -/
theorem isPullback_etalePullbackFunctor (f : Y ⟶ X) (U : EquivariantEtaleSite X.space) :
    IsPullback (GSpace.forget.map (etalePullbackProjection f U))
      (GSpace.forget.map ((etalePullbackFunctor f).obj U).hom)
      ((GSpace.forget (G := X.group.carrier)).map U.hom) f.hom :=
  GSpace.isPullback_forget_of_quasiEtale
    (IsPullback.of_hasPullback ((EquivariantEtaleSite.res f.groupHom).obj U).hom (restrictedHom f))
    (GSpace.etale_le_quasiEtale _ U.prop)

/-- The quasi-étale base-change square is an analytic pullback. -/
theorem isPullback_quasiEtalePullbackFunctor (f : Y ⟶ X) (U : EquivariantQuasiEtaleSite X.space) :
    IsPullback (GSpace.forget.map (quasiEtalePullbackProjection f U))
      (GSpace.forget.map ((quasiEtalePullbackFunctor f).obj U).hom)
      ((GSpace.forget (G := X.group.carrier)).map U.hom) f.hom :=
  GSpace.isPullback_forget_of_quasiEtale
    (IsPullback.of_hasPullback ((EquivariantQuasiEtaleSite.res f.groupHom).obj U).hom
      (restrictedHom f)) U.prop

end SpaceWithOperators

end Langlands.Analytic.SaturatedAtlasPresentation

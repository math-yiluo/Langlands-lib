import Langlands.AlgebraicGeometry.Picard.RigidifiedClassDescentData
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesFlatSeparated
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation

/-! # Conditional effectivity for rigidified classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.ClassDescent

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S) {T U : Over S} (h : U ⟶ T)
  (L : relative f ε section_eq U)
  (compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
    Nonempty ((relativePullback f ε section_eq a).obj L ≅
      (relativePullback f ε section_eq b).obj L))

/-- The comparisons have exactly the naturality required by module descent. -/
lemma theta_precomp
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    (V W : Scheme.{u}) (k : W ⟶ V) (a b : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h)
    (hab' : (k ≫ a) ≫ (relativeSpace f).map h = (k ≫ b) ≫ (relativeSpace f).map h) :
    (theta f ε section_eq h L compat W (k ≫ a) (k ≫ b) hab').hom =
      (Scheme.Modules.pullbackComp k a).inv.app L.obj.carrier ≫
        (Scheme.Modules.pullback k).map (theta f ε section_eq h L compat V a b hab).hom ≫
          (Scheme.Modules.pullbackComp k b).hom.app L.obj.carrier := by
  have hka : (k ≫ a) ≫ (relativeSpace f).map h = k ≫ (a ≫ (relativeSpace f).map h) :=
    Category.assoc _ _ _
  have hkb : (k ≫ b) ≫ (relativeSpace f).map h = k ≫ (a ≫ (relativeSpace f).map h) := by
    rw [Category.assoc, hab]
  rw [theta_eq_common f ε section_eq h L compat _ (k ≫ a) (k ≫ b) hka hkb,
    theta_eq_common f ε section_eq h L compat _ a b rfl hab.symm,
    thetaCommon_precomp f ε section_eq h L compat unique k]
  rfl

include compat in
/-- Explicit module descent descends the ordinary carrier of the compatible class. -/
lemma exists_carrier
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    [IsAffineHom h.left] [Flat h.left] [Surjective h.left] :
    ∃ M : LineBundle ((relativeSpace f).obj T),
      Nonempty ((Scheme.Modules.pullback ((relativeSpace f).map h)).obj M.obj ≅
        L.obj.carrier) := by
  obtain ⟨M, hM, e⟩ := hD2 _ _ ((relativeSpace f).map h)
    (relativeSpace_map_isAffineHom f h) (relativeSpace_map_flat f h)
    (relativeSpace_map_surjective f h) L.obj.carrier L.property
    (theta f ε section_eq h L compat)
    (theta_precomp f ε section_eq h L compat unique)
    (theta_comp f ε section_eq h L compat unique)
  exact ⟨⟨M, hM⟩, e⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.ClassDescent

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S) {T U : Over S} (h : U ⟶ T)
  (L : relative f ε section_eq U) (M : LineBundle ((relativeSpace f).obj T))
  (e : (Scheme.Modules.pullback ((relativeSpace f).map h)).obj M.obj ≅ L.obj.carrier)

/-- The restriction of a descended carrier becomes trivial after the original base change. -/
def carrierRestrictionIso :
    (Scheme.Modules.pullback h.left).obj
        ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj M.obj) ≅
      structureSheaf U.left :=
  (relativeSectionPullbackIso f ε section_eq h M).symm ≪≫
    (Scheme.Modules.pullback ((relativeSection f ε section_eq).app U)).mapIso e ≪≫
      L.obj.rigidification.symm

/-- The inverse of the section restriction becomes trivial after base change. -/
def inverseRestrictionIso (N : LineBundle T.left)
    (ev : tensorObj
      ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj M.obj)
      N.obj ≅ structureSheaf T.left) :
    (Scheme.Modules.pullback h.left).obj N.obj ≅ structureSheaf U.left := by
  letI := pullbackTensorComparisonIsIso h.left
  exact (tensorLeftUnitor ((Scheme.Modules.pullback h.left).obj N.obj)).symm ≪≫
    (Langlands.Scheme.Modules.tensorFunctor U.left).mapIso
      ((carrierRestrictionIso f ε section_eq h L M e).symm.prod (Iso.refl _)) ≪≫
    ((asIso (pullbackTensorComparison h.left)).app
      (((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj M.obj),
        N.obj)).symm ≪≫
    (Scheme.Modules.pullback h.left).mapIso ev ≪≫ pullbackUnitIso h.left

/-- Pulling back the normalized carrier recovers the original ordinary carrier. -/
def normalizedCarrierIso (N : LineBundle T.left)
    (ev : tensorObj
      ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj M.obj)
      N.obj ≅ structureSheaf T.left) :
    (Scheme.Modules.pullback ((relativeSpace f).map h)).obj
      (LineBundle.normalize pullbackTensorComparisonIsIso
        ((relativeProjection f).app T) ((relativeSection f ε section_eq).app T)
        (relativeSection_projection f ε section_eq T) M N ev).obj.carrier ≅
      L.obj.carrier := by
  letI := pullbackTensorComparisonIsIso ((relativeSpace f).map h)
  let baseIso :
      (Scheme.Modules.pullback ((relativeSpace f).map h)).obj
        ((Scheme.Modules.pullback ((relativeProjection f).app T)).obj N.obj) ≅
        structureSheaf ((relativeSpace f).obj U) :=
    (Scheme.Modules.pullbackComp ((relativeSpace f).map h)
      ((relativeProjection f).app T)).app N.obj ≪≫
    (Scheme.Modules.pullbackCongr ((relativeProjection f).naturality h)).app N.obj ≪≫
    ((Scheme.Modules.pullbackComp ((relativeProjection f).app U) h.left).app N.obj).symm ≪≫
    (Scheme.Modules.pullback ((relativeProjection f).app U)).mapIso
      (inverseRestrictionIso f ε section_eq h L M e N ev) ≪≫
    pullbackUnitIso ((relativeProjection f).app U)
  exact (asIso (pullbackTensorComparison ((relativeSpace f).map h))).app
      (M.obj, (Scheme.Modules.pullback ((relativeProjection f).app T)).obj N.obj) ≪≫
    (Langlands.Scheme.Modules.tensorFunctor ((relativeSpace f).obj U)).mapIso
      (e.prod baseIso) ≪≫ tensorRightUnitor L.obj.carrier

include e in
/-- A descended ordinary carrier can always be normalized to descend its rigidified class. -/
lemma exists_rigidified_of_carrier :
    ∃ M' : relative f ε section_eq T,
      Nonempty ((relativePullback f ε section_eq h).obj M' ≅ L) := by
  obtain ⟨N, ⟨ev⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback ((relativeSection f ε section_eq).app T)).obj M)
  refine ⟨LineBundle.normalize pullbackTensorComparisonIsIso
    ((relativeProjection f).app T) ((relativeSection f ε section_eq).app T)
    (relativeSection_projection f ε section_eq T) M N ev, ⟨?_⟩⟩
  exact isoOfCarrierIso pullbackTensorComparisonIsIso
    ((relativeProjection f).app U) (relativeSection_projection f ε section_eq U)
    (normalizedCarrierIso f ε section_eq h L M e N ev)

/-- Effective ordinary line-bundle descent yields effective descent of rigidified classes. -/
lemma exists_rigidified_of_descent
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    [IsAffineHom h.left] [Flat h.left] [Surjective h.left]
    (compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
      Nonempty ((relativePullback f ε section_eq a).obj L ≅
        (relativePullback f ε section_eq b).obj L)) :
    ∃ M' : relative f ε section_eq T,
      Nonempty ((relativePullback f ε section_eq h).obj M' ≅ L) := by
  obtain ⟨M', ⟨e'⟩⟩ := ClassDescent.exists_carrier f ε section_eq h L compat hD2 unique
  exact exists_rigidified_of_carrier f ε section_eq h L M' e'

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroTensor

/-! # Elementary isomorphisms of line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- Successive pullbacks of one line bundle agree with pullback by a composite. -/
def pullbackCompEqIso (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    (L : LineBundle Z) :
    (pullback f).obj ((pullback g).obj L) ≅ (pullback h).obj L :=
  (pullbackComp f g).app L ≪≫ eqToIso (congrArg (fun k ↦ (pullback k).obj L) w)

/-- Pullbacks along equal morphisms agree. -/
def pullbackEqIso {f f' : X ⟶ Y} (w : f = f') (L : LineBundle Y) :
    (pullback f).obj L ≅ (pullback f').obj L :=
  eqToIso (congrArg (fun k ↦ (pullback k).obj L) w)

/-- Pullback along an isomorphism reflects isomorphism of line bundles. -/
def isoOfPullbackIso (i : X ⟶ Y) [IsIso i] {L M : LineBundle Y}
    (e : (pullback i).obj L ≅ (pullback i).obj M) : L ≅ M :=
  ((pullbackId Y).app L).symm ≪≫ (pullbackCompEqIso (inv i) i (IsIso.inv_hom_id i) L).symm ≪≫
    (pullback (inv i)).mapIso e ≪≫ pullbackCompEqIso (inv i) i (IsIso.inv_hom_id i) M ≪≫
    (pullbackId Y).app M

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- The explicit right unitor as an isomorphism of line bundles. -/
def tensorTrivialIso (L : LineBundle X) : tensor preservation L (trivial X) ≅ L :=
  ObjectProperty.isoMk _ (tensorRightUnitor L.obj)

/-- The explicit tensor symmetry as an isomorphism of line bundles. -/
def tensorCommIso (L M : LineBundle X) : tensor preservation L M ≅ tensor preservation M L :=
  ObjectProperty.isoMk _ (tensorComm L.obj M.obj)

/-- Tensoring with a line bundle isomorphic to the trivial one changes nothing up to
isomorphism. -/
def tensorIsoTrivialIso (L : LineBundle X) {M : LineBundle X} (e : M ≅ trivial X) :
    tensor preservation L M ≅ L :=
  tensorIso preservation (Iso.refl L) e ≪≫ tensorTrivialIso preservation L

end Langlands.AlgebraicGeometry.Picard.LineBundle

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

variable {X : Scheme.{u}}

/-- A line bundle trivialized on the whole space is trivial. -/
lemma nonempty_iso_trivial_of_restrict_top (L : LineBundle X) (U : X.Opens) (hU : U = ⊤)
    (e : L.obj.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty (L ≅ trivial X) := by
  subst hU
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  let e' : (pullback (⊤ : X.Opens).ι).obj L ≅ (pullback (⊤ : X.Opens).ι).obj (trivial X) :=
    ObjectProperty.isoMk _
      (((Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app L.obj).symm ≪≫ e) ≪≫
      (pullbackTrivialIso (⊤ : X.Opens).ι).symm
  exact ⟨isoOfPullbackIso (⊤ : X.Opens).ι e'⟩

/-- On a scheme with exactly one point every line bundle is trivial. -/
lemma nonempty_iso_trivial_of_unique [Unique X] (L : LineBundle X) :
    Nonempty (L ≅ trivial X) := by
  refine nonempty_iso_trivial_of_restrict_top L (L.trivializingOpen default) ?_
    (L.localTrivialization default)
  refine eq_top_iff.mpr (fun y _ ↦ ?_)
  rw [Subsingleton.elim y default]
  exact L.mem_trivializingOpen default

end Langlands.AlgebraicGeometry.Picard.LineBundle

import Langlands.GroupScheme.Descent.FiniteStageHom
import Langlands.GroupScheme.Torus.MaximalDescent
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Finite models of specified split-torus inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TorusFiniteModel

open Descent.FiniteStage
open Langlands.AlgebraicGeometry.Picard

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of Ω))}

/-- A finite model retains the specified torus inclusion and its exact recovery
in the ambient group after the canonical field-tower comparison. -/
structure Model
    (i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G) where
  fieldOfDefinition : FinIntermediateField k Ω
  torus : CommGroupScheme (Spec (CommRingCat.of fieldOfDefinition.1))
  inclusion : torus.toGrp ⟶
    (baseChange (algebraBaseMap k fieldOfDefinition.1)).obj G
  isSplitTorus : IsSplitTorus torus.toGrp
  isClosedSubgroup : IsClosedSubgroup inclusion
  recovery : (baseChange (algebraBaseMap fieldOfDefinition.1 Ω)).obj torus.toGrp ≅ T.toGrp
  comparison : (baseChange (algebraBaseMap fieldOfDefinition.1 Ω)).map inclusion =
    recovery.hom ≫ i ≫ (Descent.FiniteStage.comparison k Ω fieldOfDefinition G).hom

/-- A specified closed split torus over an algebraic extension has an actual
closed split-torus model over a finite intermediate field. -/
theorem nonempty_model [Algebra.IsAlgebraic k Ω]
    [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom]
    (i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) :
    Nonempty (Model k Ω i) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let S := splitTorus (Spec (CommRingCat.of k)) I
  have hs : IsSplitTorus S := isSplitTorus_splitTorus I
  let : IsAffineHom S.X.hom := hs.isAffineHom
  let : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  let a : (baseChange (algebraBaseMap k Ω)).obj S ≅ T.toGrp :=
    splitTorus.baseChangeIso (algebraBaseMap k Ω) I ≪≫ e.symm
  let f := a.hom ≫ i
  let D := homModel k Ω f
  let E := D.fieldOfDefinition
  let S₀ : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { S with comm := hs.isCommMonObj }
  let S₁ := (CommGroupScheme.baseChange (algebraBaseMap k E.1)).obj S₀
  let r : (baseChange (algebraBaseMap E.1 Ω)).obj S₁.toGrp ≅ T.toGrp :=
    (Descent.FiniteStage.comparison k Ω E S).symm ≪≫ a
  refine ⟨⟨E, S₁, D.hom, hs.baseChange (algebraBaseMap k E.1),
    D.isClosedSubgroup (hi.iso_comp a), r, ?_⟩⟩
  apply (cancel_epi (Descent.FiniteStage.comparison k Ω E S).hom).mp
  simpa only [r, f, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using D.recovery

/-- Choose a finite split-torus model of the specified inclusion. -/
def model [Algebra.IsAlgebraic k Ω]
    [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom]
    (i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) : Model k Ω i :=
  Classical.choice (nonempty_model k Ω i hT hi)

variable {k Ω}
variable {i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G}

/-- Exact recovery transfers maximality to the actual extension of the finite
model, without using forward preservation of arbitrary maximal tori. -/
theorem Model.isMaximalTorus_baseChange (D : Model k Ω i) (hi : IsMaximalTorus i) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange
      (algebraBaseMap D.fieldOfDefinition.1 Ω)).obj D.torus)
      ((baseChange (algebraBaseMap D.fieldOfDefinition.1 Ω)).map D.inclusion) := by
  rw [D.comparison]
  exact (hi.comp_iso (Descent.FiniteStage.comparison k Ω D.fieldOfDefinition G)).iso_comp
    (T' := (CommGroupScheme.baseChange
      (algebraBaseMap D.fieldOfDefinition.1 Ω)).obj D.torus) D.recovery

/-- The finite model is itself maximal by independent field-extension
reflection. -/
theorem Model.isMaximalTorus (D : Model k Ω i) (hi : IsMaximalTorus i) :
    IsMaximalTorus D.inclusion :=
  IsMaximalTorus.of_baseChange D.isClosedSubgroup (D.isMaximalTorus_baseChange hi)

end Langlands.GroupScheme.TorusFiniteModel

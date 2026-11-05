import Langlands.GroupScheme.Descent.FiniteStageHom
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.CorepresentedComultiplication

/-! # Centrality at finite fields of definition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent.FiniteStage

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {f : (baseChange (algebraBaseMap k K)).obj G ⟶
      (baseChange (algebraBaseMap k K)).obj H}

/-- Finite fields of definition retain centrality of the original homomorphism. -/
theorem HomModel.isCentral (D : HomModel k K f) (hf : IsCentral f) :
    IsCentral D.hom := by
  let E := D.fieldOfDefinition
  let q := algebraBaseMap E.1 K
  let : Flat q := (fieldExtension_fpqc E.1 K).2.1
  let : Surjective q := (fieldExtension_fpqc E.1 K).1
  apply IsCentral.of_baseChange q
  have hmap : (baseChange q).map D.hom =
      (comparison k K E G).inv ≫ f ≫ (comparison k K E H).hom := by
    apply (cancel_epi (comparison k K E G).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using D.recovery
  rw [hmap]
  exact (hf.comp_iso (comparison k K E H)).comp (comparison k K E G).inv

/-- A chosen finite model of a central closed homomorphism retains both
properties, as well as its exact recovery equation. -/
def centralClosedHomModel [Algebra.IsAlgebraic k K]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    [IsAffine G.X.left] [IsAffine H.X.left]
    (f : (baseChange (algebraBaseMap k K)).obj G ⟶
      (baseChange (algebraBaseMap k K)).obj H)
    (hf : IsClosedSubgroup f) (hc : IsCentral f) :
    {D : HomModel k K f // IsClosedSubgroup D.hom ∧ IsCentral D.hom} :=
  let D := homModel k K f
  ⟨D, D.isClosedSubgroup hf, D.isCentral hc⟩

end Descent.FiniteStage

end Langlands.GroupScheme

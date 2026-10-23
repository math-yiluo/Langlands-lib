import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundleTensor

/-! # Normalizing a line bundle along a section -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
    (section_eq : ε ≫ f = 𝟙 S)

/-- Pulling a base module back along the structure map and its section recovers it. -/
def sectionBasePullbackIso (M : S.Modules) :
    (Scheme.Modules.pullback ε).obj ((Scheme.Modules.pullback f).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp ε f).app M ≪≫
    (Scheme.Modules.pullbackCongr section_eq).app M ≪≫
      (Scheme.Modules.pullbackId S).app M

/-- Trivialize the restriction of `L ⊗ f* M` using an actual evaluation
`ε* L ⊗ M ≅ O_S`. -/
def normalizationTrivialization (L : LineBundle X) (M : LineBundle S)
    (evaluation :
      tensorObj ((Scheme.Modules.pullback ε).obj L.obj) M.obj ≅ structureSheaf S) :
    (Scheme.Modules.pullback ε).obj
      (tensor preservation L ((pullback f).obj M)).obj ≅ structureSheaf S := by
  letI := preservation ε
  exact (asIso (pullbackTensorComparison ε)).app
      (L.obj, (Scheme.Modules.pullback f).obj M.obj) ≪≫
    (Langlands.Scheme.Modules.tensorFunctor S).mapIso
      ((Iso.refl _).prod (sectionBasePullbackIso f ε section_eq M.obj)) ≪≫
    evaluation

/-- Normalize an ordinary line bundle along a section using a supplied inverse
of its restriction and the actual evaluation isomorphism. -/
def normalize (L : LineBundle X) (M : LineBundle S)
    (evaluation :
      tensorObj ((Scheme.Modules.pullback ε).obj L.obj) M.obj ≅ structureSheaf S) :
    RigidifiedLineBundle ε :=
  RigidifiedLineBundle.ofLineBundle (tensor preservation L ((pullback f).obj M))
    (normalizationTrivialization preservation f ε section_eq L M evaluation).symm

/-- The underlying normalized bundle includes the required base factor. -/
lemma normalize_forget (L : LineBundle X) (M : LineBundle S)
    (evaluation :
      tensorObj ((Scheme.Modules.pullback ε).obj L.obj) M.obj ≅ structureSheaf S) :
    (RigidifiedLineBundle.forget ε).obj
        (normalize preservation f ε section_eq L M evaluation) =
      tensor preservation L ((pullback f).obj M) := rfl

/-- The constructed rigidification is inverse to the actual restriction trivialization. -/
lemma normalize_rigidification_comp (L : LineBundle X) (M : LineBundle S)
    (evaluation :
      tensorObj ((Scheme.Modules.pullback ε).obj L.obj) M.obj ≅ structureSheaf S) :
    (normalize preservation f ε section_eq L M evaluation).obj.rigidification.hom ≫
        (normalizationTrivialization preservation f ε section_eq L M evaluation).hom =
      𝟙 (structureSheaf S) :=
  (normalizationTrivialization preservation f ε section_eq L M evaluation).inv_hom_id

end Langlands.AlgebraicGeometry.Picard.LineBundle

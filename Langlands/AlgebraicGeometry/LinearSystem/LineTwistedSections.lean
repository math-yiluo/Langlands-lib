import Langlands.AlgebraicGeometry.Picard.LineBundleDualSectionEvaluation
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio

/-! # Global sections twisted by the dual of a line bundle from the base -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {X S T : Scheme.{u}}

/-- Tensoring a zero morphism with the identity of a line bundle gives zero. -/
lemma tensorMap_zero_id {A A' : X.Modules} (B : X.Modules) (hB : IsLocallyFreeRankOne B) :
    tensorMap (0 : A ⟶ A') (𝟙 B) = 0 := by
  have := Langlands.AlgebraicGeometry.Modules.tensorBy_isEquivalence B hB
  exact (Langlands.AlgebraicGeometry.Modules.tensorBy B).map_zero A A'

/-- Tensors of isomorphisms are isomorphisms. -/
instance isIso_tensorMap {A A' B B' : X.Modules} (a : A ⟶ A') (b : B ⟶ B') [IsIso a]
    [IsIso b] : IsIso (tensorMap a b) :=
  inferInstanceAs (IsIso ((tensorFunctor X).mapIso ((asIso a).prod (asIso b))).hom)

/-- Pullback of a morphism tensored with an identity, in terms of the canonical tensor
comparison isomorphisms. -/
lemma pullback_map_tensorMap_id (f : T ⟶ X) {A A' : X.Modules} (α : A ⟶ A') (B : X.Modules) :
    (Scheme.Modules.pullback f).map (tensorMap α (𝟙 B)) =
      pullbackTensorComparisonApp f A B ≫
        tensorMap ((Scheme.Modules.pullback f).map α) (𝟙 _) ≫
          inv (pullbackTensorComparisonApp f A' B) := by
  rw [← Category.assoc, IsIso.eq_comp_inv, pullbackTensorComparisonApp_naturality,
    CategoryTheory.Functor.map_id]

/-- The coevaluation of a line bundle: the inverse of evaluation on its dual. -/
def lineCoevaluation (Λ : LineBundle S) :
    structureSheaf S ⟶ tensorObj Λ.obj (Langlands.Scheme.Modules.dual Λ.obj) :=
  haveI := isIso_dualTensorEval Λ.property
  inv (dualTensorEval Λ.obj)

instance (Λ : LineBundle S) : IsIso (lineCoevaluation Λ) := by
  dsimp only [lineCoevaluation]
  infer_instance

variable (p : X ⟶ S) {L : X.Modules} (Λ : LineBundle S)

/-- The pullback of the coevaluation, from the structure sheaf to the tensor of the pulled
back line bundle and of its pulled back dual. -/
def pulledCoevaluation :
    structureModule X ⟶ tensorObj ((Scheme.Modules.pullback p).obj Λ.obj)
      ((Scheme.Modules.pullback p).obj (Langlands.Scheme.Modules.dual Λ.obj)) :=
  (pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map (lineCoevaluation Λ) ≫
    pullbackTensorComparisonApp p Λ.obj (Langlands.Scheme.Modules.dual Λ.obj)

instance : IsIso (pulledCoevaluation p Λ) := by
  dsimp only [pulledCoevaluation]
  infer_instance

/-- The section morphism attached to `α : p^*Λ ⟶ L`, with values in `L ⊗ p^*Λ^∨`. -/
def twistedHom (α : (Scheme.Modules.pullback p).obj Λ.obj ⟶ L) :
    structureModule X ⟶
      tensorObj L ((Scheme.Modules.pullback p).obj (Langlands.Scheme.Modules.dual Λ.obj)) :=
  pulledCoevaluation p Λ ≫ tensorMap α (𝟙 _)

/-- The global section of `L ⊗ p^*Λ^∨` attached to `α : p^*Λ ⟶ L`. -/
def twistedSection (α : (Scheme.Modules.pullback p).obj Λ.obj ⟶ L) :
    GlobalSections
      (tensorObj L ((Scheme.Modules.pullback p).obj (Langlands.Scheme.Modules.dual Λ.obj))) :=
  (twistedHom p Λ α).app ⊤ (1 : Γ(X, ⊤))

lemma sectionHom_pullbackSection_twistedSection (f : T ⟶ X)
    (α : (Scheme.Modules.pullback p).obj Λ.obj ⟶ L) :
    sectionHom _ (pullbackSection f _ (twistedSection p Λ α)) =
      (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (pulledCoevaluation p Λ) ≫
        pullbackTensorComparisonApp f _ _ ≫
          tensorMap ((Scheme.Modules.pullback f).map α) (𝟙 _) ≫
            inv (pullbackTensorComparisonApp f _ _) := by
  rw [sectionHom_pullbackSection, pullbackSectionHom, twistedSection,
    Langlands.AlgebraicGeometry.Picard.sectionHom_app_top_one,
    twistedHom, Functor.map_comp, pullback_map_tensorMap_id]

/-- The pullback of a twisted section along `f` only depends on the pullback of `α`
along `f`. -/
lemma pullbackSection_twistedSection_congr (f : T ⟶ X)
    {α α' : (Scheme.Modules.pullback p).obj Λ.obj ⟶ L}
    (h : (Scheme.Modules.pullback f).map α = (Scheme.Modules.pullback f).map α') :
    pullbackSection f _ (twistedSection p Λ α) = pullbackSection f _ (twistedSection p Λ α') := by
  apply sectionHom_injective
  rw [sectionHom_pullbackSection_twistedSection, sectionHom_pullbackSection_twistedSection, h]

/-- A twisted section vanishes along `f` when the pullback of `α` along `f` is zero. -/
lemma pullbackSection_twistedSection_eq_zero (f : T ⟶ X)
    {α : (Scheme.Modules.pullback p).obj Λ.obj ⟶ L}
    (h : (Scheme.Modules.pullback f).map α = 0) :
    pullbackSection f _ (twistedSection p Λ α) = 0 := by
  apply sectionHom_injective
  rw [sectionHom_pullbackSection_twistedSection, h,
    tensorMap_zero_id ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj
      (Langlands.Scheme.Modules.dual Λ.obj))) ((LineBundle.pullback f).obj
      ((LineBundle.pullback p).obj Λ.dual)).property]
  simp only [Limits.zero_comp, Limits.comp_zero]
  exact (sectionHom_zero (M := _)).symm

/-- A twisted section trivializes its bundle along `f` when the pullback of `α` along
`f` is an isomorphism. -/
lemma trivializationOpen_pullbackSection_twistedSection (f : T ⟶ X)
    {α : (Scheme.Modules.pullback p).obj Λ.obj ⟶ L}
    (h : IsIso ((Scheme.Modules.pullback f).map α)) :
    trivializationOpen _ (pullbackSection f _ (twistedSection p Λ α)) = ⊤ := by
  apply trivializationOpen_eq_top_of_isIso
  rw [sectionHom_pullbackSection_twistedSection]
  infer_instance

end Langlands.AlgebraicGeometry.LinearSystem

import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Restriction of an actual subgroup family to an open parameter scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T : Over S}
variable {K : GroupScheme M.left}

/-- The actual open subscheme of a parameter scheme, viewed over the original base. -/
def openParameter (U : M.left.Opens) : Over S :=
  Over.mk (U.ι ≫ M.hom)

/-- The open parameter inclusion over the original base. -/
def openParameterMap (U : M.left.Opens) : openParameter U ⟶ M :=
  Over.homMk U.ι rfl

instance (U : M.left.Opens) : Mono (openParameterMap U) := by
  have : Mono (openParameterMap U).left := by
    change Mono U.ι
    infer_instance
  exact Over.mono_of_mono_left _

/-- Lift a parameter morphism whose image lies in the chosen open subset. -/
def openParameterLift (U : M.left.Opens) (a : T ⟶ M)
    (ha : Set.range a.left ⊆ U) : T ⟶ openParameter U := by
  let l : T.left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι a.left (by rwa [Scheme.Opens.range_ι])
  refine Over.homMk l ?_
  change l ≫ (U.ι ≫ M.hom) = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact Over.w a

@[simp]
theorem openParameterLift_fac (U : M.left.Opens) (a : T ⟶ M)
    (ha : Set.range a.left ⊆ U) :
    openParameterLift U a ha ≫ openParameterMap U = a := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Restricting an actual family and then evaluating agrees with evaluation
at the original parameter morphism. -/
theorem evaluate_openParameter
    (j : K ⟶ (baseChange M.hom).obj G) (U : M.left.Opens)
    (a : T ⟶ openParameter U) :
    evaluate (familyHom j (openParameterMap U)) a =
      evaluate j (a ≫ openParameterMap U) :=
  evaluate_comp j (openParameterMap U) a

/-- An open part of a smooth parameter scheme is smooth over the base. -/
theorem smooth_openParameter (U : M.left.Opens) [Smooth M.hom] :
    Smooth (openParameter U).hom := by
  change Smooth (U.ι ≫ M.hom)
  infer_instance

/-- A closed open part of a proper parameter scheme is proper over the base. -/
theorem isProper_openParameter (U : M.left.Opens) (hU : IsClosed (U : Set M.left))
    [IsProper M.hom] : IsProper (openParameter U).hom := by
  let : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by rwa [Scheme.Opens.range_ι])
  change IsProper (U.ι ≫ M.hom)
  infer_instance

/-- A uniquely classified subgroup whose classifying parameter lies in an open
subset is uniquely classified by the restricted actual family. -/
theorem existsUnique_evaluate_openParameter
    (j : K ⟶ (baseChange M.hom).obj G) (U : M.left.Opens)
    (F : SubgroupFunctor ((baseChange T.hom).obj G))
    (huni : ∃! a : T ⟶ M, evaluate j a = F)
    (himage : ∀ a : T ⟶ M, evaluate j a = F → Set.range a.left ⊆ U) :
    ∃! a : T ⟶ openParameter U,
      evaluate (familyHom j (openParameterMap U)) a = F := by
  obtain ⟨a, ha, hu⟩ := huni
  refine ⟨openParameterLift U a (himage a ha), ?_, ?_⟩
  · change evaluate (familyHom j (openParameterMap U)) _ = F
    rw [evaluate_openParameter, openParameterLift_fac, ha]
  · intro b hb
    apply (cancel_mono (openParameterMap U)).mp
    rw [openParameterLift_fac]
    exact hu _ ((evaluate_openParameter j U b).symm.trans hb)

end Langlands.GroupScheme.TorusSubgroupModuli

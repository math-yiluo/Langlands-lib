import Langlands.Sheaf.Equivariant.TwistedGodementPointProduct
import Langlands.Sheaf.Equivariant.TwistedCompactComparison

/-! # Exactness of the locally discrete Godement functor on a twisted site -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits LocalActionSystem

universe u v uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasAdmissibleRefinements (twistedTopology ρ J)]
variable {I : Type w} (points : I → J.Point.{w})
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

local notation "inc" => L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J)

/-- The degree-zero Godement functor of the locally discrete sheaves for the given
local action system. -/
abbrev smoothGodementZero :=
  exactZeroFunctor ρ J points R inc (LocalActionSystem.smoothCoreflector L (twistedTopology ρ J))

local notation "Z₀" => smoothGodementZero ρ J L points R

variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

private instance smoothGodementCoefficientFunctor_preservesEpimorphisms :
    (smoothGodementCoefficientFunctor ρ J L points R).PreservesEpimorphisms where
  preserves f _ := by
    have (i : Discrete I) : Epi (((smoothGodementCoefficientFunctor ρ J L points R).map f).app i) := by
      change Epi ((points i.as).sheafFiber.map ((inc ⋙ restriction ρ J (ModuleCat.{w} R)).map f))
      infer_instance
    exact NatTrans.epi_of_epi_app _

variable [HasSheafify J (ModuleCat.{w} R)]

/-- The locally discrete Godement functor preserves epimorphisms. Its underlying
ordinary sheaf is the exact restricted point product applied to its point fibres. -/
instance smoothGodementZero_preservesEpimorphisms : (Z₀).PreservesEpimorphisms := by
  have : (Z₀ ⋙ inc ⋙ restriction ρ J (ModuleCat.{w} R)).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (restrictedSmoothGodementPointProductIso ρ J L points R).symm
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects Z₀ (inc ⋙ restriction ρ J (ModuleCat.{w} R))

variable [LocallySmall.{w} (P.Over ⊤ X)]

omit [HasSheafify J (ModuleCat.{w} R)] in
/-- The locally discrete Godement functor is left exact. -/
instance smoothGodementZero_preservesFiniteLimits : PreservesFiniteLimits Z₀ := by
  have : (LocalActionSystem.smoothCoreflector (R := R) L (twistedTopology ρ J)).IsRightAdjoint :=
    (LocalActionSystem.smoothAdjunction (R := R) L (twistedTopology ρ J)).isRightAdjoint
  let e := (piEquivalenceFunctorDiscrete I (ModuleCat.{w} R)).functor
  let F := PointProduct.fiberFunctor points (ModuleCat.{w} R)
  have : PreservesFiniteLimits (F ⋙ e) := preservesFiniteLimits_of_evaluation _ fun i =>
    inferInstanceAs (PreservesFiniteLimits ((points i.as).sheafFiber (A := ModuleCat.{w} R)))
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F e
  have : PreservesFiniteLimits (Langlands.Sheaf.Godement.zeroFunctor points (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso (PointProduct.godementZeroIso points (ModuleCat.{w} R)).symm
  dsimp only [smoothGodementZero, exactZeroFunctor, twistedZeroFunctor]
  infer_instance

omit [HasSheafify J (ModuleCat.{w} R)] in
instance smoothGodementZero_additive : (Z₀).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The locally discrete Godement functor is exact. -/
instance smoothGodementZero_preservesHomology : (Z₀).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The locally discrete Godement functor preserves finite colimits. -/
instance smoothGodementZero_preservesFiniteColimits : PreservesFiniteColimits Z₀ :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Langlands.Sheaf.Equivariant.TwistedOver

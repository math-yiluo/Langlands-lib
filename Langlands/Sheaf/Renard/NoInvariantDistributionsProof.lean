import Langlands.Sheaf.Renard.CoinvariantStatements
import Langlands.Sheaf.Renard.FibreCoinvariantProof

/-!
# Renard III.3.1 Corollary: vanishing of invariant distributions

Reduction of the distribution Corollary to the fibre Proposition, through the
original coinvariant module of compact sections and its projector sheaf, and the
closed Corollary from the published fibre Proposition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.NoInvariantDistributionsProof

open CategoryTheory Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.SectionActions

/-- If every invariant linear form vanishes, the coinvariants are trivial. -/
theorem coinvariants_subsingleton_of_forall_invariant_eq_zero
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (h : ∀ T : Module.Dual ℂ V, (∀ (g : G) (v : V), T (ρ g v) = T v) → T = 0) :
    Subsingleton (Representation.Coinvariants ρ) := by
  have key : ∀ z : Representation.Coinvariants ρ, z = 0 := by
    intro z
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ z]
    intro φ
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ z
    have hT := h (φ ∘ₗ Representation.Coinvariants.mk ρ) (fun g v => by
      simp only [LinearMap.coe_comp, Function.comp_apply,
        Representation.Coinvariants.mk_self_apply])
    exact LinearMap.congr_fun hT v
  exact ⟨fun a b => (key a).trans (key b).symm⟩

variable {G : Type} [Group G] [TopologicalSpace G]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [ContinuousSMul G X]

/-- Fibrewise vanishing of invariant distributions makes the fibre coinvariants trivial. -/
theorem fibreCoinvariants_subsingleton (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x) (y : Y) (F : ActionSheaf G X)
    (h : letI := InvariantFibres.fibreAction q hq y
      letI := InvariantFibres.fibreContinuousSMul q hq y
      ∀ T : Distribution ((InvariantFibres.restriction q hq y).obj F),
        IsInvariantDistribution ((InvariantFibres.restriction q hq y).obj F) T → T = 0) :
    Subsingleton ((InvariantFibres.coinvariants q hq y).obj F) := by
  let _ := InvariantFibres.fibreAction q hq y
  let _ := InvariantFibres.fibreContinuousSMul q hq y
  exact coinvariants_subsingleton_of_forall_invariant_eq_zero _ h

/-- A nondegenerate target-test module whose projector sheaf has trivial stalks is trivial. -/
theorem module_subsingleton_of_stalks (hY : Langlands.Topology.IsLocallyProfinite Y)
    {M : Type} [AddCommGroup M] [NonUnitalModule (PointwiseTestAlgebra.Carrier Y) M]
    (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier Y) M)
    (h : ∀ y : Y, Subsingleton ((ProjectorVectorSheaf.presheaf.{0, 0} hY hM).stalk y)) :
    Subsingleton M := by
  let _ := ProjectorVectorSheaf.originalModule hM
  have key : ∀ m : M, m = 0 := by
    intro m
    have hs : ProjectorVectorSheaf.originalSection.{0, 0} hY hM ⊤ m =
        ProjectorVectorSheaf.originalSection.{0, 0} hY hM ⊤ 0 := by
      apply TopCat.Presheaf.section_ext (ProjectorVectorSheaf.sheaf.{0, 0} hY hM) ⊤
      intro y _
      exact (h y).elim _ _
    obtain ⟨K, hK⟩ := ProjectorVectorSheaf.exists_compactOpen_action_eq hY hM m
    have hc := congrArg (fun s => (s.val ⟨K, le_top⟩).val) hs
    change ProjectorBasisSheaf.action hY M K m = ProjectorBasisSheaf.action hY M K 0 at hc
    rw [map_zero, hK] at hc
    exact hc
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- Renard III.3.1 Corollary, conditional on the fibre Proposition. -/
theorem noInvariantDistributions_of_fibreCoinvariant
    (hfib : CoinvariantStatements.FibreCoinvariantStatement) :
    CoinvariantStatements.NoInvariantDistributionsStatement := by
  intro G _ _ _ hG X Y _ _ _ _ hX q hq hY F hfibres T hT
  have hstalk : ∀ y : Y, Subsingleton
      ((ProjectorVectorSheaf.presheaf.{0, 0} hY
        ((CoinvariantSheaf.modules hX q hq hY).obj F).property).stalk y) := by
    intro y
    obtain ⟨e⟩ := hfib G hG X Y hX q hq hY y
    have := fibreCoinvariants_subsingleton q hq y F (hfibres y)
    have hinj : Function.Injective (e.hom.app F).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hinj.subsingleton
  let _ := NondegenerateScalars.module ℂ PointwiseTestAlgebra.isIdempotented
    (CompactSectionActions.moduleObject hX F).property
  have hmod := module_subsingleton_of_stalks hY
    ((CoinvariantSheaf.modules hX q hq hY).obj F).property hstalk
  let T' : (CompactSectionActions.moduleObject hX F).obj →ₗ[ℂ] ℂ :=
    { toFun := fun s => T s
      map_add' := fun s t => map_add T s t
      map_smul' := fun c s =>
        (congrArg T (CompactSectionActions.canonicalScalar_eq hX F c s)).trans
          (map_smul T c (show CompactSupport.submodule
            (Langlands.Sheaf.Equivariant.CompactSections.ordinary F.obj) from s)) }
  have hT' : ∀ g, T' ∘ₗ CompactSectionActions.canonicalAction hX F g = T' := fun g =>
    LinearMap.ext fun s => hT g s
  ext s
  change T' s = 0
  have h1 : Representation.Coinvariants.mk (CompactSectionActions.canonicalAction hX F) s = 0 :=
    @Subsingleton.elim _ hmod _ _
  exact (Representation.Coinvariants.lift_mk _ T' hT' s).symm.trans
    ((congrArg (Representation.Coinvariants.lift _ T' hT') h1).trans (map_zero _))

end Langlands.Sheaf.Renard.NoInvariantDistributionsProof

namespace Langlands.Sheaf.Renard.CoinvariantStatements

/-- Renard III.3.1 Corollary: if every fibre restriction has no nonzero invariant
distribution, then neither does the original action sheaf. -/
theorem noInvariantDistributionsStatement : NoInvariantDistributionsStatement :=
  NoInvariantDistributionsProof.noInvariantDistributions_of_fibreCoinvariant
    fibreCoinvariantStatement

end Langlands.Sheaf.Renard.CoinvariantStatements

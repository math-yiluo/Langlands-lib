import Langlands.Sheaf.Renard.InductionSheaf
import Langlands.Sheaf.Renard.ProjectorActionStalks
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Topology.LocallyProfiniteProof

/-!
# The identity-coset stalk of Renard's induction sheaf

Evaluation at the identity and the original-vector germ at the identity coset
are two surjections from the same compactly induced functions with the same
kernel. They identify every smooth coefficient representation, naturally and
equivariantly, with the original stalk of its induction sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.HomogeneousOriginStalk

open CategoryTheory
open Langlands.Induction Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.ProjectorBasisSheaf

attribute [local instance] homogeneousAction

section Evaluation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)
variable {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H V)

/-- Evaluation of an original compactly induced function at the identity. -/
def evalOne : CompactFunctions H σ →ₗ[ℂ] V where
  toFun f := eval H σ f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalOne_apply (f : CompactFunctions H σ) : evalOne H σ f = eval H σ f.val 1 := rfl

/-- Right translation by an element of `H`, then evaluation at the identity,
is the coefficient action. -/
theorem evalOne_compactInduced (h : H) (f : CompactFunctions H σ) :
    evalOne H σ (compactInduced H σ h f) = σ h (evalOne H σ f) := by
  change eval H σ f.val (1 * (h : G)) = σ h (eval H σ f.val 1)
  rw [one_mul, ← eval_covariant, mul_one]

/-- Evaluation at the identity is natural for the original induced maps. -/
theorem evalOne_compactInducedMap {W : Type} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (T : σ.IntertwiningMap τ) (f : CompactFunctions H σ) :
    evalOne H τ (compactInducedMap H T f) = T (evalOne H σ f) := rfl

/-- For smooth coefficients every vector is the identity value of a compactly induced
function. -/
theorem evalOne_surjective (hG : Langlands.Topology.IsLocallyProfinite G)
    (hσ : IsSmooth σ) : Function.Surjective (evalOne H σ) := by
  let : NonarchimedeanGroup G :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨K, _, hKU⟩ :=
          ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).1 hG).2 U hU
        exact ⟨K, hKU⟩ }
  let := hG.locallyCompactSpace
  intro v
  exact ⟨compactLocalSection H σ hσ 1 v Set.univ isOpen_univ trivial,
    compactLocalSection_apply H σ hσ 1 v Set.univ isOpen_univ trivial⟩

variable [LocallyCompactSpace G] (hH : IsClosed (H : Set G))
variable (hXq : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))

/-- The original characteristic test of a compact open multiplies values pointwise. -/
theorem eval_action (K : CompactOpen hXq) (f : CompactFunctions H σ) (g : G) :
    eval H σ (action hXq (CompactInductionTestModule.moduleObject H hH σ).obj K f).val g =
      (K.obj : Set (LeftQuotient H)).indicator (fun _ => (1 : ℂ)) (quotientMap H g) •
        eval H σ f.val g := rfl

/-- The identity value vanishes exactly when a compact-open neighborhood test of the
identity coset kills the function. -/
theorem evalOne_eq_zero_iff (f : CompactFunctions H σ) :
    evalOne H σ f = 0 ↔ ∃ K : CompactOpen hXq, origin H ∈ K.obj ∧
      action hXq (CompactInductionTestModule.moduleObject H hH σ).obj K f = 0 := by
  have hiff := quotientMap_mem_quotientSupport_iff_of_covariant H σ (eval H σ f.val)
    (fun h x => eval_covariant H σ f.val h x)
  constructor
  · intro hf
    have hS : IsOpen (quotientSupport H (eval H σ f.val))ᶜ :=
      (isClosed_quotientSupport H σ f.val).isOpen_compl
    have ho : origin H ∈ (quotientSupport H (eval H σ f.val))ᶜ :=
      fun h => (hiff 1).1 h hf
    obtain ⟨K, hoK, hKS⟩ := (compactOpenBasis hXq).exists_subset ⟨_, hS⟩ ho
    refine ⟨K, hoK, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (K.obj : Set (LeftQuotient H)).indicator (fun _ => (1 : ℂ)) (quotientMap H g) •
      eval H σ f.val g = 0
    by_cases hg : eval H σ f.val g = 0
    · rw [hg, smul_zero]
    · have hgK : quotientMap H g ∉ (K.obj : Set (LeftQuotient H)) :=
        fun h => hKS h ((hiff g).2 hg)
      rw [Set.indicator_of_notMem hgK, zero_smul]
  · rintro ⟨K, hoK, hK⟩
    have h1 := congrArg (fun k : CompactFunctions H σ => eval H σ k.val 1) hK
    change (K.obj : Set (LeftQuotient H)).indicator (fun _ => (1 : ℂ)) (quotientMap H 1) •
      eval H σ f.val 1 = 0 at h1
    rw [Set.indicator_of_mem (show quotientMap H 1 ∈ (K.obj : Set (LeftQuotient H)) from hoK),
      one_smul] at h1
    exact h1

end Evaluation

section Germ

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (hG : Langlands.Topology.IsLocallyProfinite G)
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

/-- The original compact-induced compatible action of a smooth coefficient representation. -/
abbrev inducedAction (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    CompatibleTestAction.{0, 0, 0} G (LeftQuotient H) :=
  letI := hG.locallyCompactSpace
  CompactInductionTestModule.compatibleObject H hH A.representation

/-- The original-vector germ at the identity coset, on the original induced functions. -/
def germOne (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    CompactFunctions H A.representation →ₗ[ℂ]
      (CompactSections.ordinary ((InductionSheaf.functor hG H hH).obj A).obj.obj).stalk
        (origin H) :=
  letI := hG.locallyCompactSpace
  { toFun := fun f => ProjectorActionStalks.originalGerm (quotient_isLocallyProfinite H hG hH)
      (inducedAction hG H hH A) (origin H) f
    map_add' := fun f k => map_add (ProjectorActionStalks.originalGerm
      (quotient_isLocallyProfinite H hG hH) (inducedAction hG H hH A) (origin H)) f k
    map_smul' := fun c f => by
      rw [← CompactInductionTestModule.canonicalScalar_eq H hH A.representation c f]
      let := (inducedAction hG H hH A).complexModule
      exact LinearMap.map_smul (ProjectorActionStalks.originalGerm
        (quotient_isLocallyProfinite H hG hH) (inducedAction hG H hH A) (origin H)) c f }

theorem germOne_apply (A : Langlands.SmoothRep.{0, 0, 0} ℂ H)
    (f : CompactFunctions H A.representation) :
    germOne hG H hH A f =
      ProjectorActionStalks.originalGerm (quotient_isLocallyProfinite H hG hH)
        (inducedAction hG H hH A) (origin H) f := rfl

theorem germOne_surjective (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    Function.Surjective (germOne hG H hH A) :=
  ProjectorActionStalks.originalGerm_surjective (quotient_isLocallyProfinite H hG hH)
    (inducedAction hG H hH A) (origin H)

/-- Both surjections have the same kernel. -/
theorem ker_evalOne (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    LinearMap.ker (evalOne H A.representation) = LinearMap.ker (germOne hG H hH A) := by
  let := hG.locallyCompactSpace
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    evalOne_eq_zero_iff H A.representation hH (quotient_isLocallyProfinite H hG hH)]
  exact (ProjectorActionStalks.originalGerm_eq_zero_iff (quotient_isLocallyProfinite H hG hH)
    (inducedAction hG H hH A) (origin H) f).symm

/-- The complex-linear identification of the coefficients with the identity-coset stalk. -/
def unitLinearEquiv (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    A ≃ₗ[ℂ]
      (CompactSections.ordinary ((InductionSheaf.functor hG H hH).obj A).obj.obj).stalk
        (origin H) :=
  ((evalOne H A.representation).quotKerEquivOfSurjective
      (evalOne_surjective H A.representation hG A.isSmooth)).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (ker_evalOne hG H hH A)) ≪≫ₗ
    ((germOne hG H hH A).quotKerEquivOfSurjective (germOne_surjective hG H hH A))

/-- The identification sends the identity value of a function to its identity-coset germ. -/
theorem unitLinearEquiv_evalOne (A : Langlands.SmoothRep.{0, 0, 0} ℂ H)
    (f : CompactFunctions H A.representation) :
    unitLinearEquiv hG H hH A (evalOne H A.representation f) = germOne hG H hH A f := by
  simp only [unitLinearEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The identification intertwines the coefficient action and the original stalk action. -/
theorem unitLinearEquiv_intertwining (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) (h : H)
    (v : A) :
    unitLinearEquiv hG H hH A (A.representation h v) =
      ((pointRestriction H hG hH).obj ((InductionSheaf.functor hG H hH).obj A)).representation
        h (unitLinearEquiv hG H hH A v) := by
  obtain ⟨f, rfl⟩ := evalOne_surjective H A.representation hG A.isSmooth v
  rw [← evalOne_compactInduced, unitLinearEquiv_evalOne, unitLinearEquiv_evalOne,
    germOne_apply, germOne_apply]
  exact (ProjectorActionStalks.stalkPull_originalGerm (quotient_isLocallyProfinite H hG hH)
    (inducedAction hG H hH A) (h : G) (origin H) (subgroup_fixes_origin H h⁻¹) f).symm

/-- The equivariant identification of the coefficients with the identity-coset stalk. -/
def unitEquiv (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    A.representation.Equiv
      ((pointRestriction H hG hH).obj ((InductionSheaf.functor hG H hH).obj A)).representation :=
  Representation.Equiv.mk (unitLinearEquiv hG H hH A) fun h =>
    LinearMap.ext fun v => unitLinearEquiv_intertwining hG H hH A h v

/-- The identification is natural for all original smooth coefficient maps. -/
theorem unitLinearEquiv_naturality {A B : Langlands.SmoothRep.{0, 0, 0} ℂ H} (u : A ⟶ B)
    (v : A) :
    unitLinearEquiv hG H hH B (Langlands.SmoothRep.hom u v) =
      Langlands.SmoothRep.hom
        ((pointRestriction H hG hH).map ((InductionSheaf.functor hG H hH).map u))
        (unitLinearEquiv hG H hH A v) := by
  let := hG.locallyCompactSpace
  obtain ⟨f, rfl⟩ := evalOne_surjective H A.representation hG A.isSmooth v
  rw [← evalOne_compactInducedMap, unitLinearEquiv_evalOne, unitLinearEquiv_evalOne,
    germOne_apply, germOne_apply]
  exact (ProjectorActionStalks.stalkMap_originalGerm (quotient_isLocallyProfinite H hG hH)
    (CompactInductionTestModule.compatibleMap H hH A.representation
      (Langlands.SmoothRep.hom u)) (origin H) f).symm

/-- Renard III.3.2: every smooth coefficient representation is naturally the original
identity-coset stalk of its induction sheaf. -/
def unitIso :
    𝟭 (Langlands.SmoothRep.{0, 0, 0} ℂ H) ≅
      InductionSheaf.functor hG H hH ⋙ pointRestriction H hG hH :=
  NatIso.ofComponents (fun A => Langlands.SmoothRep.mkIso (unitEquiv hG H hH A)) (by
    intro A B u
    ext v
    exact unitLinearEquiv_naturality hG H hH u v)

end Germ

end Langlands.Sheaf.Renard.HomogeneousOriginStalk

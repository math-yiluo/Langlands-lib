import Langlands.Geometry.Building.KPApartment
import Langlands.GroupScheme.Torus.RootSupportBaseChange

/-! # Actual reduced translations under split-torus base change -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (S : CommGroupScheme (Spec (CommRingCat.of k)))
  (hS : IsSplitTorus S.toGrp)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S

/-- Real scalar extension of the actual cocharacter base-change equivalence
of the supplied split torus. -/
def splitCocharacterBaseChange : V S ≃ₗ[ℝ] V S_K :=
  LinearEquiv.baseChange ℤ ℝ _ _
    (cocharacterLattice.baseChangeEquiv b S hS).toIntLinearEquiv

/-- Every pure tensor uses the original scheme-theoretic cocharacter pullback. -/
@[simp] theorem splitCocharacterBaseChange_tmul (r : ℝ) (ν : cocharacterLattice S) :
    splitCocharacterBaseChange (K := K) S hS (r ⊗ₜ[ℤ] ν) =
      r ⊗ₜ[ℤ] cocharacterLattice.baseChange b S ν := rfl

/-- The actual character and cocharacter pullbacks preserve real evaluation. -/
theorem eval_splitCocharacterBaseChange (χ : characterLattice S) (v : V S) :
    eval S_K (characterLattice.baseChange b S χ)
        (splitCocharacterBaseChange (K := K) S hS v) = eval S χ v := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    rw [splitCocharacterBaseChange_tmul, eval_tmul, eval_tmul,
      latticePairing_baseChange]
  | add v w hv hw => simp only [map_add, hv, hw]

variable {S}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G)

local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

local instance splitTranslationBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The actual base-change map preserves and reflects the full common root
annihilator, without a supplied root-set comparison hypothesis. -/
theorem splitCocharacterBaseChange_mem_rootAnnihilator_iff (v : V S) :
    splitCocharacterBaseChange (K := K) S hS v ∈ rootAnnihilator i_K ↔
      v ∈ rootAnnihilator i := by
  rw [mem_rootAnnihilator, mem_rootAnnihilator]
  constructor
  · intro hv χ hχ
    have hχK : characterLattice.baseChange b S χ ∈ relativeRoots i_K :=
      (mem_roots_baseChange_iff (K := K) G S hS i χ).mpr hχ
    simpa only [eval_splitCocharacterBaseChange] using hv _ hχK
  · intro hv χK hχK
    obtain ⟨χ, rfl⟩ := (characterLattice.baseChangeEquiv b S hS).surjective χK
    simp only [characterLattice.baseChangeEquiv_apply] at hχK ⊢
    rw [eval_splitCocharacterBaseChange]
    exact hv χ ((mem_roots_baseChange_iff (K := K) G S hS i χ).mp hχK)

/-- The image of the common root annihilator is the entire pulled-back
annihilator. -/
theorem map_splitCocharacterBaseChange_rootAnnihilator :
    (rootAnnihilator i).map
        (splitCocharacterBaseChange (K := K) S hS : V S →ₗ[ℝ] V S_K) =
      rootAnnihilator i_K := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (splitCocharacterBaseChange_mem_rootAnnihilator_iff (K := K) hS i w).mpr hw
  · intro hv
    obtain ⟨w, rfl⟩ := (splitCocharacterBaseChange (K := K) S hS).surjective v
    exact ⟨w,
      (splitCocharacterBaseChange_mem_rootAnnihilator_iff (K := K) hS i w).mp hv, rfl⟩

/-- Actual field extension induces an equivalence on the reduced translation
spaces for the supplied split torus and its scheme pullback. -/
def splitTranslationBaseChange :
    TranslationSpace i ≃ₗ[ℝ] TranslationSpace (S := S_K) i_K :=
  Submodule.Quotient.equiv _ _ (splitCocharacterBaseChange (K := K) S hS)
    (map_splitCocharacterBaseChange_rootAnnihilator (K := K) hS i)

/-- The quotient equivalence is represented by actual cocharacter base change. -/
@[simp] theorem splitTranslationBaseChange_mk (v : V S) :
    splitTranslationBaseChange (K := K) hS i (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (splitCocharacterBaseChange (K := K) S hS v) := rfl

/-- Each actual relative-root form commutes with reduced translation
base change. -/
theorem rootForm_splitTranslationBaseChange (α : relativeRoots i)
    (v : TranslationSpace i) :
    rootForm (S := S_K) i_K (rootsBaseChangeEquiv (K := K) G S hS i α)
        (splitTranslationBaseChange (K := K) hS i v) = rootForm i α v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  exact eval_splitCocharacterBaseChange S hS α.val w

end Langlands.Geometry.Building

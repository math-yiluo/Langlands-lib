import Langlands.GroupScheme.Lie.ActionBaseChange
import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.ActionWeightSupport
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Scalar extension of weights of an external split-torus action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange b) G

local instance actionWeightBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance actionWeightBaseChangeFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

variable (a : AutomorphicAction S.toGrp G)

/-- An intrinsic action weight vector extends to the corresponding character
weight of the actual pulled-back action. -/
theorem actionWeightSpace_baseChange_mem (χ : characterLattice S)
    {x : Additive (lieKernel G k)} (hx : x ∈ actionWeightSpace a χ) :
    Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
      actionWeightSpace (a.baseChange b) (characterLattice.baseChange b S χ) := by
  rw [actionWeightSpace_eq_lieWeightSpace, AutomorphicAction.mem_lieWeightSpace]
  intro A _ _ t
  let : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  simp only [Grp.id_hom_hom, Category.comp_id]
  apply (Lie.kernelBaseChangeLinearEquiv k K G A).injective
  rw [AutomorphicAction.differential_baseChange,
    Lie.schemeScalarExtension_base_naturality, LinearEquiv.map_smul,
    Lie.schemeScalarExtension_base_naturality, Lie.characterValue_baseChange]
  rw [actionWeightSpace_eq_lieWeightSpace] at hx
  simpa only [Grp.id_hom_hom, Category.comp_id] using
    (AutomorphicAction.mem_lieWeightSpace.mp hx) A
      (Lie.affineBaseChangeEquiv k K S.toGrp A t)

/-- The scalar-extended span of one intrinsic action weight space inside the
actual Lie kernel of the scheme pullback. -/
def extendedActionWeightSpace (χ : characterLattice S) :
    Submodule K (Additive (lieKernel G_K K)) :=
  Submodule.span K ((fun x => Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x)) ''
    (actionWeightSpace a χ : Set (Additive (lieKernel G k))))

/-- The extended span lies in its specified pulled-back action weight space. -/
theorem extendedActionWeightSpace_le (χ : characterLattice S) :
    extendedActionWeightSpace (K := K) a χ ≤
      actionWeightSpace (a.baseChange b) (characterLattice.baseChange b S χ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  exact actionWeightSpace_baseChange_mem a χ hx

/-- Scalar extension preserves and reflects nonvanishing of the extended span. -/
theorem extendedActionWeightSpace_ne_bot_iff (χ : characterLattice S) :
    extendedActionWeightSpace (K := K) a χ ≠ ⊥ ↔ actionWeightSpace a χ ≠ ⊥ := by
  constructor
  · intro h hbot
    apply h
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ actionWeightSpace a χ at hx
    have hx0 : x = 0 := by simpa only [hbot, Submodule.mem_bot] using hx
    change Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) = 0
    rw [hx0, TensorProduct.tmul_zero, LinearEquiv.map_zero]
  · intro h hbot
    apply h
    apply bot_unique
    intro x hx
    have he : Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
        extendedActionWeightSpace (K := K) a χ := Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at he
    have hz : (1 : K) ⊗ₜ[k] x = 0 :=
      (Lie.schemeScalarExtension (K := K) G).injective
        (by simpa only [LinearEquiv.map_zero] using he)
    change x = 0
    simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using hz

/-- Extended action weight spaces span whenever the original spaces span. -/
theorem iSup_extendedActionWeightSpace_eq_top
    (hi : iSup (actionWeightSpace a) = ⊤) :
    iSup (extendedActionWeightSpace (K := K) a) = ⊤ := by
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨z, rfl⟩ := (Lie.schemeScalarExtension (K := K) G).surjective y
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    have hx : x ∈ iSup (actionWeightSpace a) := by rw [hi]; trivial
    have he : Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
        iSup (extendedActionWeightSpace (K := K) a) := by
      refine Submodule.iSup_induction (actionWeightSpace a)
        (motive := fun x => Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
          iSup (extendedActionWeightSpace (K := K) a)) hx ?_ ?_ ?_
      · intro χ x hx
        exact Submodule.mem_iSup_of_mem χ (Submodule.subset_span ⟨x, hx, rfl⟩)
      · simpa only [TensorProduct.tmul_zero, LinearEquiv.map_zero] using
          (iSup (extendedActionWeightSpace (K := K) a)).zero_mem
      · intro x y hx hy
        simpa only [TensorProduct.tmul_add, LinearEquiv.map_add] using
          (iSup (extendedActionWeightSpace (K := K) a)).add_mem hx hy
    have hc := (iSup (extendedActionWeightSpace (K := K) a)).smul_mem c he
    simpa only [Lie.schemeScalarExtension_tmul, one_smul] using hc
  | add x y hx hy =>
    simpa only [LinearEquiv.map_add] using
      (iSup (extendedActionWeightSpace (K := K) a)).add_mem hx hy

open Classical in
private theorem actionWeightSpace_baseChange_isInternal (hS : IsSplitTorus S.toGrp) :
    DirectSum.IsInternal
      (actionWeightSpace (k := K) (G := G_K)
        (S := (CommGroupScheme.baseChange b).obj S) (a.baseChange b)) := by
  classical
  exact isInternal_actionWeightSpace (k := K) (G := G_K)
    (S := (CommGroupScheme.baseChange b).obj S) (a.baseChange b) (hS.baseChange b)

/-- Every pulled-back action weight space is the sum of extended spaces
in its character fiber. -/
theorem actionWeightSpace_baseChange_eq_iSup (hS : IsSplitTorus S.toGrp)
    (ψ : characterLattice ((CommGroupScheme.baseChange b).obj S)) :
    actionWeightSpace (a.baseChange b) ψ =
      ⨆ χ : {χ : characterLattice S // characterLattice.baseChange b S χ = ψ},
        extendedActionWeightSpace (K := K) a χ.val := by
  classical
  exact submodule_eq_iSup_of_refinement (extendedActionWeightSpace (K := K) a)
    (actionWeightSpace (k := K) (G := G_K)
      (S := (CommGroupScheme.baseChange b).obj S) (a.baseChange b))
    (iSup_extendedActionWeightSpace_eq_top (K := K) a
      (iSup_actionWeightSpace_eq_top a hS))
    (actionWeightSpace_baseChange_isInternal (K := K) a hS)
    (characterLattice.baseChange b S) (extendedActionWeightSpace_le (K := K) a) ψ

/-- Every weight space of the pulled-back external action is exactly its
scalar-extended original weight space. -/
theorem actionWeightSpace_baseChange_eq_extendedActionWeightSpace
    (hS : IsSplitTorus S.toGrp) (χ : characterLattice S) :
    actionWeightSpace (a.baseChange b) (characterLattice.baseChange b S χ) =
      extendedActionWeightSpace (K := K) a χ := by
  classical
  rw [actionWeightSpace_baseChange_eq_iSup a hS]
  apply le_antisymm
  · refine iSup_le fun ψ => ?_
    have hψ : ψ.val = χ :=
      (hS.characterLattice_baseChange_bijective b S).injective ψ.property
    rw [hψ]
  · exact le_iSup_of_le ⟨χ, rfl⟩ le_rfl

/-- A character occurs in the original external action exactly when its
pullback occurs; the zero character is included. -/
theorem actionWeightSpace_baseChange_ne_bot_iff
    (hS : IsSplitTorus S.toGrp) (χ : characterLattice S) :
    actionWeightSpace (a.baseChange b) (characterLattice.baseChange b S χ) ≠ ⊥ ↔
      actionWeightSpace a χ ≠ ⊥ := by
  rw [actionWeightSpace_baseChange_eq_extendedActionWeightSpace a hS χ]
  exact extendedActionWeightSpace_ne_bot_iff a χ

/-- Every field extension preserves and reflects the whole actual Lie support
of an external split-torus action, including occurring zero. -/
theorem mem_actionWeightSupport_top_baseChange_iff
    (hS : IsSplitTorus S.toGrp) (χ : characterLattice S) :
    characterLattice.baseChange b S χ ∈ actionWeightSupport (a.baseChange b) ⊤ ↔
      χ ∈ actionWeightSupport a ⊤ := by
  rw [actionWeightSupport_top, actionWeightSupport_top]
  exact actionWeightSpace_baseChange_ne_bot_iff a hS χ

end Langlands.GroupScheme.RelativeRoot

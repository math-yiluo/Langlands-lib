import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.LinearAlgebra.InternalTensorSupport

/-! # Actual split-torus root support under arbitrary field extension -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

local instance rootSupportBaseChangeAffine : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance rootSupportBaseChangeFiniteType : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

include hT

/-- The actual base-changed character has a zero adjoint weight space precisely
when the original character does. -/
theorem weightSpace_baseChange_eq_bot_iff (χ : characterLattice T) :
    weightSpace (T := T_K) i_K (characterLattice.baseChange b T χ) = ⊥ ↔
      weightSpace i χ = ⊥ := by
  classical
  exact Langlands.LinearAlgebra.component_eq_bot_iff_of_tensorEquiv
    (k := k) (K := K)
    (weightSpace i) (weightSpace (T := T_K) i_K) (characterLattice.baseChange b T)
    (hT.characterLattice_baseChange_bijective b T).injective
    (isInternal_weightSpace_of_isSplitTorus k G T hT i)
    (isInternal_weightSpace_of_isSplitTorus K G_K T_K (hT.baseChange b) i_K)
    (Lie.schemeScalarExtension (K := K) G)
    (fun χ x hx => weightSpace_baseChange_mem G i χ hx) χ

/-- Actual root membership is preserved and reflected by character pullback. -/
theorem mem_roots_baseChange_iff (χ : characterLattice T) :
    characterLattice.baseChange b T χ ∈ roots i_K ↔ χ ∈ roots i := by
  have hz : characterLattice.baseChange b T χ = 0 ↔ χ = 0 :=
    (characterLattice.baseChangeEquiv b T hT).map_eq_zero_iff
  simp only [mem_roots, ne_eq, hz, weightSpace_baseChange_eq_bot_iff G T hT i]

/-- The roots after arbitrary field extension are exactly the actual pullbacks
of the old roots. -/
theorem roots_baseChange :
    roots (T := T_K) i_K = (characterLattice.baseChange b T) '' roots i := by
  ext χ'
  obtain ⟨χ, rfl⟩ := (characterLattice.baseChangeEquiv b T hT).surjective χ'
  change characterLattice.baseChange b T χ ∈ roots i_K ↔
    characterLattice.baseChange b T χ ∈ (characterLattice.baseChange b T) '' roots i
  rw [mem_roots_baseChange_iff G T hT i]
  constructor
  · intro hχ
    exact ⟨χ, hχ, rfl⟩
  · rintro ⟨ψ, hψ, hψχ⟩
    exact (hT.characterLattice_baseChange_bijective b T).injective hψχ ▸ hψ

/-- The canonical equivalence between the actual roots before and after extension. -/
def rootsBaseChangeEquiv : roots (T := T) i ≃ roots (T := T_K) i_K :=
  (characterLattice.baseChangeEquiv b T hT).toEquiv.subtypeEquiv
    (fun χ => (mem_roots_baseChange_iff G T hT i χ).symm)

@[simp] theorem rootsBaseChangeEquiv_apply (α : roots i) :
    (rootsBaseChangeEquiv (K := K) G T hT i α).val =
      characterLattice.baseChange b T α.val := rfl

end Langlands.GroupScheme

import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Torus.WeightBaseChangeSupport
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Comparison of complete weight spaces after field extension -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
namespace Langlands.GroupScheme
set_option backward.isDefEq.respectTransparency false

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange b) G

local instance weightComparisonBaseChangeAffine : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance weightComparisonBaseChangeFiniteType : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

open Classical in
private theorem weightSpace_baseChange_isInternal (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) :
    DirectSum.IsInternal (weightSpace
      (T := (CommGroupScheme.baseChange b).obj T) (G := G_K)
      ((GroupScheme.baseChange b).map i)) := by
  classical
  exact isInternal_weightSpace_of_isSplitTorus K G_K
    ((CommGroupScheme.baseChange b).obj T) (hT.baseChange b)
    ((GroupScheme.baseChange b).map i)

/-- Every pullback weight space is the sum of the extended original spaces in its
character fiber. -/
theorem weightSpace_baseChange_eq_iSup (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G)
    (ψ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    weightSpace ((GroupScheme.baseChange b).map i) ψ =
      ⨆ χ : {χ : characterLattice T // characterLattice.baseChange b T χ = ψ},
        extendedWeightSpace (K := K) i χ.val := by
  classical
  exact submodule_eq_iSup_of_refinement (extendedWeightSpace (K := K) i)
    (weightSpace (T := (CommGroupScheme.baseChange b).obj T) (G := G_K)
      ((GroupScheme.baseChange b).map i))
    (iSup_extendedWeightSpace_eq_top (K := K) i
      (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top)
    (weightSpace_baseChange_isInternal (K := K) hT i)
    (characterLattice.baseChange b T) (extendedWeightSpace_le (K := K) i) ψ

/-- The weight space of a pulled-back character is exactly its scalar-extended
original weight span. -/
theorem weightSpace_baseChange_eq_extendedWeightSpace (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    weightSpace ((GroupScheme.baseChange b).map i) (characterLattice.baseChange b T χ) =
      extendedWeightSpace (K := K) i χ := by
  rw [weightSpace_baseChange_eq_iSup hT i]
  apply le_antisymm
  · refine iSup_le fun ψ => ?_
    have hψ : ψ.val = χ := (hT.characterLattice_baseChange_bijective b T).injective ψ.property
    rw [hψ]
  · exact le_iSup_of_le ⟨χ, rfl⟩ le_rfl

/-- A split-torus character has a nonzero weight space exactly when its pullback does. -/
theorem weightSpace_baseChange_ne_bot_iff (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    weightSpace ((GroupScheme.baseChange b).map i)
      (characterLattice.baseChange b T χ) ≠ ⊥ ↔ weightSpace i χ ≠ ⊥ := by
  rw [weightSpace_baseChange_eq_extendedWeightSpace hT i χ]
  exact extendedWeightSpace_ne_bot_iff i χ

/-- Pullback identifies the actual root sets of a split-torus action over a field
and over any extension field. -/
abbrev rootBaseChangeEquiv (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) :
    roots i ≃ roots (T := (CommGroupScheme.baseChange b).obj T) (G := G_K)
      ((GroupScheme.baseChange b).map i) :=
  rootsBaseChangeEquiv (K := K) G T hT i

@[simp]
theorem rootBaseChangeEquiv_val (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : roots i) :
    (rootBaseChangeEquiv (K := K) hT i χ : characterLattice
      ((CommGroupScheme.baseChange b).obj T)) = characterLattice.baseChange b T χ := rfl

/-- Negation stability for the actual roots of a split-torus action is equivalent
before and after field extension. -/
theorem roots_negation_baseChange_iff (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) :
    (∀ ψ ∈ roots (T := (CommGroupScheme.baseChange b).obj T) (G := G_K)
      ((GroupScheme.baseChange b).map i), -ψ ∈
      roots ((GroupScheme.baseChange b).map i)) ↔
    (∀ χ ∈ roots i, -χ ∈ roots i) := by
  constructor
  · intro h χ hχ
    apply (mem_roots_baseChange_iff (K := K) G T hT i (-χ)).mp
    rw [map_neg]
    exact h _ ((mem_roots_baseChange_iff (K := K) G T hT i χ).mpr hχ)
  · intro h ψ hψ
    obtain ⟨χ, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).surjective ψ
    rw [← map_neg]
    exact (mem_roots_baseChange_iff (K := K) G T hT i (-χ)).mpr
      (h χ ((mem_roots_baseChange_iff (K := K) G T hT i χ).mp hψ))

end FieldExtension

end Langlands.GroupScheme

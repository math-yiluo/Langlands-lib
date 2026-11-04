import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Lie.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Positive roots and the actual dynamic tangent dimension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A positive adjoint weight space lies in the actual tangent submodule of
the dynamic identity-limit subgroup. -/
theorem weightSpace_le_tangentSubmodule_unipotent
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {χ : characterLattice T} (hχ : 0 < latticePairing T χ ν) :
    weightSpace i χ ≤
      tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) := by
  rw [tangentSubmodule_unipotent_eq_semigroupWeightSpan hT i ν]
  rw [← actionWeightSpace_conjugation i χ]
  exact le_iSup
    (fun ψ : positiveSemigroup ν => actionWeightSpace (AutomorphicAction.conjugation i) ψ.val)
    ⟨χ, hχ⟩

/-- The canonical linear inclusion of a positive adjoint weight space into
the actual dynamic unipotent tangent submodule. -/
def positiveWeightTangentInclusion
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {χ : characterLattice T} (hχ : 0 < latticePairing T χ ν) :
    weightSpace i χ →ₗ[k]
      tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) :=
  Submodule.inclusion (weightSpace_le_tangentSubmodule_unipotent hT i ν hχ)

/-- Distinct positive actual roots force the actual dynamic tangent submodule
to have dimension at least two. -/
theorem two_le_finrank_tangentSubmodule_unipotent_of_distinct_positive_roots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {α β : characterLattice T} (hα : α ∈ roots i) (hβ : β ∈ roots i)
    (hαpos : 0 < latticePairing T α ν) (hβpos : 0 < latticePairing T β ν)
    (hne : α ≠ β) :
    2 ≤ Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) := by
  classical
  have hd : Disjoint (weightSpace i α) (weightSpace i β) :=
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep.pairwiseDisjoint hne
  have hαdim : 1 ≤ Module.finrank k (weightSpace i α) :=
    Submodule.one_le_finrank_iff.mpr hα.2
  have hβdim : 1 ≤ Module.finrank k (weightSpace i β) :=
    Submodule.one_le_finrank_iff.mpr hβ.2
  have hsum : Module.finrank k ↥(weightSpace i α ⊔ weightSpace i β) +
      Module.finrank k ↥(weightSpace i α ⊓ weightSpace i β) =
      Module.finrank k (weightSpace i α) + Module.finrank k (weightSpace i β) :=
    Submodule.finrank_sup_add_finrank_inf_eq (weightSpace i α) (weightSpace i β)
  rw [hd.eq_bot, finrank_bot, add_zero] at hsum
  have hle : Module.finrank k ↥(weightSpace i α ⊔ weightSpace i β) ≤
      Module.finrank k
        (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) :=
    Submodule.finrank_mono
      (sup_le (weightSpace_le_tangentSubmodule_unipotent hT i ν hαpos)
        (weightSpace_le_tangentSubmodule_unipotent hT i ν hβpos))
  omega

/-- A one-dimensional bound on the actual dynamic tangent submodule implies
uniqueness of a positive actual root. No reductivity or maximality is needed
for this implication. -/
theorem positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hdim : Module.finrank k
      (tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) ≤ 1)
    {α β : characterLattice T} (hα : α ∈ roots i) (hβ : β ∈ roots i)
    (hαpos : 0 < latticePairing T α ν) (hβpos : 0 < latticePairing T β ν) :
    α = β := by
  by_contra hne
  have htwo := two_le_finrank_tangentSubmodule_unipotent_of_distinct_positive_roots
    hT i ν hα hβ hαpos hβpos hne
  omega

end Langlands.GroupScheme.RelativeRoot

import Langlands.GroupScheme.Lie.WeightImage
import Langlands.GroupScheme.Lie.FieldExtension
import Langlands.GroupScheme.Torus.RootSupportBaseChange

/-! # Field extension of opposite-weight Lie-image witnesses -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

/-- Both opposite character weight spaces contain a nonzero vector in the actual
Lie image of the specified subgroup homomorphism. -/
def MeetsOppositeWeightSpaces {R : CommRingCat.{u}}
    {T : CommGroupScheme (Spec R)} {H G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] (j : T.toGrp ⟶ G) (i : H ⟶ G)
    (α : characterLattice T) : Prop :=
  MeetsWeightSpace j i α ∧ MeetsWeightSpace j i (-α)

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k K

local instance weightImageBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- A supplied nonzero actual Lie-image weight witness survives any field extension. -/
theorem MeetsWeightSpace.baseChange (j : T.toGrp ⟶ G) (i : H ⟶ G)
    (α : characterLattice T) (h : MeetsWeightSpace j i α) :
    MeetsWeightSpace ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map i) (characterLattice.baseChange b T α) :=
  weightSpace_lieImage_baseChange j α i h

/-- An opposite-weight pair survives field extension with the actual pulled-back
character and the same pulled-back subgroup homomorphism. -/
theorem MeetsOppositeWeightSpaces.baseChange (j : T.toGrp ⟶ G) (i : H ⟶ G)
    (α : characterLattice T) (h : MeetsOppositeWeightSpaces j i α) :
    MeetsOppositeWeightSpaces ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map i) (characterLattice.baseChange b T α) := by
  refine ⟨h.1.baseChange j i α, ?_⟩
  simpa only [map_neg] using h.2.baseChange (K := K) j i (-α)

/-- Excluding an opposite-weight pair after field extension excludes it before
extension, without any assumption on the acting torus or subgroup. -/
theorem not_meetsOppositeWeightSpaces_of_baseChange
    (j : T.toGrp ⟶ G) (i : H ⟶ G) (α : characterLattice T)
    (h : ¬ MeetsOppositeWeightSpaces ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map i) (characterLattice.baseChange b T α)) :
    ¬ MeetsOppositeWeightSpaces j i α :=
  fun hpair => h (hpair.baseChange j i α)

/-- For a split acting torus, exclusion on all actual roots descends along any
field extension. Root preservation and witness preservation use the same
character pullback. -/
theorem not_meetsOppositeWeightSpaces_on_roots_of_baseChange
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (i : H ⟶ G)
    (h : ∀ β ∈ roots (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map j),
      ¬ MeetsOppositeWeightSpaces ((GroupScheme.baseChange b).map j)
        ((GroupScheme.baseChange b).map i) β) :
    ∀ α ∈ roots j, ¬ MeetsOppositeWeightSpaces j i α := by
  intro α hα
  exact not_meetsOppositeWeightSpaces_of_baseChange j i α
    (h _ ((mem_roots_baseChange_iff (K := K) G T hT j α).mpr hα))

end FieldExtension

end Langlands.GroupScheme.Lie

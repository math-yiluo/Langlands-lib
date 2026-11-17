import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Torus.WeightSpaceScalarExtension
import Langlands.GroupScheme.Reductive.RankOneRootSupportLinesStatement
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Pointwise rank-one support and line spaces under field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section LocalData

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual adjoint roots are supported on a prescribed signed pair, and
both corresponding actual weight spaces admit linear coordinates. -/
def RankOneSupportLines (i : T.toGrp ⟶ G) (α : characterLattice T) : Prop :=
  (∀ β ∈ roots i, β = α ∨ β = -α) ∧
    Nonempty (k ≃ₗ[k] weightSpace i α) ∧
    Nonempty (k ≃ₗ[k] weightSpace i (-α))

end LocalData

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

local instance rankOneSupportLinesBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

include hT

/-- Signed-pair support is preserved and reflected by actual character pullback. -/
theorem roots_signedPair_baseChange_iff (α : characterLattice T) :
    (∀ β ∈ roots (T := T_K) i_K,
      β = characterLattice.baseChange b T α ∨
        β = -characterLattice.baseChange b T α) ↔
      (∀ β ∈ roots i, β = α ∨ β = -α) := by
  constructor
  · intro h β hβ
    have hβK := (mem_roots_baseChange_iff (K := K) G T hT i β).mpr hβ
    rcases h _ hβK with h | h
    · exact Or.inl ((hT.characterLattice_baseChange_bijective b T).injective h)
    · right
      apply (hT.characterLattice_baseChange_bijective b T).injective
      simpa only [map_neg] using h
  · intro h β hβ
    obtain ⟨β, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).surjective β
    rcases h β ((mem_roots_baseChange_iff (K := K) G T hT i β).mp hβ) with h | h
    · exact Or.inl (congrArg (characterLattice.baseChange b T) h)
    · right
      simpa only [map_neg] using congrArg (characterLattice.baseChange b T) h

/-- The local support and two line-space inputs for the rank-one cell descend
through every field extension of a split torus. -/
theorem rankOneSupportLines_baseChange_iff (α : characterLattice T) :
    RankOneSupportLines (T := T_K) i_K (characterLattice.baseChange b T α) ↔
      RankOneSupportLines i α := by
  have hneg :
      Nonempty (K ≃ₗ[K] weightSpace i_K (-characterLattice.baseChange b T α)) ↔
        Nonempty (k ≃ₗ[k] weightSpace i (-α)) := by
    rw [← (characterLattice.baseChange b T).map_neg α]
    exact weightSpace_line_baseChange_iff (K := K) hT i (-α)
  exact (roots_signedPair_baseChange_iff (K := K) G T hT i α).and
    ((weightSpace_line_baseChange_iff (K := K) hT i α).and hneg)

end FieldExtension

/-- The all-field structural input restricts to its algebraically closed case. -/
theorem algClosedRankOneRootSupportLines_of_statement
    (h : SplitRankOneRootSupportLinesStatement.{u}) :
    AlgClosedRankOneRootSupportLinesStatement.{u} := by
  intro k _ _ G hG T hT i hi J P hP hdep r
  exact h k G hG T hT i hi J P hP hdep r

/-- The pointwise algebraically closed support and line-space input suffices
for the exact arbitrary-field structural input. -/
theorem splitRankOneRootSupportLines_of_algClosed
    (hclosed : AlgClosedRankOneRootSupportLinesStatement.{u}) :
    SplitRankOneRootSupportLinesStatement.{u} := by
  intro k _ G hG T hT i hi J P hP hdep r
  have := hG.isAffineHom
  have := hG.smooth
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let ic : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map i
  let Pc := SplitRootDatum.baseChange b T hT P
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have hic : IsMaximalTorus ic :=
    (maximalTorusBaseChange k (AlgebraicClosure k) G T i hi.1 hi.2.1).mp hi
  have hPc : IsRootDatumOf ic Pc :=
    hP.baseChange (K := AlgebraicClosure k) G T hT i
  have hdepc : ∀ α ∈ roots ic, ∀ β ∈ roots ic,
      ¬ LinearIndependent ℤ ![α, β] :=
    (roots_pairwise_dependent_baseChange_iff (K := AlgebraicClosure k) G T hT i).mpr hdep
  have hlocal : RankOneSupportLines ic (Pc.root r) :=
    hclosed (AlgebraicClosure k) Gc hGc Tc (hT.baseChange b) ic hic J Pc hPc hdepc r
  exact (rankOneSupportLines_baseChange_iff
    (K := AlgebraicClosure k) G T hT i (P.root r)).mp hlocal

/-- The full support/line interface and its algebraically closed geometric
case are equivalent in the same arbitrary universe. -/
theorem splitRankOneRootSupportLines_iff_algClosed :
    SplitRankOneRootSupportLinesStatement.{u} ↔
      AlgClosedRankOneRootSupportLinesStatement.{u} :=
  ⟨algClosedRankOneRootSupportLines_of_statement,
    splitRankOneRootSupportLines_of_algClosed⟩

end Langlands.GroupScheme

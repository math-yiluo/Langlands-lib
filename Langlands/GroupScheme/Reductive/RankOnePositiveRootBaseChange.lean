import Langlands.GroupScheme.Reductive.RankOnePositiveRootStatement
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Positive roots under field extension and the algebraically closed reduction -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

include hT

/-- Pullback identifies the actual roots positive on a specified cocharacter. -/
def positiveRootBaseChangeEquiv (ν : cocharacterLattice T) :
    {α : characterLattice T // α ∈ roots i ∧ 0 < latticePairing T α ν} ≃
      {α : characterLattice T_K // α ∈ roots (T := T_K) i_K ∧
        0 < latticePairing T_K α (cocharacterLattice.baseChange b T ν)} :=
  (characterLattice.baseChangeEquiv b T hT).toEquiv.subtypeEquiv (fun α => by
    exact (mem_roots_baseChange_iff (K := K) G T hT i α).symm.and
      (Iff.of_eq (congrArg (fun m : ℤ => 0 < m)
        (latticePairing_baseChange b T α ν).symm)))

@[simp]
theorem positiveRootBaseChangeEquiv_val (ν : cocharacterLattice T)
    (α : {α : characterLattice T // α ∈ roots i ∧ 0 < latticePairing T α ν}) :
    (positiveRootBaseChangeEquiv (K := K) G T hT i ν α).val =
      characterLattice.baseChange b T α.val := rfl

/-- Integral dependence of a pair of characters is unchanged by pullback. -/
theorem linearIndependent_pair_baseChange_iff (α β : characterLattice T) :
    LinearIndependent ℤ
      ![characterLattice.baseChange b T α, characterLattice.baseChange b T β] ↔
      LinearIndependent ℤ ![α, β] := by
  rw [LinearIndependent.pair_iff, LinearIndependent.pair_iff]
  constructor
  · intro h m n hmn
    apply h m n
    simpa only [map_add, map_zsmul, map_zero] using
      congrArg (characterLattice.baseChange b T) hmn
  · intro h m n hmn
    apply h m n
    apply (hT.characterLattice_baseChange_bijective b T).injective
    simpa only [map_add, map_zsmul, map_zero] using hmn

/-- The pairwise integral dependence hypothesis on actual roots is equivalent
before and after every field extension. -/
theorem roots_pairwise_dependent_baseChange_iff :
    (∀ α ∈ roots (T := T_K) i_K, ∀ β ∈ roots (T := T_K) i_K,
      ¬ LinearIndependent ℤ ![α, β]) ↔
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) := by
  constructor
  · intro h α hα β hβ
    rw [← linearIndependent_pair_baseChange_iff (K := K) T hT α β]
    exact h _ ((mem_roots_baseChange_iff (K := K) G T hT i α).mpr hα)
      _ ((mem_roots_baseChange_iff (K := K) G T hT i β).mpr hβ)
  · intro h α hα β hβ
    obtain ⟨α, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).surjective α
    obtain ⟨β, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).surjective β
    rw [linearIndependent_pair_baseChange_iff (K := K) T hT α β]
    exact h α ((mem_roots_baseChange_iff (K := K) G T hT i α).mp hα)
      β ((mem_roots_baseChange_iff (K := K) G T hT i β).mp hβ)

/-- For a specified cocharacter, at most one actual root is positive before
extension precisely when at most one is positive after extension. -/
theorem positiveRoot_uniqueness_baseChange_iff (ν : cocharacterLattice T) :
    (∀ α ∈ roots (T := T_K) i_K, ∀ β ∈ roots (T := T_K) i_K,
      0 < latticePairing T_K α (cocharacterLattice.baseChange b T ν) →
      0 < latticePairing T_K β (cocharacterLattice.baseChange b T ν) → α = β) ↔
    (∀ α ∈ roots i, ∀ β ∈ roots i,
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β) := by
  let e := positiveRootBaseChangeEquiv (K := K) G T hT i ν
  constructor
  · intro h α hα β hβ hαν hβν
    have he := h _ (e ⟨α, hα, hαν⟩).property.1
      _ (e ⟨β, hβ, hβν⟩).property.1
      (e ⟨α, hα, hαν⟩).property.2 (e ⟨β, hβ, hβν⟩).property.2
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  · intro h α hα β hβ hαν hβν
    have he := h _ (e.symm ⟨α, hα, hαν⟩).property.1
      _ (e.symm ⟨β, hβ, hβν⟩).property.1
      (e.symm ⟨α, hα, hαν⟩).property.2 (e.symm ⟨β, hβ, hβν⟩).property.2
    exact congrArg Subtype.val (e.symm.injective (Subtype.ext he))

end FieldExtension

/-- The algebraically closed case of the exact positive-root uniqueness target.
This proposition records the remaining geometric case; it supplies no proof. -/
def RankOneAlgClosedPositiveRootUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
        ∀ ν : cocharacterLattice T, ∀ α ∈ roots i, ∀ β ∈ roots i,
          0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β

/-- The full target restricts to its algebraically closed case. -/
theorem rankOneAlgClosedPositiveRootUniqueness_of_statement
    (h : RankOnePositiveRootUniquenessStatement.{u}) :
    RankOneAlgClosedPositiveRootUniquenessStatement.{u} := by
  intro k _ _ G hG T hT i hi
  exact h k G hG T hT i hi

/-- Forward preservation of maximal tori and the algebraically closed geometric
case imply the exact all-field target. Both inputs remain explicit obligations. -/
theorem rankOnePositiveRootUniqueness_of_algClosed
    (hmax : MaximalTorusBaseChangeForwardStatement.{u})
    (hclosed : RankOneAlgClosedPositiveRootUniquenessStatement.{u}) :
    RankOnePositiveRootUniquenessStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  have := hG.smooth
  intro hdep ν
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let ic : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map i
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have hic : IsMaximalTorus ic := hmax k (AlgebraicClosure k) G T i hi
  have hdepc : ∀ α ∈ roots ic, ∀ β ∈ roots ic,
      ¬ LinearIndependent ℤ ![α, β] :=
    (roots_pairwise_dependent_baseChange_iff (K := AlgebraicClosure k) G T hT i).mpr hdep
  exact (positiveRoot_uniqueness_baseChange_iff
    (K := AlgebraicClosure k) G T hT i ν).mp
      (hclosed (AlgebraicClosure k) Gc hGc Tc (hT.baseChange b) ic hic hdepc
        (cocharacterLattice.baseChange b T ν))

end Langlands.GroupScheme

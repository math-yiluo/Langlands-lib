/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M014.030 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusClosureDegree Statements module,
the proof of frobeniusClosureDegree_generator (M014.029) and the published
proofs it uses, give the theorem the published proposition
frobeniusClosureDegree_rangeStatement as its type, unfolded by an initial show,
and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. Two source steps use proofs that
are not yet published: the generation fact frobeniusInClosure_topologicallyGenerates
(M014.027) is replaced by its source proof, inlined as the local fact hgen0, and
the source's unused local fact hn (M014.013, frobeniusExponent_pos) is omitted.
The published proof of zHatOne_topologicallyGenerates has a Statement
proposition as its type, so it is first restated as the local fact hone. The
source step simpa using hmap used the unpublished source simp lemma
zHatPowNat_one; its source proof is inlined as the local equation hpow, used
by rw. The rest of the proof is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.U029.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U006.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U007.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U006.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U024.Proofs

/-!
# The degree image of the Frobenius closure
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image of `d_K` on `Γ` is precisely `n ℤ̂`, where
`n = d_K(σ)`.  This is the group-dual residue-degree calculation in
the Frobenius fixed-field residue-degree formula. -/
theorem frobeniusClosureDegree_range (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusClosureDegree_rangeStatement D K L hLK σ := by
  show (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range =
      AddSubgroup.toSubgroup
        ((zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range)
  let : CompactSpace K.field.toSubgroup := by
    change CompactSpace K.field
    infer_instance
  let Γ := D.frobeniusClosure K L hLK σ
  let x : Γ := D.frobeniusInClosure K L hLK σ
  let f : Γ →ₜ* ZHatMul :=
    D.frobeniusClosureDegree K L hLK σ
  let n := D.frobeniusExponent K L hLK σ
  let R : Subgroup ZHatMul :=
    AddSubgroup.toSubgroup ((zHatMulNat n).toAddMonoidHom.range)
  -- The source applies M014.027 `frobeniusInClosure_topologicallyGenerates`;
  -- `hgen0` is its source proof.
  have hgen0 : TopologicallyGenerates
      ({D.frobeniusInClosure K L hLK σ} : Set
        (D.frobeniusClosure K L hLK σ)) := by
    let φ : Unit →
        (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :=
      fun _ => σ.1
    have hgen := closedSubgroupGeneratedMap_topologicallyGenerates φ
    have hrange : Set.range (closedSubgroupGeneratedMap φ) =
        ({closedSubgroupGeneratedMap φ ()} : Set
          (closedSubgroupGenerated (Set.range φ))) := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        cases u
        rfl
      · intro hx
        exact ⟨(), hx.symm⟩
    rw [hrange] at hgen
    change TopologicallyGenerates
      ({closedSubgroupGeneratedMap φ ()} : Set
        (closedSubgroupGenerated (Set.range φ) : Subgroup _))
    exact hgen
  have hxgen : TopologicallyGenerates ({x} : Set Γ) := by
    simpa [Γ, x] using hgen0
  have hfx : f x =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    change D.frobeniusClosureDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ
    exact D.frobeniusClosureDegree_generator K L hLK σ
  have hRclosed : IsClosed (R : Set ZHatMul) := by
    exact isClosed_zHatMulNat_range n
  have hclosed_le_R :
      (closedSubgroupGenerated ({f x} : Set ZHatMul) : Subgroup ZHatMul) ≤ R := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      rw [hfx]
      change n • (1 : ZHat) ∈
        (zHatMulNat n).toAddMonoidHom.range
      exact ⟨(1 : ZHat), rfl⟩
    · exact hRclosed
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    have ha : a ∈
        (closedSubgroupGenerated ({x} : Set Γ) : Subgroup Γ) := by
      rw [show (closedSubgroupGenerated ({x} : Set Γ) : Subgroup Γ) = ⊤ by
        simpa [TopologicallyGenerates, closedSubgroupGenerated] using hxgen]
      trivial
    exact hclosed_le_R
      (map_mem_closedSubgroupGenerated_singleton f x ha)
  · intro y hy
    change y.toAdd ∈ (zHatMulNat n).toAddMonoidHom.range at hy
    obtain ⟨z, hz⟩ := hy
    have hzgen : z ∈
        (closedSubgroupGenerated
          ({Multiplicative.ofAdd (1 : ZHat)} : Set ZHatMul) :
          Subgroup ZHatMul) := by
      have hone : TopologicallyGenerates
          ({Multiplicative.ofAdd (1 : ZHat)} : Set ZHatMul) :=
        zHatOne_topologicallyGenerates
      rw [show (closedSubgroupGenerated
          ({Multiplicative.ofAdd (1 : ZHat)} : Set ZHatMul) :
          Subgroup ZHatMul) = ⊤ by
        simpa [TopologicallyGenerates, closedSubgroupGenerated] using
          hone]
      trivial
    have hmap := map_mem_closedSubgroupGenerated_singleton
      (zHatPowNat n)
      (Multiplicative.ofAdd (1 : ZHat)) hzgen
    have hclosed_le_range :
        (closedSubgroupGenerated
          ({(Multiplicative.ofAdd (1 : ZHat)) ^ n} : Set ZHatMul) :
          Subgroup ZHatMul) ≤ f.toMonoidHom.range := by
      apply Subgroup.topologicalClosure_minimal
      · rw [Subgroup.closure_le]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact ⟨x, hfx⟩
      · have hcompact : IsCompact (Set.range f) :=
          isCompact_range f.continuous_toFun
        have hrange : Set.range f = (f.toMonoidHom.range : Set ZHatMul) := by
          ext w
          constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, rfl⟩
        let : T2Space ZHatMul := by
          change T2Space ZHat
          infer_instance
        exact (hrange ▸ hcompact).isClosed
    -- The source closes this step with `simpa using hmap`, which uses the
    -- unpublished source simp lemma `zHatPowNat_one`; `hpow` is its source proof.
    have hpow : zHatPowNat n (Multiplicative.ofAdd (1 : ZHat)) =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
      apply Multiplicative.ext
      rfl
    have hzmap : zHatPowNat n z ∈ f.toMonoidHom.range := by
      apply hclosed_le_range
      rw [hpow] at hmap
      exact hmap
    have hzy : zHatPowNat n z = y := by
      apply Multiplicative.ext
      exact hz
    exact hzy ▸ hzmap

end DegreeData

end Langlands.NYLL.ClassFormation

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 754 (2026-11-16): extract the proof of M016.018
`frobeniusFixedField_relativeResidueQuotientFinite` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean
(lines 438–458) at commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace ClassFormation with Langlands.NYLL; state the theorem as the
published `frobeniusFixedField_relativeResidueQuotientFiniteStatement`
applied to the source binders, with `extensionSubgroup K.field L hLK`
expanded to its Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`
as in that statement and in all binders below. The tactic proof of
M016.018 is the source's. The source theorems it uses whose proofs are not
published are proved here as private lemmas, named by the source name with
an `_aux` suffix and applied in place of the source theorems:
* `frobeniusFixedField_mappedRelIndex_aux`: the source-private M016.016
  `frobeniusFixedField_mappedRelIndex` (FrobeniusField.lean lines 355–420),
  with the source proof, except that the M016.015 step, proved in the source
  by `simpa [S, dK] using` M016.015, is the private lemma below used as a
  term, and the published `zHatMulNat_range_index`, whose type is a
  Statement proposition, is first restated as the local fact `hindex`.
* `frobeniusFixedSubgroupWithin_normalizedDegree_image_aux`: M016.015
  (FrobeniusField.lean lines 324–353), with the source proof, in which the
  application of the unpublished M012.006 `extensionNormalizedDegree_mk` is
  replaced by its source proof `rfl`.
* `frobeniusExponent_pos_aux`: M014.013 `frobeniusExponent_pos` of
  Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean
  (lines 309–316), with the source proof.
* `frobeniusClosureDegree_range_aux`: M014.030 `frobeniusClosureDegree_range`
  of that file (lines 587–684), following the adaptation by Worker 5264 in the
  shared draft of Task 7047: the unpublished M014.027
  `frobeniusInClosure_topologicallyGenerates` is replaced by its source proof
  (local fact `hgen0`), the unused local fact `hn` is omitted, the published
  `zHatOne_topologicallyGenerates` is restated as the local fact `hone`, and
  the simp lemma `zHatPowNat_one` is replaced by its source proof (local
  equation `hpow`); in addition, the unpublished M014.029
  `frobeniusClosureDegree_generator` is replaced by its source proof, in which
  M014.014 `extensionNormalizedDegree_frobenius_eq_pow` is replaced by its
  source proof `(Exists.choose_spec σ.2).2`.
The two M014 lemmas use this file's section variable `{G : Type*}` in place
of the source's `{G : Type u}`. The unused `open CyclicCohomology` is omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ResidueDegree.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U006.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U007.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U006.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U011.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U024.Proofs

/-!
# Finiteness of the relative residue quotient of the Frobenius fixed field (NYLL M016.018)

For a Frobenius lift `σ` of `L/K`, the degree image of the fixed field `Σ`
has finite index in the degree image of `K`. The index is computed as
`d_K(σ)` (the source-private M016.016), which is positive.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Source M014.013 `frobeniusExponent_pos`: the Frobenius exponent attached
to a finite extension is strictly positive. -/
private theorem frobeniusExponent_pos_aux (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    0 < D.frobeniusExponent K L hLK σ :=
  (Exists.choose_spec σ.2).1

/-- Source M014.030 `frobeniusClosureDegree_range`: the image of `d_K` on
`Γ` is precisely `n ℤ̂`, where `n = d_K(σ)`. -/
private theorem frobeniusClosureDegree_range_aux (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range =
      AddSubgroup.toSubgroup
        ((zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range) := by
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
    -- The source applies M014.029 `frobeniusClosureDegree_generator`; the
    -- next four lines are its source proof, ending with the source proof of
    -- M014.014 `extensionNormalizedDegree_frobenius_eq_pow`.
    change D.extensionNormalizedDegree K L hLK
        (D.frobeniusInClosure K L hLK σ).1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK σ
    have hval :
        (D.frobeniusInClosure K L hLK σ).1 = σ.1 := rfl
    rw [hval]
    exact (Exists.choose_spec σ.2).2
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
    -- source simp lemma `zHatPowNat_one`; `hpow` is its source proof.
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

/-- Source M016.015 `frobeniusFixedSubgroupWithin_normalizedDegree_image`:
the normalized-degree image of `G_Σ ≤ G_K` is the image already computed on
the group-dual `Γ`. -/
private theorem frobeniusFixedSubgroupWithin_normalizedDegree_image_aux
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
        (D.normalizedDegree K).toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨QuotientGroup.mk k, hk⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) a.1
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
      change (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      exact hk.symm ▸ a.2
    refine ⟨k, hkS, ?_⟩
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK
            ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) :=
        rfl
      _ = D.extensionNormalizedDegree K L hLK a.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hk

/-- Source-private M016.016 `frobeniusFixedField_mappedRelIndex`: the degree
image of `Σ` has relative index `d_K(σ)` in the degree image of `K`. -/
private theorem frobeniusFixedField_mappedRelIndex_aux (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
        D.degree.toMonoidHom).relIndex
      (K.field.toSubgroup.map D.degree.toMonoidHom) =
      D.frobeniusExponent K L hLK σ := by
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let dK : K.field.toSubgroup →* ZHatMul :=
    (D.normalizedDegree K).toMonoidHom
  let scale : ZHatMul →* ZHatMul :=
    (zHatPowNat (K.residueDegree : ℕ)).toMonoidHom
  have hraw : (D.restrictedDegree K.field).toMonoidHom = scale.comp dK := by
    apply MonoidHom.ext
    intro k
    apply Multiplicative.ext
    exact (D.residueDegree_nsmul_normalizedDegree K k).symm
  have hSigmaImage :
      (D.frobeniusFixedField K L hLK σ).toSubgroup.map
          D.degree.toMonoidHom =
        S.map (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k, hk, ?_⟩
      exact congrArg D.degree hkg
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.1, ⟨k, hk, rfl⟩, rfl⟩
  have hKimage :
      K.field.toSubgroup.map D.degree.toMonoidHom =
        (⊤ : Subgroup K.field.toSubgroup).map
          (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, trivial, rfl⟩
    · rintro ⟨k, _, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
  have hscale : Function.Injective scale := by
    intro x y hxy
    apply Multiplicative.ext
    apply zHatMulNat_injective K.residueDegree.property
    exact congrArg Multiplicative.toAdd hxy
  have htop : (⊤ : Subgroup K.field.toSubgroup).map dK = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨k, hk⟩ := D.normalizedDegree_surjective K z
    exact ⟨k, trivial, hk⟩
  have hindex :
      (zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range.index =
        D.frobeniusExponent K L hLK σ :=
    zHatMulNat_range_index _ (D.frobeniusExponent_pos_aux K L hLK σ)
  rw [hSigmaImage, hKimage, hraw]
  rw [← Subgroup.map_map, ← Subgroup.map_map]
  rw [Subgroup.relIndex_map_map_of_injective _ _ hscale]
  rw [show S.map dK =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range from
        D.frobeniusFixedSubgroupWithin_normalizedDegree_image_aux K L hLK σ]
  rw [htop, Subgroup.relIndex_top_right,
    D.frobeniusClosureDegree_range_aux K L hLK σ,
    AddSubgroup.index_toSubgroup, hindex]

/-- The actual relative residue quotient of the Frobenius fixed field over
`K` is finite.  Positivity of the computed mapped relative index gives an
honest finite-index witness before any natural-valued cardinality is formed. -/
theorem frobeniusFixedField_relativeResidueQuotientFinite
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusFixedField_relativeResidueQuotientFiniteStatement K L hLK σ := by
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
      D.degree.toMonoidHom).relIndex
        (K.field.toSubgroup.map D.degree.toMonoidHom) ≠ 0
  rw [D.frobeniusFixedField_mappedRelIndex_aux K L hLK σ]
  exact (D.frobeniusExponent_pos_aux K L hLK σ).ne'

end DegreeData

end

end Langlands.NYLL.ClassFormation

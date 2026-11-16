/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M014.039 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusClosure Statements module, the
proof of frobeniusClosureDegree_range (M014.030) and the published declarations
the proof uses, give the theorem the published proposition
frobeniusFixedField_finiteIndexStatement as its type, unfolded by an initial
show, and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. Four source prerequisites whose
proofs are not yet published are replaced by their source proofs, inlined as
local facts: frobeniusExponent_pos (M014.013) as hpos, the surjectivity
extensionNormalizedDegreeContinuous_surjective (M014.019) inside htopmap, the
injectivity extensionDegreeKernelRestriction_injective (M014.021) as hinj, and
the relative-index identity relIndex_eq_map_relIndex_mul_inf_ker_relIndex
(M006.009), specialized to the subgroups of this proof, as hindex together with
the source proofs of its two lemmas M006.007 and M006.008. The published
theorems normalizedDegree_ker and frobeniusClosureDegree_range have Statement
propositions as their types, so they are first restated as local equations.
The rest of the proof is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.U030.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U006.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U011.Proofs

/-!
# The Frobenius closure has finite index
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- finiteness of the Frobenius fixed field, in the Galois-dual form: the closed subgroup
`Γ = closure ⟨σ⟩` has finite index in `G(\widetilde L|K)`, hence its
fixed field `Σ` is finite over `K`. -/
theorem frobeniusFixedField_finiteIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusFixedField_finiteIndexStatement D K L hLK σ := by
  show Finite
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup)
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let dQ : Q →ₜ* ZHatMul :=
    D.extensionNormalizedDegreeContinuous K L hLK
  -- The source applies M014.013 `frobeniusExponent_pos`; `hpos` is its source proof.
  have hpos : 0 < D.frobeniusExponent K L hLK σ :=
    (Exists.choose_spec σ.2).1
  have hrange : (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range =
      AddSubgroup.toSubgroup
        ((zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range) :=
    D.frobeniusClosureDegree_range K L hLK σ
  have hΓmap : Γ.map dQ.toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
  have htopmap : (Subgroup.map dQ.toMonoidHom (⊤ : Subgroup Q)) = ⊤ := by
    apply top_unique
    intro z _
    -- The source applies M014.019 `extensionNormalizedDegreeContinuous_surjective`;
    -- the next two lines are its source proof.
    obtain ⟨k, hk⟩ := D.normalizedDegree_surjective K z
    exact ⟨QuotientGroup.mk k, trivial, hk⟩
  have himage : (Γ.map dQ.toMonoidHom).relIndex
      ((⊤ : Subgroup Q).map dQ.toMonoidHom) ≠ 0 := by
    rw [hΓmap, htopmap, Subgroup.relIndex_top_right,
      hrange,
      AddSubgroup.index_toSubgroup,
      zHatMulNat_range_index _ hpos]
    exact hpos.ne'
  let j := D.extensionDegreeKernelRestriction K L hLK
  -- The source applies M014.021 `extensionDegreeKernelRestriction_injective`;
  -- `hinj` is its source proof.
  have hinj : Function.Injective j := by
    intro a b hab
    let c := (a.1 : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)⁻¹ * b.1
    have hcRestriction : D.extensionRestriction K.field L hLK c = 1 := by
      dsimp [c]
      rw [map_mul, map_inv]
      change (D.extensionDegreeKernelRestriction K L hLK a)⁻¹ *
          D.extensionDegreeKernelRestriction K L hLK b = 1
      rw [hab, inv_mul_cancel]
    have hcDegree :
        D.extensionNormalizedDegreeContinuous K L hLK c = 1 := by
      dsimp [c]
      rw [map_mul, map_inv]
      change (D.extensionNormalizedDegreeContinuous K L hLK a.1)⁻¹ *
          D.extensionNormalizedDegreeContinuous K L hLK b.1 = 1
      have ha : D.extensionNormalizedDegreeContinuous K L hLK a.1 = 1 := a.2
      have hb : D.extensionNormalizedDegreeContinuous K L hLK b.1 = 1 := b.2
      rw [ha, hb, inv_one, one_mul]
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) c
    have hkE : k ∈ L.toSubgroup.subgroupOf K.field.toSubgroup := by
      apply (QuotientGroup.eq_one_iff k).mp
      rw [← hk] at hcRestriction
      exact hcRestriction
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      have hker :
          (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field :=
        D.normalizedDegree_ker K
      rw [← hker]
      change D.normalizedDegree K k = 1
      rw [← hk] at hcDegree
      exact hcDegree
    have hkc : k ∈ D.extensionInertiaWithin K.field L hLK :=
      ⟨hkE, hkI⟩
    have hcOne : c = 1 := by
      rw [← hk]
      exact (QuotientGroup.eq_one_iff k).mpr hkc
    apply Subtype.ext
    exact inv_mul_eq_one.mp hcOne
  let : Finite dQ.toMonoidHom.ker :=
    Finite.of_injective j hinj
  let T : Subgroup Q := (⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker
  let toKer : T → dQ.toMonoidHom.ker :=
    fun t => ⟨t.1, t.2.2⟩
  let : Finite T := Finite.of_injective toKer (by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : dQ.toMonoidHom.ker => x.1) hab)
  have hkernel : (Γ ⊓ dQ.toMonoidHom.ker).relIndex
      ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) ≠ 0 := by
    rw [Subgroup.relIndex]
    change ((Γ ⊓ dQ.toMonoidHom.ker).subgroupOf T).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  -- The source applies M006.009 `relIndex_eq_map_relIndex_mul_inf_ker_relIndex`
  -- with `d = dQ`, `L = Γ` and `K = ⊤`; `hindex` is its source proof, with the
  -- source proofs of M006.007 (`hsat`) and M006.008 (`hmapIndex`) inlined.
  have hindex : Γ.relIndex (⊤ : Subgroup Q) =
      (Γ.map dQ.toMonoidHom).relIndex ((⊤ : Subgroup Q).map dQ.toMonoidHom) *
        (Γ ⊓ dQ.toMonoidHom.ker).relIndex
          ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) := by
    have hLK' : Γ ≤ (⊤ : Subgroup Q) := le_top
    have hsat : Γ.relIndex ((⊤ : Subgroup Q) ⊓ (Γ ⊔ dQ.toMonoidHom.ker)) =
        (Γ ⊓ dQ.toMonoidHom.ker).relIndex
          ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) := by
      unfold Subgroup.relIndex
      exact Nat.card_congr (kernelCosetEquivSaturation dQ.toMonoidHom hLK').symm
    have hmapIndex :
        (Γ.map dQ.toMonoidHom).relIndex ((⊤ : Subgroup Q).map dQ.toMonoidHom) =
          ((⊤ : Subgroup Q) ⊓ (Γ ⊔ dQ.toMonoidHom.ker)).relIndex
            (⊤ : Subgroup Q) := by
      rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq,
        ← Subgroup.inf_relIndex_right, inf_comm]
    rw [hmapIndex, ← hsat, mul_comm]
    exact (Subgroup.relIndex_mul_relIndex Γ
      ((⊤ : Subgroup Q) ⊓ (Γ ⊔ dQ.toMonoidHom.ker)) (⊤ : Subgroup Q)
      (fun x hx ↦ ⟨hLK' hx, (show Γ ≤ Γ ⊔ dQ.toMonoidHom.ker from le_sup_left) hx⟩)
      inf_le_left).symm
  have hrel : Γ.relIndex (⊤ : Subgroup Q) ≠ 0 := by
    rw [hindex]
    exact Nat.mul_ne_zero himage hkernel
  apply (Subgroup.index_ne_zero_iff_finite).mp
  simpa [Γ, Q, Subgroup.relIndex_top_right] using hrel

end DegreeData

end Langlands.NYLL.ClassFormation

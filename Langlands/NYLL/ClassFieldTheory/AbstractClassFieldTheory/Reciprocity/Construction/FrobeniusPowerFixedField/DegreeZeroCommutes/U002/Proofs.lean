/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs

/-!
# NYLL M038.002: powers by the degree of a finite stage commute with degree zero

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.quotientPower_card_commutes_degreeZeroStatement` (M038.002) by
the source proof of `DegreeData.quotientPower_card_commutes_degreeZero` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type and
begin the proof with `show` stating it unfolded. The source proof applies
three results whose proofs are not in the Library; the port proves what it
needs locally:
- M038.001 `extensionInertia_commutes_of_mem_extensionSubgroup` is proved,
  by its source proof, as the private theorem `inertia_commutes_aux` with the
  unfolded statement (its use of the published `...Statement`-typed M011.010
  `normalizedDegree_ker` goes through the local fact `hker`, and its final
  source step `simp [mul_assoc]`, which does not close the goal with the
  published simp set, is replaced by
  `simpa [mul_assoc] using (D.fieldInertiaWithin K.field).mul_mem
  ((D.fieldInertiaWithin K.field).inv_mem htI) hconj`);
- in `hIP`, the source rewrites the hypothesis with M029.022
  `extensionSubgroup_maximalUnramifiedField` (whose inclusion argument is
  M029.020 `maximalUnramifiedField_le_of_le`) to place `x` in the subgroup of
  the maximal unramified field; the port obtains this membership directly,
  since by definition that subgroup is `L ⊓ ker d` and `x` lies in `L` and in
  the kernel.
Replace the source import by published modules, open `KummerTheory` for the
published `mem_extensionSubgroup_iff` (M022.001), whose `...Statement` type
is used through `.1` and `.2`, and omit the other unused opens and the rest
of the source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The source theorem M038.001
`DegreeData.extensionInertia_commutes_of_mem_extensionSubgroup` with its
source proof, under a private name. -/
private theorem inertia_commutes_aux (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k := by
  have hker : (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field :=
    D.normalizedDegree_ker K
  revert hq
  refine Quotient.inductionOn' q ?_
  intro t hdt
  have htI : t ∈ D.fieldInertiaWithin K.field := by
    rw [← hker]
    exact hdt
  change QuotientGroup.mk (k * t) = QuotientGroup.mk (t * k)
  apply QuotientGroup.eq.mpr
  constructor
  · change (k * t)⁻¹ * (t * k) ∈ extensionSubgroup K.field L hLK
    have hconj : t⁻¹ * k⁻¹ * t ∈ extensionSubgroup K.field L hLK := by
      simpa using hLnormal.conj_mem k⁻¹
        ((extensionSubgroup K.field L hLK).inv_mem hk) t⁻¹
    simpa [mul_assoc] using
      (extensionSubgroup K.field L hLK).mul_mem hconj hk
  · change (k * t)⁻¹ * (t * k) ∈ D.fieldInertiaWithin K.field
    have hconj : k⁻¹ * t * k ∈ D.fieldInertiaWithin K.field := by
      simpa using (inferInstance : (D.fieldInertiaWithin K.field).Normal).conj_mem
        t htI k⁻¹
    simpa [mul_assoc] using
      (D.fieldInertiaWithin K.field).mul_mem
        ((D.fieldInertiaWithin K.field).inv_mem htI) hconj

/-- Let `P/K` be a finite Galois subextension of `\widetilde L/K`
containing `L`.  The `|G(P/K)|`-th power of every element of
`G(\widetilde L/K)` fixes `P`, hence commutes with the degree-zero kernel.
This is the precise finite-stage input behind the choice
`n = [M:K]`, `σ = φⁿ`. -/
theorem quotientPower_card_commutes_degreeZero (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) :
    quotientPower_card_commutes_degreeZeroStatement D K L hLK P hPL q τ hτ := by
  show
    let n := Nat.card
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
    q ^ n * τ = τ * q ^ n
  let R := K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below
  let : Finite R := P.finite
  let n := Nat.card R
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field P.field P.below := by
    intro x hx
    have hxE : (x : G) ∈ D.maximalUnramifiedField L := by
      change (x : G) ∈ L.toSubgroup ⊓ D.degree.toMonoidHom.ker
      exact Subgroup.mem_inf.mpr ⟨hx.1, hx.2⟩
    apply (mem_extensionSubgroup_iff K.field P.field P.below x).2
    exact P.above hxE
  let rP : Q →* R :=
    QuotientGroup.map (D.extensionInertiaWithin K.field L hLK)
      (extensionSubgroup K.field P.field P.below)
      (MonoidHom.id K.field.toSubgroup) hIP
  let k : K.field.toSubgroup := Quotient.out (q ^ n)
  have hkq : (QuotientGroup.mk k : Q) = q ^ n :=
    Quotient.out_eq' (q ^ n)
  have hrPpow : rP (q ^ n) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  have hkP : k ∈ extensionSubgroup K.field P.field P.below := by
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k : R) = rP (QuotientGroup.mk k) := rfl
      _ = rP (q ^ n) := congrArg rP hkq
      _ = 1 := hrPpow
  have hkL : k ∈ extensionSubgroup K.field L hLK := by
    apply (mem_extensionSubgroup_iff K.field L hLK k).2
    exact hPL ((mem_extensionSubgroup_iff K.field P.field P.below k).1 hkP)
  have hcomm := inertia_commutes_aux D
    K L hLK k hkL τ hτ
  simpa [Q, n, hkq] using hcomm

end DegreeData

end degreeOnePowerFields

end

end Langlands.NYLL.ClassFormation

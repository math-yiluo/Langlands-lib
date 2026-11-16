# Inertia commutes with elements fixing the extension

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionInertia_commutes_of_mem_extensionSubgroup`, the proof phase of
M038.001 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m038).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionInertia_commutes_of_mem_extensionSubgroupStatement` applied to the
theorem's parameters:

```lean
theorem extensionInertia_commutes_of_mem_extensionSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    extensionInertia_commutes_of_mem_extensionSubgroupStatement D K L hLK k hk q hq
```

## Target and binders

The section variables are those of the published statement module and the source: `universe u` and `{G : Type u} [Group G] [TopologicalSpace G]`, in `section degreeOnePowerFields` and `namespace DegreeData`. The theorem takes `D`, `K`, `L`, `hLK`, the normality instance `hLnormal`, `k`, `hk`, `q` and `hq`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements`, the target is the proposition

```lean
(QuotientGroup.mk k :
    K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
  q * QuotientGroup.mk k
```

Here `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree` from `G` onto the profinite integers written multiplicatively; `K : FiniteResidueAbstractField D` (M010.021) is an abstract field `K.field` with finite residue quotient; `L` is a closed subgroup with `hLK : L ≤ K.field` such that `extensionSubgroup K.field L hLK` (M004.002, the subgroup `L` of `K.field` as a subgroup of `K.field`) is normal. `D.fieldInertiaWithin K.field` (M010.014) is the kernel of the degree restricted to `K.field`, the inertia subgroup `I_K`; `D.extensionInertiaWithin K.field L hLK` (M012.002) is `L ∩ I_K` inside `K.field`, so that the quotient `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` is the group `G(\widetilde L/K)`; and `D.extensionNormalizedDegree K L hLK` (M012.005) is the normalized degree `D.normalizedDegree K` (M011.006) of `K.field` factored through this quotient. The element `k` of `K.field` lies in `extensionSubgroup K.field L hLK` (`hk`, it fixes `L`), and `q` is an element of `G(\widetilde L/K)` of normalized degree one (`hq`, degree zero in additive notation). The target says that the class of `k` commutes with `q` in `G(\widetilde L/K)`; the hypotheses `hk` and `hq` are used by the proof. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements`, which defines the targets and imports, through the published `FrobeniusClosure.Definitions` and `NormSubgroup.Definitions` modules, `DegreeData` (M010.002), `FiniteResidueAbstractField` (M010.021), `fieldInertiaWithin` (M010.014) with its normality instance (M010.015), `extensionInertiaWithin` (M012.002), `extensionNormalizedDegree` (M012.005), `FrobeniusElements` (M012.009), `frobeniusExponent` (M014.012), `FiniteIntermediateField` (M029.001), `maximalUnramifiedField` (M029.016) and `extensionSubgroup` (M004.002);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`, the published proof of M011.010 `DegreeData.normalizedDegree_ker`, of type `normalizedDegree_kerStatement D K`, which unfolds to `(D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`.

The module opens `CyclicCohomology`, as the source does, for `extensionSubgroup`; the source's `open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators` are not needed, since none of their names or notation occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof states the published `D.normalizedDegree_ker K` as the local fact `hker` (its `...Statement` type is accepted by definitional unfolding, but `rw` needs the unfolded equation) and follows the source proof. By `Quotient.inductionOn'` it suffices to treat the class of `t : K.field` of degree zero (`hdt`); then `t ∈ D.fieldInertiaWithin K.field` (`htI`) by rewriting with `hker`. The claim `k t ≡ t k` modulo `L ∩ I_K` becomes, by `QuotientGroup.eq`, that `(k t)⁻¹ (t k)` lies in both `extensionSubgroup K.field L hLK` and `D.fieldInertiaWithin K.field`. For the first, `hconj : t⁻¹ k⁻¹ t ∈ L` follows from the normality of `L` in `K.field`, and the product with `hk` gives the claim (`simpa [mul_assoc]`). For the second, `hconj : k⁻¹ t k ∈ I_K` follows from the normality of `I_K` (M010.015), and the product of the inverse of `htI` with `hconj` gives the claim: the port closes this goal with `simpa [mul_assoc] using (D.fieldInertiaWithin K.field).mul_mem ((D.fieldInertiaWithin K.field).inv_mem htI) hconj`, because the source's closing `simp [mul_assoc]` does not close it with the simp set available from the Library.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`, lines 37–71](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean#L37-L71):
the docstring at lines 37–41 and the theorem at lines 42–71. It lies in `namespace ClassFormation` (line 19), with `open KummerTheory` (line 21) and `open CyclicCohomology` (line 22), after `universe u` (line 17), in its `noncomputable section` (line 26) with `open CategoryTheory` (line 28) and `open scoped BigOperators` (line 29), `section degreeOnePowerFields` (line 31), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 33) and `namespace DegreeData` (line 35). The source is:

```lean
/-- An element fixing `L` commutes modulo `G_{\widetilde L}` with every
degree-zero element of `G(\widetilde L/K)`.  Group-theoretically this is
`[G_L,I_K] ⊆ G_L ∩ I_K = G_{\widetilde L}`; it is the reason the
fields fixed by the powers of `φⁿ` in the universal norm-descent lemma are stable under the
elements `τᵢ` occurring in `(*)`. -/
theorem extensionInertia_commutes_of_mem_extensionSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k := by
  revert hq
  refine Quotient.inductionOn' q ?_
  intro t hdt
  have htI : t ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
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
    simp [mul_assoc]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`;
its SHA-256 is `4f9719760da9ac7344ece27b3aaf46d4acbd1d1295202dbb9eb84b41bc9b4256`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `extensionInertia_commutes_of_mem_extensionSubgroupStatement D K L hLK k hk q hq` as its type, and begin the proof with `show` stating it unfolded;
- state the published `...Statement`-typed M011.010 `D.normalizedDegree_ker K` unfolded as the local fact `hker` and rewrite with it in place of the source's `rw [← D.normalizedDegree_ker K]`;
- replace the closing `simp [mul_assoc]` by `simpa [mul_assoc] using (D.fieldInertiaWithin K.field).mul_mem ((D.fieldInertiaWithin K.field).inv_mem htI) hconj`;
- omit `open KummerTheory`, `open CategoryTheory`, `open scoped BigOperators` and all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M038.001. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

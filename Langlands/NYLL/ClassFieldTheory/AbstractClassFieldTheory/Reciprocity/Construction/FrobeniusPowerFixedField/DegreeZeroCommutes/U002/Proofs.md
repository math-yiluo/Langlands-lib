# Powers by the degree of a finite stage commute with degree zero

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.quotientPower_card_commutes_degreeZero`, the proof phase of
M038.002 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m038).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.quotientPower_card_commutes_degreeZeroStatement` applied to the
theorem's parameters:

```lean
theorem quotientPower_card_commutes_degreeZero (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) :
    quotientPower_card_commutes_degreeZeroStatement D K L hLK P hPL q τ hτ
```

## Target and binders

The section variables are those of the published statement module and the source: `universe u` and `{G : Type u} [Group G] [TopologicalSpace G]`, in `section degreeOnePowerFields` and `namespace DegreeData`. The theorem takes `D`, `K`, `L`, `hLK`, `hLnormal`, `P`, `hPL`, `hPnormal`, `q`, `τ` and `hτ`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements`, the target is the proposition

```lean
let n := Nat.card
  (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
q ^ n * τ = τ * q ^ n
```

Here `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree` from `G` onto the profinite integers written multiplicatively; `K : FiniteResidueAbstractField D` (M010.021) is an abstract field `K.field` with finite residue quotient; `L` is a closed subgroup with `hLK : L ≤ K.field` such that `extensionSubgroup K.field L hLK` (M004.002, the subgroup `L` of `K.field` as a subgroup of `K.field`) is normal. `D.fieldInertiaWithin K.field` (M010.014) is the kernel of the degree restricted to `K.field`, the inertia subgroup `I_K`; `D.extensionInertiaWithin K.field L hLK` (M012.002) is `L ∩ I_K` inside `K.field`, so that the quotient `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` is the group `G(\widetilde L/K)`; and `D.extensionNormalizedDegree K L hLK` (M012.005) is the normalized degree `D.normalizedDegree K` (M011.006) of `K.field` factored through this quotient. `D.maximalUnramifiedField L` (M029.016) is `L ⊓ D.inertia`, the subgroup of `\widetilde L`, and `P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field` (M029.001) is a closed subgroup `P.field` with `\widetilde L ≤ P.field` (`P.above`), `P.field ≤ K.field` (`P.below`) and finite index `P.finite`; `hPL` says `P.field ≤ L`, and `hPnormal` that `P.field` is normal in `K.field`. For `q τ` in `G(\widetilde L/K)` with `τ` of degree zero (`hτ`), the target says that `q ^ n` commutes with `τ`, where `n` is the index `[K.field : P.field]`, the order of `G(P/K)`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements`, which defines the targets and imports, through the published `FrobeniusClosure.Definitions` and `NormSubgroup.Definitions` modules, `DegreeData` (M010.002), `FiniteResidueAbstractField` (M010.021), `fieldInertiaWithin` (M010.014) with its normality instance (M010.015), `extensionInertiaWithin` (M012.002), `extensionNormalizedDegree` (M012.005), `FrobeniusElements` (M012.009), `frobeniusExponent` (M014.012), `FiniteIntermediateField` (M029.001), `maximalUnramifiedField` (M029.016) and `extensionSubgroup` (M004.002);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`, the published proof of M011.010 `DegreeData.normalizedDegree_ker`, of type `normalizedDegree_kerStatement D K`, which unfolds to `(D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`;
- `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs`, the published proof of M022.001 `KummerTheory.mem_extensionSubgroup_iff`, of type `mem_extensionSubgroup_iffStatement K L hLK k`, which unfolds to `k ∈ L.toSubgroup.subgroupOf K.toSubgroup ↔ (k : G) ∈ L`.

The module opens `KummerTheory` and `CyclicCohomology`, as the source does, for `mem_extensionSubgroup_iff` and `extensionSubgroup`; the source's `open CategoryTheory` and `open scoped BigOperators` are not needed, since none of their names or notation occur in the statement or the proof.

## Implemented proof

The source proof applies M038.001, whose proof is not yet in the Library; the module therefore first proves M038.001, with its unfolded statement and the proof described in its own module (`hker` for M011.010 and the explicit closing `simpa`), as the private theorem `inertia_commutes_aux`.

After `show` states the published proposition unfolded, the proof follows the source proof. Write `R` for the coset space of `P.field` in `K.field`, finite by `P.finite`, `n = Nat.card R` and `Q` for `G(\widetilde L/K)`. First `hIP` shows that `L ∩ I_K` lies in `P.field`: for `x` in it, `x` lies in `D.maximalUnramifiedField L`, and `P.above` places it in `P.field` (`mem_extensionSubgroup_iff` converts the membership). The source obtains the membership of `x` in the maximal unramified field by rewriting with M029.022 `extensionSubgroup_maximalUnramifiedField` (with the inclusion M029.020 `maximalUnramifiedField_le_of_le`), which are not yet in the Library; the port obtains it directly, since by definition (M029.016, M010.012, M010.006) that subgroup is `L ⊓ ker D.degree` and `x` lies in `L` and, being in `I_K`, in the kernel. With `rP : Q →* R` the induced map, `q ^ n` maps to `1` in `R` (`pow_card_eq_one'`), so a representative `k` of `q ^ n` lies in `P.field` and hence, by `hPL`, in `L`. Then `inertia_commutes_aux` (M038.001) for `k`, `τ` and `hτ` gives `k τ = τ k` in `Q`, which is the claim after `simpa [Q, n, hkq]`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`, lines 37–126](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean#L37-L126):
the docstring at lines 73–77 and the theorem at lines 78–126; lines 37–71 are the theorem M038.001 that the port proves as the private `inertia_commutes_aux`. It lies in `namespace ClassFormation` (line 19), with `open KummerTheory` (line 21) and `open CyclicCohomology` (line 22), after `universe u` (line 17), in its `noncomputable section` (line 26) with `open CategoryTheory` (line 28) and `open scoped BigOperators` (line 29), `section degreeOnePowerFields` (line 31), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 33) and `namespace DegreeData` (line 35). The source is:

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
    let n := Nat.card
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
    q ^ n * τ = τ * q ^ n := by
  let R := K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below
  let : Finite R := P.finite
  let n := Nat.card R
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field P.field P.below := by
    intro x hx
    have hxE : x ∈ extensionSubgroup K.field (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) := by
      rw [D.extensionSubgroup_maximalUnramifiedField K.field L hLK]
      exact hx
    apply (mem_extensionSubgroup_iff K.field P.field P.below x).2
    exact P.above
      ((mem_extensionSubgroup_iff K.field (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) x).1 hxE)
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
  have hcomm := D.extensionInertia_commutes_of_mem_extensionSubgroup
    K L hLK k hkL τ hτ
  simpa [Q, n, hkq] using hcomm
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`;
its SHA-256 is `4f9719760da9ac7344ece27b3aaf46d4acbd1d1295202dbb9eb84b41bc9b4256`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `quotientPower_card_commutes_degreeZeroStatement D K L hLK P hPL q τ hτ` as its type, and begin the proof with `show` stating it unfolded;
- prove the source theorem M038.001 `extensionInertia_commutes_of_mem_extensionSubgroup`, with its unfolded statement and its source proof (with `hker` and the closing `simpa` of the M038.001 module), as the private theorem `inertia_commutes_aux`, and apply it in place of `D.extensionInertia_commutes_of_mem_extensionSubgroup`;
- in `hIP`, replace the rewrite with `D.extensionSubgroup_maximalUnramifiedField K.field L hLK` (and the subsequent `mem_extensionSubgroup_iff` for the maximal unramified field) by the direct proof of `(x : G) ∈ D.maximalUnramifiedField L` with `change` to `L.toSubgroup ⊓ D.degree.toMonoidHom.ker` and `Subgroup.mem_inf`;
- omit `open CategoryTheory`, `open scoped BigOperators` and all other source declarations.

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

This module proves only M038.002. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

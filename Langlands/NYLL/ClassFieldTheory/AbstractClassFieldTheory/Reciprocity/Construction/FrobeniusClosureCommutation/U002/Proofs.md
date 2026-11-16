# A representative commuting with a Frobenius lift stabilizes its fixed field

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.conjugate_frobeniusFixedField_eq_of_commutes`, the proof phase of
M042.002 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m042).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.conjugate_frobeniusFixedField_eq_of_commutesStatement` applied to the
theorem's parameters:

```lean
theorem conjugate_frobeniusFixedField_eq_of_commutes (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    conjugate_frobeniusFixedField_eq_of_commutesStatement D K L hLK σ q hq
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type u} [Group G] [TopologicalSpace G]` (the ambient group with its group structure and topology, in the source universe `u`), then `D : DegreeData G` (M010.002, a continuous surjective degree homomorphism `G → ℤ̂`), the instance arguments `[IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]` (so `G` is profinite), `K : FiniteResidueAbstractField D` (M010.021, an abstract field with finite residue degree), `L : ClosedSubgroup G` and `hLK : L.toSubgroup ≤ K.field.toSubgroup` (an abstract extension `L` of `K`), the instance argument `[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` (normality of `L` in `K`), `σ : D.FrobeniusElements K L hLK` (a Frobenius lift, M012.009: a class `σ.1` in the quotient `Q = K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` of `G_K` by `G_L ⊓ I_K` (M012.002) whose normalized degree is a positive power of the generator), an element `q : Q` and `hq : q * σ.1 = σ.1 * q`. The source writes the subgroup in `hLnormal` as `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation.Statements`, the target is the proposition

```lean
let k : K.field.toSubgroup := Quotient.out q
conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
  D.frobeniusFixedField K L hLK σ
```

That is, for the chosen representative `k` of `q` in `G_K`, conjugating the Frobenius fixed field `D.frobeniusFixedField K L hLK σ` (M016.004, the closed subgroup `Σ` of `G` that is the image in `G` of the preimage in `G_K` of the Frobenius closure) by `k.1⁻¹` (M026.001 `conjugateClosedSubgroup`) gives the same closed subgroup. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation.U001.Proofs`, the proof of M042.001 (`frobeniusClosure_commutes_of_commutes_generator`; staged in the same task as candidate `76be8c88-c464-4e22-ae59-7f3a525adbbb` and not yet in Library `72480b70c88adff84a438bd7029d64ee3977469c`, so this module must be integrated after it), which also brings the target module and the definitions `frobeniusClosure` (M014.023), `frobeniusFixedSubgroupWithin` (M016.001), `frobeniusFixedField` (M016.004) and `conjugateClosedSubgroup` (M026.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`, the published proof of `conjugateClosedSubgroup_mem` (M026.002): `x ∈ conjugateClosedSubgroup T s ↔ s * x * s⁻¹ ∈ T`.

The module opens no namespace.

## Implemented proof

The proof unfolds the target with `show` and `dsimp only`, fixes `k := Quotient.out q` with `hkq : QuotientGroup.mk k = q`, and proves the equality of closed subgroups by extensionality in `x`. It rewrites membership in the conjugate with `conjugateClosedSubgroup_mem` (M026.002); because that published theorem has the type `conjugateClosedSubgroup_memStatement T k.1⁻¹ x`, the proof first states the unfolded equivalence as a local `have hmem` proved by the theorem and rewrites with `hmem` (the source rewrites with the theorem directly). For the forward inclusion, a witness `t ∈ G_K` in the fixed subgroup with `t = k⁻¹ x k` gives `x = k t k⁻¹ ∈ G_K`; by M042.001 (the theorem of the module imported above) `q` commutes with the class of `t`, so the class of `k t k⁻¹` is `q t q⁻¹ = t`, in the Frobenius closure, and `x` is in the fixed field. The reverse inclusion is symmetric with `k⁻¹ x k`. These steps are the source's.

The development check with `lean_check` in the approved environment, over Library
`72480b70c88adff84a438bd7029d64ee3977469c` together with the M042.001 module, compiled
the module with no errors or warnings; the theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusClosureCommutation.lean`, lines 70–167](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusClosureCommutation.lean#L70-L167):
the docstring at lines 70–71 and the theorem at lines 72–167. It lies in `namespace ClassFormation` (line 19), with `open KummerTheory` and `open CyclicCohomology` (lines 21–22), its `noncomputable section` (line 26), `open CategoryTheory` and `open scoped BigOperators` (lines 28–29), `section frobeniusClosureCommutation` (line 31), the group variables of line 33 and `namespace DegreeData` (line 35); `universe u` is line 17. The source is:

```lean
/-- If a quotient element commutes with the Frobenius lift, its chosen
representative stabilizes the corresponding fixed field. -/
theorem conjugate_frobeniusFixedField_eq_of_commutes (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ := by
  dsimp only
  let T := D.frobeniusFixedField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [this]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q * QuotientGroup.mk t * q⁻¹ = QuotientGroup.mk t := by
        calc
          q * QuotientGroup.mk t * q⁻¹ =
              (QuotientGroup.mk t * q) * q⁻¹ := by rw [hcomm']
          _ = QuotientGroup.mk t := mul_inv_cancel_right _ _
      change QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      have hxval : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hyClosure : QuotientGroup.mk yK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q⁻¹ * QuotientGroup.mk t * q = QuotientGroup.mk t := by
        calc
          q⁻¹ * QuotientGroup.mk t * q =
              q⁻¹ * (QuotientGroup.mk t * q) := by simp [mul_assoc]
          _ = q⁻¹ * (q * QuotientGroup.mk t) := by rw [hcomm']
          _ = QuotientGroup.mk t := inv_mul_cancel_left _ _
      have hyval : yK = k⁻¹ * t * k := by
        apply Subtype.ext
        dsimp [yK]
        have htxval : t.1 = x := by simpa using htx
        rw [htxval]
      rw [hyval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)⁻¹ *
          QuotientGroup.mk t * QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    refine ⟨yK, hyClosure, ?_⟩
    simp [yK]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusClosureCommutation.lean`;
its SHA-256 is `4dd15338da3a0523169c4e611714e9356e93234e2d659a92bafe286b0b2302e2`.

Modifications by Worker 5264 on 15 November 2026:

- give the theorem the published proposition `conjugate_frobeniusFixedField_eq_of_commutesStatement D K L hLK σ q hq` as its type, unfolded by an initial `show` before the source `dsimp only`;
- add the `Langlands.NYLL` namespace prefix and replace the source import by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- replace `rw [conjugateClosedSubgroup_mem]` by a local `have hmem` stating the unfolded equivalence for `x`, proved by the published theorem `conjugateClosedSubgroup_mem`, followed by `rw [hmem]`;
- omit `open KummerTheory`, `open CyclicCohomology`, `open CategoryTheory`, `open scoped BigOperators` and all other source declarations; keep the universe, the noncomputable section, the section, the variable line and the namespaces.

Worker 755 checked this draft on 16 November 2026 against the current Library and
the retained source and staged it unchanged in Lean; the Markdown was edited only to
state the M042.001 dependency and the compilation base precisely.

The binders, the local definitions and every tactic step not listed above are the source's. The retained original belongs to registered source
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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M042.002. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

# The Frobenius closure has finite index

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_finiteIndex`, the proof phase of
M014.039 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m014).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_finiteIndexStatement` applied to the
theorem's parameters:

```lean
theorem frobeniusFixedField_finiteIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusFixedField_finiteIndexStatement D K L hLK σ
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type u} [Group G] [TopologicalSpace G]`, then `D : DegreeData G` (M010.002), `[IsTopologicalGroup G] [CompactSpace G] [T2Space G]`, `K : FiniteResidueAbstractField D` (M010.021), a closed subgroup `L` with `hLK : L.toSubgroup ≤ K.field.toSubgroup`, the instances `hLnormal` (`G_L` is normal in `G_K`) and `hLfinite` (`G_K ⧸ G_L` is finite), and a Frobenius lift `σ : D.FrobeniusElements K L hLK` (M012.009). The source writes the normality instance and the finiteness instance with `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements`, the target is the proposition

```lean
Finite
  ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
    (D.frobeniusClosure K L hLK σ).toSubgroup)
```

That is, the Frobenius closure `Γ` (M014.023), a subgroup of `Q = G_K ⧸ I_L` where `I_L = extensionInertiaWithin K.field L hLK` (M012.002), has finite index in `Q`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements`, which defines the target and imports the published definitions `frobeniusClosure` (M014.023) and `extensionInertiaWithin` (M012.002);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.U030.Proofs`, the proof of M014.030 `frobeniusClosureDegree_range` in this task, which also brings the published definitions `extensionNormalizedDegreeContinuous` (M014.016) and `extensionDegreeKernelRestriction` (M014.020);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs`, the published proof of M011.009 `normalizedDegree_surjective`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`, the published proof of M011.010 `normalizedDegree_ker`: the kernel of `D.normalizedDegree K` is `D.fieldInertiaWithin K.field`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U006.Definitions`, the published definition M006.006 `kernelCosetEquivSaturation`, the bijection between the kernel cosets and the saturated cosets of a subgroup pair;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U011.Proofs`, the published proof of M009.011 `zHatMulNat_range_index`: for `0 < n` the subgroup `n ℤ̂` has index `n`.

The module opens no namespace.

## Implemented proof

After `show` unfolds the target, the proof follows the source. Let `dQ : Q → ℤ̂` be the continuous normalized degree M014.016. The relative index of `Γ` in `Q` is the product of the index of `dQ(Γ)` in `dQ(Q)` and the relative index of `Γ ⊓ ker dQ` in `ker dQ`, and both factors are nonzero. The first: `dQ(Q)` is all of `ℤ̂` and `dQ(Γ)` is the image of `frobeniusClosureDegree`, equal to `n ℤ̂` by M014.030 (stated first as the local equation `hrange`, since its type is a Statement proposition), of index `n > 0` by M009.011. The second: restriction to `G_K ⧸ G_L` is injective on `ker dQ`, so `ker dQ` is finite because `G_K ⧸ G_L` is. Four source prerequisites whose proofs are not in the Library are replaced by their source proofs, inlined as local facts with comments: `hpos : 0 < n` is the source proof `(Exists.choose_spec σ.2).1` of M014.013 `frobeniusExponent_pos`; the surjectivity of `dQ`, M014.019 `extensionNormalizedDegreeContinuous_surjective`, is replaced inside `htopmap` by its source argument, the published surjectivity M011.009 of the normalized degree on `G_K` applied to a lift; `hinj` is the source proof of the injectivity M014.021 `extensionDegreeKernelRestriction_injective`, which uses the published kernel M011.010 (stated first as the local equation `hker`); and `hindex` is the source proof of the relative-index identity M006.009 `relIndex_eq_map_relIndex_mul_inf_ker_relIndex` for `d = dQ`, `L = Γ` and `K = ⊤`, with the source proofs of its two lemmas inlined: M006.007 as `hsat`, by the published bijection M006.006, and M006.008 as `hmapIndex`, by Mathlib relative-index rewriting. Finally the relative index of `Γ` in `⊤` is the index of `Γ`, and a nonzero index gives a finite quotient.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`, lines 860–921](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean#L860-L921):
the docstring at lines 860–862 and the theorem at lines 863–921. It lies in `namespace ClassFormation` (line 19), with `open CyclicCohomology` (line 21), its `noncomputable section` (line 25), `universe u` (line 27), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 29) and `namespace DegreeData` (line 300). The inlined prerequisites are M014.013 (lines 310–316), M014.019 (lines 381–390) and M014.021 (lines 404–444) of the same file, and M006.007–M006.009 of `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean` (lines 93–98, 102–107 and 114–121). The source is:

```lean
/-- finiteness of the Frobenius fixed field, in the Galois-dual form: the closed subgroup
`Γ = closure ⟨σ⟩` has finite index in `G(\widetilde L|K)`, hence its
fixed field `Σ` is finite over `K`. -/
theorem frobeniusFixedField_finiteIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let dQ : Q →ₜ* ZHatMul :=
    D.extensionNormalizedDegreeContinuous K L hLK
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
    obtain ⟨q, rfl⟩ :=
      D.extensionNormalizedDegreeContinuous_surjective K L hLK z
    exact ⟨q, trivial, rfl⟩
  have himage : (Γ.map dQ.toMonoidHom).relIndex
      ((⊤ : Subgroup Q).map dQ.toMonoidHom) ≠ 0 := by
    rw [hΓmap, htopmap, Subgroup.relIndex_top_right,
      D.frobeniusClosureDegree_range K L hLK σ,
      AddSubgroup.index_toSubgroup,
      zHatMulNat_range_index _
        (D.frobeniusExponent_pos K L hLK σ)]
    exact (D.frobeniusExponent_pos K L hLK σ).ne'
  let j := D.extensionDegreeKernelRestriction K L hLK
  let : Finite dQ.toMonoidHom.ker :=
    Finite.of_injective j
      (D.extensionDegreeKernelRestriction_injective K L hLK)
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
  have hrel : Γ.relIndex (⊤ : Subgroup Q) ≠ 0 := by
    rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex
      dQ.toMonoidHom le_top]
    exact Nat.mul_ne_zero himage hkernel
  apply (Subgroup.index_ne_zero_iff_finite).mp
  simpa [Γ, Q, Subgroup.relIndex_top_right] using hrel
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`;
its SHA-256 is `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.

Modifications by Worker 5264 on 15 November 2026:

- give the theorem the published proposition `frobeniusFixedField_finiteIndexStatement D K L hLK σ` as its type, unfolded by an initial `show`;
- state the source's fact `D.frobeniusExponent_pos K L hLK σ` (M014.013, not proved in the Library) once as the local fact `hpos`, proved by its source proof term, and use `hpos` in `himage`;
- in `htopmap`, replace the source's use of M014.019 (not proved in the Library) by its source argument: obtain `k` with `D.normalizedDegree K k = z` from M011.009 and give `QuotientGroup.mk k`; the source's final `simpa using hk` becomes the direct term `⟨QuotientGroup.mk k, trivial, hk⟩`;
- state the published M014.030, whose type is its Statement proposition, as the local equation `hrange` and rewrite with it in `himage`;
- prove the injectivity used for `Finite dQ.toMonoidHom.ker` (M014.021, not proved in the Library) as the local fact `hinj` by its source proof, in which `simpa using hcRestriction` and `simpa using hcDegree` become `exact`, and `rw [← D.normalizedDegree_ker K]` uses the published M011.010 through the local equation `hker` with its unfolded type;
- replace the source's rewrite with M006.009 `relIndex_eq_map_relIndex_mul_inf_ker_relIndex dQ.toMonoidHom le_top` (not proved in the Library) by the local equation `hindex`, its source proof for these subgroups, with the source proofs of M006.007 and M006.008 inlined as `hsat` and `hmapIndex`;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` in the normality and finiteness binders and in the inlined fact `hkE` to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- omit `open CyclicCohomology`, the `noncomputable section` and all other source declarations; keep `universe u` and the variable line.

The docstring, the binders and all other proof steps are the source's. The retained original belongs to registered source
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

This module proves only M014.039. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

# NYLL M073.005: the norm of the fixed representation is the relative norm

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.extensionFixedRepresentation_norm_coeStatement`
by the theorem
`Langlands.NYLL.ClassFormation.extensionFixedRepresentation_norm_coe`.
The theorem's type is exactly that proposition applied to its source
parameters, `extensionFixedRepresentation_norm_coeStatement A K L hLK hnormal a`,
with the finite coset-type instance supplied by elaboration.

## Target and parameters

The theorem has, in this order, implicit `G : IntegralRepGroupType` (the
published alias of `Type 0`), the instances `[Group G]` and
`[TopologicalSpace G]`, explicit `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup` and
`hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`, the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, then
explicit `a : (extensionFixedRepresentation A K L hLK hnormal).V`: the
statement's telescope with the same binder kinds. Like the statement, it has
no universe parameter. No premise is added. Unfolding the proposition gives,
after the local instances `letI := hnormal` and
`letI := Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))`,

```lean
((extensionFixedRepresentation A K L hLK hnormal).norm.hom a).1 =
  ((relativeNorm A K L hLK
    (extensionFixedRepresentationEquiv A K L hLK hnormal a) :
      ambientFixedAddSubgroup A K) : A.V)
```

Here `extensionFixedRepresentation A K L hLK hnormal` (published M004.003) is
the representation of the finite quotient `K/L` on the `L`-fixed vectors of
`A` restricted to `K`; its vectors are subtypes of `A.V`, and `.1` is the
underlying ambient vector. `Rep.norm` is Mathlib's norm endomorphism
`x ↦ ∑ g, ρ g x` over the finite quotient. The right side is the ambient
vector of the published M024.009 relative norm of `a`, viewed through the
published M073.001 carrier equivalence `extensionFixedRepresentationEquiv`
as an element of `ambientFixedAddSubgroup A L`. The assertion says that the
representation norm of `a`, computed in the quotient representation, is the
actual coset-sum relative norm of the same fixed coefficient.

## Implemented proof

The complete proof body is

```lean
  unfold extensionFixedRepresentation_norm_coeStatement
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
  simp only [Rep.norm, Representation.norm]
  let M := extensionFixedRepresentation A K L hLK hnormal
  let : Module ℤ M.V := M.hV2
  change ((∑ q, M.ρ q) a).1 =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [LinearMap.sum_apply]
  let coeToAmbient :
      (extensionFixedRepresentation A K L hLK hnormal).V →+ A.V :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change coeToAmbient (∑ q, M.ρ q a) =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact extensionFixedRepresentation_action_coe A K L hLK hnormal q a
```

The `unfold` exposes the proposition, and the two `let`s install the same
normality and `Fintype.ofFinite` instances that the statement's `letI`s use.
`simp only [Rep.norm, Representation.norm]` unfolds the definitions of
Mathlib's `Rep.norm` and `Representation.norm` on the left, whose
representation norm is by definition the endomorphism sum `∑ q, M.ρ q`
evaluated at `a`. The first `change` (with the module structure `M.hV2` of the carrier made available)
restates the goal as the ambient vector of `(∑ q, M.ρ q) a` on the left and
the coset sum `∑ q, relativeCosetAction A K L hLK (extensionFixedRepresentationEquiv A K L hLK hnormal a) q`
on the right. The right side is reached by definitional unfolding: the
published `relativeNorm` sends a fixed coefficient to the subtype element
whose value is the published M024.005 `relativeNormValue`, and that value is
by definition this coset sum over the same `Fintype.ofFinite` structure.

Mathlib's `LinearMap.sum_apply` turns `(∑ q, M.ρ q) a` into `∑ q, M.ρ q a`.
The local additive homomorphism `coeToAmbient`, the subtype coercion from the
carrier to `A.V`, makes the outer `.1` an application of an additive map, so
the second `change` restates the left side as `coeToAmbient (∑ q, M.ρ q a)`,
and `map_sum` pushes it inside the sum. `Finset.sum_congr rfl` reduces the
equation to the termwise identities `(M.ρ q a).1 = relativeCosetAction A K L hLK (extensionFixedRepresentationEquiv A K L hLK hnormal a) q`
for every coset `q`, which is exactly the published M073.004 theorem
`extensionFixedRepresentation_action_coe A K L hLK hnormal q a`.

## Dependencies

The direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Norm.Statements`,
which supplies the target statement and through its imports the published
`extensionFixedRepresentation`, `extensionFixedRepresentationEquiv`,
`relativeNorm`, `relativeNormValue` and `relativeCosetAction`; and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs`,
which supplies the published M073.004 theorem
`extensionFixedRepresentation_action_coe`. Mathlib supplies `Rep.norm`,
`Representation.norm`, `LinearMap.sum_apply`, `map_sum` and
`Finset.sum_congr`. Both project imports are in the Library; no published
Lean/Markdown pair is changed. The proof does not use the M024.010 theorem
`relativeNorm_apply_coe` and imports no unpublished module.

## Pinned source and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`,
whose whole-file SHA-256
`8124bbdd42702e1dba3060f8a2f14c6d66ead33c113d0b4310bc6157fea19bb9`
Worker 744 recomputed from the retained copy under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`
on 16 November 2026 UTC; it matches the
[port partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m073),
which records no patch10 edit for M073. The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; the
attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The passage is
[lines 102–139](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean#L102-L139),
the last declaration of the file: docstring at 102–103, theorem name and
telescope at 104–109, the asserted type at 110–116 and proof at 117–139. The
enclosing context is namespace `ClassFormation` (line 18), the opens at lines
20 and 22, `noncomputable section` (line 26), `open scoped BigOperators`
(line 28) and the section variables at line 31.

The source proof has, in order, the two `let`s (lines 117–119),
`rw [relativeNorm_apply_coe]` (line 120),
`simp only [Rep.norm, Representation.norm, relativeNormValue]` (line 121) and
then exactly the steps from `let M` onward reproduced above (lines 122–139).
This proof differs only as follows:

1. It starts with `unfold extensionFixedRepresentation_norm_coeStatement`,
   since its stated type is the named proposition.
2. It drops `rw [relativeNorm_apply_coe]`. That M024.010 equation holds by
   `rfl` (its source proof, line 172 of `Degree/Norm.lean`), and the first
   `change` already reaches the coset-sum form of the right side by
   definitional unfolding. The proof therefore needs neither the M024.010
   proof (not yet in the Library) nor a local copy of it.
3. Accordingly it drops `relativeNormValue` from the `simp only` list: without
   the rewrite, no `relativeNormValue` term occurs in the goal at that point.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `extensionFixedRepresentation_norm_coe` | Published `extensionFixedRepresentation_norm_coeStatement` |
| Proof `extensionFixedRepresentation_norm_coe` | This theorem, same adapted name |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, as in the statement |
| `extensionFixedRepresentation_action_coe` (M073.004) | Published theorem of the same adapted name |
| `relativeNorm_apply_coe` (M024.010) | Not used; replaced by definitional unfolding |
| `extensionFixedRepresentation`, `extensionFixedRepresentationEquiv`, `relativeNorm`, `relativeNormValue`, `relativeCosetAction` | Existing published data (M004.003, M073.001, M024.009, M024.005, M024.001) |

Modifications by Worker 744 on 16 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source imports with the two focused
published imports; give the theorem the published proposition applied to its
parameters as its type and unfold it first; write every occurrence of
`extensionSubgroup K L hLK` as the published `Subgroup.subgroupOf` body;
drop the `rw [relativeNorm_apply_coe]` step and `relativeNormValue` from the
`simp only` list, as explained above; omit all other source declarations of
the file. The original docstring, the `noncomputable section`, the opens of
`KummerTheory`, `CyclicCohomology` and scoped `BigOperators`, and all other
proof steps are retained.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 744's dated modification
record. Worker 744 extracted this proof directly from the pinned original and
the published statement; no project draft was reused and there are no
project coauthors. The statement pair (Worker 196) and the M073.004 proof
(Worker 190) are imported unchanged; no imported Library file is edited.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development
`lean_check` compiled the module with no errors or warnings, and declaration
inspection reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`, with no universe parameter. Development compilation is
separate from acceptance: publication under `lean.proof@1` also requires the
Lake, kernel and exact-target checks, independent semantic review and
Integrator publication.

This proof covers only M073.005. The M074.004 proof of the same task uses the
same argument through a private local lemma until this theorem is in the
Library. Every host class-formation, cup, transfer, Tate or reciprocity
target remains separate work.

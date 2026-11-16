# NYLL M074.004: the relative norm is the first cyclic Tate differential

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.cyclicFixedCycleEquiv_relativeNormStatement`
by the theorem
`Langlands.NYLL.ClassFormation.cyclicFixedCycleEquiv_relativeNorm`.
The theorem's type is exactly that proposition applied to its source
parameters,
`cyclicFixedCycleEquiv_relativeNormStatement A K L hLK hnormal hfinite g hg a`.

## Target and parameters

The theorem has, in this order, implicit `G : IntegralRepGroupType` (the
published alias of `Type 0`), the instances `[Group G]` and
`[TopologicalSpace G]`, then explicit `A : Rep ℤ G`,
`K L : ClosedSubgroup G`, `hLK : L.toSubgroup ≤ K.toSubgroup`,
`hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`,
`hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))`,
`g : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)`,
`hg : ∀ x, x ∈ Subgroup.zpowers g` and `a : ambientFixedAddSubgroup A L`:
the statement's telescope with the same binder kinds. Like the statement, it
has no universe parameter. No premise is added.

Unfolding the proposition gives a goal that first introduces, by `let`, the
five local instances of the statement (normality `hnormal`, finiteness
`hfinite`, `Fintype.ofFinite`, cyclicity of `K/L` from the generator `g`, and
`IsCyclic.commGroup`) and the local objects
`M := extensionFixedRepresentation A K L hLK hnormal` and
`T := Rep.FiniteCyclicGroup.normHomCompSub M g`, and then asserts

```lean
cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
    (relativeNorm A K L hLK a) =
  T.moduleCatToCycles
    ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)
```

Here `T` is Mathlib's short complex `M --N--> M --(ρ(g) - 1)--> M` with `N`
the representation norm, and `T.moduleCatToCycles` is its first map
co-restricted to the kernel of the second. The published M074.001
`cyclicFixedCycleEquiv` identifies the fixed group `A_K` with that kernel.
The assertion says that, under this identification, the relative norm of a
fixed coefficient `a` of `L` is the image of the corresponding vector of `M`
under the first differential of the cyclic Tate complex.

## Implemented proof

The complete proof consists of a private local lemma and the theorem.

The private lemma `extensionFixedRepresentation_norm_coe_local` has the same
telescope as the M073.005 statement and proves exactly the published
proposition
`extensionFixedRepresentation_norm_coeStatement A K L hLK hnormal a`, by the
same proof as the M073.005 proof of this task (file
`Langlands/NYLL/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation/Norm/U005/Proofs.lean`):

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

After unfolding and installing the statement's local instances, the
definitions of Mathlib's `Rep.norm` and `Representation.norm` are unfolded;
the first `change` restates the goal as the ambient vector of
`(∑ q, M.ρ q) a` against the coset sum of `relativeCosetAction` (which is, by
definitional unfolding, the value of the published `relativeNorm`);
`LinearMap.sum_apply` evaluates the endomorphism sum; the subtype coercion,
packaged as the additive homomorphism `coeToAmbient`, is pushed through the
finite sum by `map_sum`; and `Finset.sum_congr rfl` reduces the equation to
the termwise identities, each of which is the published M073.004 theorem
`extensionFixedRepresentation_action_coe`.

The theorem's proof body is

```lean
  unfold cyclicFixedCycleEquiv_relativeNormStatement
  intro instNormal instFinite instFintype instCyclic instCommGroup M T
  apply Subtype.ext
  apply Subtype.ext
  exact (extensionFixedRepresentation_norm_coe_local
    A K L hLK hnormal
      ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)).symm
```

The `unfold` exposes the proposition and the `intro` introduces its five
local instances and the objects `M` and `T`. Both sides are elements of the
kernel submodule of the second map of `T`, whose elements are subtypes of
`M.V`, whose elements are in turn subtypes of `A.V`; the two `Subtype.ext`
steps reduce the goal to the equality of the underlying vectors of `A.V`. By
definitional unfolding, the left side is the value of
`relativeNorm A K L hLK a` (the published M074.001 `cyclicFixedCycleEquiv`
sends `b` to the vector of `M` with the same underlying value, through
`fixedFieldInclusion` and the inverse carrier equivalence), and the right
side is the underlying vector of `M.norm.hom x` for
`x := (extensionFixedRepresentationEquiv A K L hLK hnormal).symm a`
(`moduleCatToCycles` co-restricts the first map of `T`, which is the norm of
`M`). The local lemma at `x` states that this norm vector equals the value of
`relativeNorm A K L hLK (extensionFixedRepresentationEquiv A K L hLK hnormal x)`,
and `extensionFixedRepresentationEquiv` applied to its inverse at `a` reduces
definitionally to `a`. Its symmetric form therefore closes the goal.

## Dependencies

The direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.RelativeNorm.Statements`
(the target statement, and through its imports the published
`cyclicFixedCycleEquiv`, `relativeNorm` and Mathlib's finite cyclic
complexes),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Norm.Statements`
(the published M073.005 statement proved by the private lemma) and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs`
(the published M073.004 theorem used by the private lemma). All three are in
the Library; no published Lean/Markdown pair is changed.

The source proof uses the M073.005 theorem
`extensionFixedRepresentation_norm_coe`, whose proof is staged separately in
this task and is not yet in the Library. Following the task's instruction to
prove locally what is not yet published, under a non-conflicting name, this
module proves the published M073.005 Statement in the `private` lemma
`extensionFixedRepresentation_norm_coe_local` and publishes no second copy
under the adapted name. The lemma's type is the published Statement itself,
not a restatement.

## Pinned source and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`,
whose whole-file SHA-256
`6dc5f10e7546a7b85d7712388b443344fe87679ef13d0eadb0f3451f925c731a`
Worker 744 recomputed from the retained copy under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`
on 16 November 2026 UTC; it matches the
[port partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m074),
which records no patch10 edit for M074. The private lemma follows the source
M073.005 proof in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`,
lines 117–139 (whole-file SHA-256
`8124bbdd42702e1dba3060f8a2f14c6d66ead33c113d0b4310bc6157fea19bb9`). The
retained source is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; the
attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The passage is
[lines 170–199](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean#L170-L199):
docstring at 170–171, theorem name and telescope at 172–179, asserted type
at 180–193 and proof at 194–199; the next unit starts at line 201 (docstring)
and 203 (declaration). The enclosing context is namespace `ClassFormation`
(line 21), the opens at lines 23, 25 and 31, `noncomputable section`
(line 29) and the section variables at line 34.

The source proof is `intro instNormal instFinite instFintype instCyclic
instCommGroup M T` (line 194), `apply Subtype.ext` twice (lines 195–196) and
`exact (extensionFixedRepresentation_norm_coe A K L hLK hnormal
((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)).symm`
(lines 197–199). This proof differs only as follows:

1. It starts with `unfold cyclicFixedCycleEquiv_relativeNormStatement`, since
   its stated type is the named proposition.
2. Its final `exact` applies the private lemma
   `extensionFixedRepresentation_norm_coe_local` in place of the source
   theorem `extensionFixedRepresentation_norm_coe`, with the same arguments.
3. The private lemma's proof is the source M073.005 proof without its
   `rw [relativeNorm_apply_coe]` step and without `relativeNormValue` in its
   `simp only` list: that M024.010 equation holds by `rfl`, and the following
   `change` reaches the same goal by definitional unfolding. It begins with
   `unfold extensionFixedRepresentation_norm_coeStatement`, since its type is
   the named proposition.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `cyclicFixedCycleEquiv_relativeNorm` | Published `cyclicFixedCycleEquiv_relativeNormStatement` |
| Proof `cyclicFixedCycleEquiv_relativeNorm` | This theorem, same adapted name |
| `extensionFixedRepresentation_norm_coe` (M073.005) | Private lemma `extensionFixedRepresentation_norm_coe_local` proving the published M073.005 Statement |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, as in the statement |
| `isCyclic_of_generator g hg` | `isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩`, as in the published statement |
| `cyclicFixedCycleEquiv`, `extensionFixedRepresentation`, `extensionFixedRepresentationEquiv`, `relativeNorm` | Existing published data (M074.001, M004.003, M073.001, M024.009) |

Modifications by Worker 744 on 16 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source imports with the three focused
published imports; give the theorem the published proposition applied to its
parameters as its type and unfold it first; write every occurrence of
`extensionSubgroup K L hLK` as the published `Subgroup.subgroupOf` body;
replace the use of the unpublished M073.005 theorem by the private local
lemma described above; omit all other source declarations of the file. The
original docstring, the `noncomputable section`, the source opens of
`KummerTheory`, `CyclicCohomology` and `CategoryTheory`, and all other proof
steps are retained.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 744's dated modification
record. Worker 744 extracted this proof directly from the pinned original and
the published statements; no project draft was reused and there are no
project coauthors. The statement pairs (Worker 196) and the M073.004 proof
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

This proof covers only M074.004. It supplies one comparison used by the
cyclic norm-quotient identification; the kernel theorem M074.005 and every
host class-formation, cup, transfer, Tate or reciprocity target remain
separate work.

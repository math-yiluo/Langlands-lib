# NYLL M020.009: pulled-back cyclic factor kernels are closed

This module proves the published Library proposition
`Langlands.NYLL.KummerTheory.cyclicFactorSubgroup_isClosedStatement` by the
theorem `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup_isClosed`. The
theorem's type is exactly that proposition applied to its source parameters,
`cyclicFactorSubgroup_isClosedStatement K L hLK f`, with the instances
`[IsTopologicalGroup G]`, `hnormal` and `hfinite` passed by instance
resolution (the bound instances themselves, since local instances are found
first).

Its target import is
`Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Statements`
([`Statements.lean`](../Statements.lean)). That published Lean/Markdown pair
and everything it imports are unchanged.

## Target and parameters

The theorem has the universe parameters `u_1` (for `G`) and `u_2` (for `C`),
as the published proposition does. Its parameters are, in this order:

1. implicit `{G : Type u_1}` with instances `[Group G] [TopologicalSpace G]`
   (section variable line) and `[IsTopologicalGroup G]` (the later section
   variable line);
2. explicit `(K L : ClosedSubgroup G)` and
   `hLK : L.toSubgroup ≤ K.toSubgroup`;
3. the instances
   `[hnormal : (extensionSubgroup (G := G) K L hLK).Normal]` and
   `[hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]`;
4. implicit `{C : Type u_2}` with `[Group C]`;
5. explicit `f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C`.

Unfolding the proposition gives

```lean
IsClosed
  (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
    Set K.toSubgroup)
```

Here `Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK` (M004.002)
is the abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`, that is, `G_L`
regarded as a subgroup of `G_K`, and
`Langlands.NYLL.KummerTheory.cyclicFactorSubgroup H f` (M020.002) is the
kernel of `f.comp (QuotientGroup.mk' H)`. So: for closed subgroups `L ≤ K`
of a topological group `G` such that `G_L` is normal of finite index in
`G_K`, and any homomorphism `f` from `G_K / G_L` to a group `C`, the preimage
in `G_K` of the kernel of `f` is closed in `G_K`.

## Implemented proof

The proof is the source tactic proof, with one replaced name.

1. `let H := extensionSubgroup (G := G) K L hLK` names the subgroup.
2. `let : IsClosed (H : Set K.toSubgroup) := extensionSubgroup_isClosed_local K L hLK`
   puts the closedness of `H` in `K.toSubgroup` into the context. Mathlib's
   `IsClosed` is a class, so this becomes a local instance. The source calls
   `extensionSubgroup_isClosed` (M020.008) here; this file calls the private
   theorem `extensionSubgroup_isClosed_local` described below instead.
3. `change IsClosed ((QuotientGroup.mk' H) ⁻¹' (MonoidHom.ker f : Set (K.toSubgroup ⧸ H)))`
   replaces the goal by the closedness of the preimage of `ker f` under the
   quotient map. This is definitionally the proposition: through the
   Statement definition and the definition of `cyclicFactorSubgroup`, the
   carrier of the kernel of `f.comp (QuotientGroup.mk' H)` is the set of `x`
   with `f (QuotientGroup.mk' H x) = 1`.
4. `exact (isClosed_discrete _).preimage QuotientGroup.continuous_mk` closes
   it. `isClosed_discrete` needs `DiscreteTopology (K.toSubgroup ⧸ H)`, which
   instance resolution finds as Mathlib's `Finite.instDiscreteTopology` (a
   finite T1 space is discrete) from:
   - `hfinite`, the finiteness of `K.toSubgroup ⧸ H`;
   - `QuotientGroup.instT1Space`: the quotient of a group with separately
     continuous multiplication by a closed subgroup is T1. Its closedness
     argument is the local instance of step 2, and its
     `SeparatelyContinuousMul K.toSubgroup` argument comes from
     `IsTopologicalGroup G` through Mathlib's instance that a subgroup of a
     topological group is a topological group.

   Every set in a discrete space is closed, and the preimage of a closed set
   under the continuous quotient map `QuotientGroup.mk` is closed.

A traced instance search in a private scratch check confirmed this
resolution, including that the bound `hfinite` and the local closedness
instance are the ones used.

### Private local copy of M020.008

The M020.008 theorem `Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed`
is staged separately by this task (candidate
`1e0df87a-4e3c-4fa5-8e61-d6892f7740bc`) and is not yet in the Library, so it
cannot be imported. As the task allows, this file proves what it needs
locally under a non-conflicting private name:

```lean
private theorem extensionSubgroup_isClosed_local
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup)
```

Its type is the source conclusion of M020.008, stated over the section
variable `G` (placed before `variable [IsTopologicalGroup G]`, so it assumes
only `[Group G] [TopologicalSpace G]`). Its proof is the source proof of
M020.008: `change` to the preimage of `L` under the inclusion `K → G`, then
`L.isClosed'.preimage continuous_subtype_val`. It is not a second public copy
of M020.008. Once M020.008 is published, an integrator may replace it by the
published theorem without changing the main proof.

The development check of the draft module (diagnostic
`fb557bca-24b8-49ee-b9a6-51ad7d4227f1`) reports no errors or warnings. The
theorem has universe parameters `u_1` and `u_2`, and its axioms are only
`propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup_isClosedStatement`
  (M020.009 statement), used only by definitional unfolding.
- The published definition
  `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup` (M020.002, in the
  sibling `Definitions` module) and the published abbreviation
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), reached
  through the import chain; both are used only by definitional unfolding.
- The private `extensionSubgroup_isClosed_local` above.
- Mathlib: `ClosedSubgroup` and its field `isClosed'`, `Subgroup.subgroupOf`,
  `IsClosed.preimage` (`Mathlib/Topology/Continuous.lean`, line 188),
  `continuous_subtype_val` (`Mathlib/Topology/Constructions.lean`, line 380),
  `isClosed_discrete` (`Mathlib/Topology/Order.lean`, line 323),
  `QuotientGroup.mk'`, `QuotientGroup.continuous_mk` and
  `QuotientGroup.instT1Space`
  (`Mathlib/Topology/Algebra/Group/Quotient.lean`, lines 44 and 109),
  `Finite.instDiscreteTopology` (`Mathlib/Topology/Separation/Basic.lean`,
  line 830), the subgroup topological-group instance
  (`Mathlib/Topology/Algebra/Group/Subgroup.lean`, line 30) and
  `MonoidHom.ker`. Line numbers refer to Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.

No other NYLL declaration is used, and no host class-formation, cup,
transfer, Tate or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean:144–162`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean#L144-L162).
Line 144 is the section variable `[IsTopologicalGroup G]`, 146–148 the
docstring, 149–157 the signature and 158–162 the proof. The theorem lies in
`namespace KummerTheory` (line 25, with `open CyclicCohomology` at line 27),
the `noncomputable section` (line 31) and
`section ClosedCyclicSubextensions` (line 131) with the variable line 133
`{G : Type*} [Group G] [TopologicalSpace G]`; the source of M020.008, whose
proof the private local copy repeats, is lines 135–142. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m020)
lists this theorem as M020.009 (source unit from line 149; the next unit
starts at line 166). The whole-file SHA-256 is
`abedaf33dffa23e93392885b9c29e77ead8a9452ee32d9100614f6f0ac731033`,
recomputed by Worker 395 on 15 November 2026 UTC from the retained snapshot.

| Original in `KummerTheory` | Adapted in `Langlands.NYLL.KummerTheory` |
| --- | --- |
| Asserted type of `cyclicFactorSubgroup_isClosed` (M020.009) | Published `cyclicFactorSubgroup_isClosedStatement` in KummerAbelianCyclicFactors.Statements |
| Proof `cyclicFactorSubgroup_isClosed` | This theorem of the same adapted name in KummerAbelianCyclicFactors.U009.Proofs |
| `extensionSubgroup_isClosed` (M020.008), as used by this proof | Private `extensionSubgroup_isClosed_local` in this file |

Worker 395 made only these changes on 15 November 2026 UTC:

- prefix the namespace with `Langlands.NYLL`;
- replace the two source imports by the sole published Statements import;
- state the theorem's type as the published proposition applied to
  `K L hLK f`;
- replace the proof's call of `extensionSubgroup_isClosed` by the private
  local copy `extensionSubgroup_isClosed_local`, with the source proof and
  conclusion of M020.008 but stated over the section variable `G` instead of
  its own `{G : Type*} [Group G] [TopologicalSpace G]` binders;
- open `Langlands.NYLL.CyclicCohomology` (the port of the source's
  `open CyclicCohomology`) so that `extensionSubgroup` resolves to the
  published abbreviation;
- omit the other declarations of the source file.

The section name, the two variable lines, the `noncomputable section`, the
docstring, the theorem name, the binders with their names and order, and the
proof tactics apart from the replaced name are unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors. Worker 4918's statement is used unchanged.

The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M020.009. It does not publish M020.008 under its own
name, and it is not a class-formation, cup, transfer, Tate or reciprocity
result.

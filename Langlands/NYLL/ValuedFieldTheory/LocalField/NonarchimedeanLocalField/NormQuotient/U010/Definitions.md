# The norm quotient as a quotient by an equal subgroup

`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq` is the
multiplicative equivalence from the published general norm quotient
`Langlands.NYLL.LocalFieldTheory.NormQuotient K L` to the concrete quotient
group `Kˣ ⧸ N`, for any subgroup `N` of `Kˣ` that is known to equal the norm
subgroup. Its complete declaration telescope is

```lean
normQuotientEquivOfSubgroupEq.{u} (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L = N) :
    Langlands.NYLL.LocalFieldTheory.NormQuotient K L ≃* (Kˣ ⧸ N)
```

The only universe parameter is `u`. It is arbitrary and shared by the two
fields. `K` and `L` are explicit. `Field K`, `Field L` and `Algebra K L` are
instance-implicit. The subgroup `N` and the equality `h` are explicit. The
declaration is an ordinary `def` of data, not a proposition.

## Meaning of the inputs and the result

The published dependencies define

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

So `localNormSubgroup K L` is the actual image of the unit norm map
`Lˣ → Kˣ`, and `NormQuotient K L` is `Kˣ` modulo that image. The subgroup
`N` is an arbitrary subgroup of `Kˣ`, given in any form. The hypothesis
`h : localNormSubgroup K L = N` says that `N` is exactly the norm image. A
typical use is a subgroup described in another way, for example as the
kernel of a map, once it has been shown to equal the norm image.

The result is the group isomorphism between `NormQuotient K L` and `Kˣ ⧸ N`
that preserves representatives. Its forward map sends the norm class of
`x : Kˣ` to the coset of `x` modulo `N`. Its inverse map sends the coset of
`x` modulo `N` to the norm class of `x`. Both maps are well defined because
the two subgroups are equal, so two units have the same class on one side
exactly when they have the same class on the other side.

There is no premise that `N` is normal. `Kˣ` is commutative, so every
subgroup of it is normal, and Lean infers this. The instance is Mathlib's
`Subgroup.normal_of_isMulCommutative`
(`Mathlib/Algebra/Group/Subgroup/Defs.lean` lines 629–631).

The two multiplication structures in the declared type are:

- on the source `NormQuotient K L`, the `Mul` projection of the published
  named instance `normQuotientCommGroup K L` (M093.003);
- on the target `Kˣ ⧸ N`, the `Mul` projection of Mathlib's
  `QuotientGroup.Quotient.group N`, with the normality argument inferred as
  above.

Both are the usual coset multiplication: the product of the classes of `x`
and `y` is the class of `x * y`.

## Construction

The source body is kept exactly:

```lean
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ N)
  exact QuotientGroup.quotientMulEquivOfEq h
```

The `change` step exposes the published quotient definition. The goal becomes
an equivalence between the concrete quotients `Kˣ ⧸ localNormSubgroup K L`
and `Kˣ ⧸ N`. Lean accepts this step because the goals are definitionally
equal, including their `Mul` structures.

The second step reuses Mathlib's `QuotientGroup.quotientMulEquivOfEq`,
defined in the approved `Mathlib/GroupTheory/QuotientGroup/Basic.lean` lines
162–168 (docstring, attribute and definition). For a group `G`, two
subgroups `M` and `N` with `M.Normal` and `N.Normal`, and `h : M = N`, it is
the group isomorphism `G ⧸ M ≃* G ⧸ N`
whose underlying bijection is `Subgroup.quotientEquivOfEq h`
(`Mathlib/GroupTheory/Coset/Defs.lean` lines 266–272). That bijection has
forward map `Quotient.map' id _` and inverse map `Quotient.map' id _`: both
are induced by the identity of `G`, so both keep the representative. Lines
170–173 of the same Mathlib file state `quotientMulEquivOfEq_mk`: on the
class of `x` the equivalence returns the class of `x`, by `rfl`. No new
quotient, projection or equivalence is built.

Here `G = Kˣ`, `M = localNormSubgroup K L` and the `N` of the declaration.
The two normality arguments are found by instance search. The compiler
stores them as the auto-generated auxiliary theorems
`normQuotientEquivOfSubgroupEq._proof_1` (normality of `N`) and
`normQuotientEquivOfSubgroupEq._proof_2` (normality of
`localNormSubgroup K L`). Both are `Subgroup.normal_of_isMulCommutative`.
They are implementation details, not public interfaces.

The elaborated value is `id (QuotientGroup.quotientMulEquivOfEq h)`. The
outer `id` is the type hint inserted by `change`. The generated equation
lemma `normQuotientEquivOfSubgroupEq.eq_1` states this value. Inside the
retained `noncomputable section`, Lean marks the definition noncomputable.

## Transparency and interface boundary

`NormQuotient` and `normQuotientEquivOfSubgroupEq` are ordinary
semireducible definitions, not reducible abbreviations. At Lean's default
transparency the following hold by `rfl`:

- the equivalence sends `normClass K L x` to the class of `x` in `Kˣ ⧸ N`;
- its inverse sends the class of `x` in `Kˣ ⧸ N` to `normClass K L x`;
- viewed on the concrete quotient, it equals
  `QuotientGroup.quotientMulEquivOfEq h`, its inverse equals
  `QuotientGroup.quotientMulEquivOfEq h.symm`, and its underlying bijection
  equals `Subgroup.quotientEquivOfEq h`;
- its composite with `normClass K L` is `QuotientGroup.mk' N`.

At reducible transparency, `with_reducible rfl` does not prove the
evaluation on `normClass K L x`. Also, `simp only
[QuotientGroup.quotientMulEquivOfEq_mk]` does not rewrite an application of
the unexpanded name. After `unfold normQuotientEquivOfSubgroupEq normClass`,
Mathlib's `QuotientGroup.quotientMulEquivOfEq_mk` closes that goal.

The public evaluation theorem `normQuotientEquivOfSubgroupEq_normClass`, its
statement target and its proof form the separate later unit M093.011. This
unit publishes only the equivalence. It adds no theorem, `simp` lemma or
instance.

When `N` is `localNormSubgroup K L` itself and `h` is `rfl`, the equivalence
agrees with the published `normQuotientConcreteEquiv K L` (M093.004) on every
element. This is checked by extensionality and quotient induction, not by
`rfl`: Lean has no definitional eta rule for quotients, so
`Quotient.map' id _ q` is not definitionally `q` for a variable `q`. The two
declarations remain separate. `normQuotientConcreteEquiv` only changes the
presentation of the same quotient. This one accepts any subgroup together with
a proof that it equals the norm image.

## General norm convention

The definition uses Mathlib's general `Algebra.norm K`, through the
published `normUnits`, `localNormSubgroup` and `NormQuotient`. That norm is
defined for every `K`-algebra `L`, with no finite-module hypothesis. In the
approved `Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define it as the
determinant of multiplication. Lines 76–79 prove
`Algebra.norm_eq_one_of_not_module_finite`: if `L` is not a finite
`K`-module, the norm is constantly `1`. Then `localNormSubgroup K L` is the
trivial subgroup `⊥`. In that case the hypothesis `h` can only hold for
`N = ⊥`, and the equivalence identifies `NormQuotient K L` with `Kˣ ⧸ ⊥`.

There is no finite-dimensionality, separability, Galois, local-field,
valuation, topology, surjectivity or exact-kernel hypothesis, exactly as in
the source. The construction needs none: Mathlib's equivalence exists for
any two equal subgroups. A finiteness premise would restrict the declaration
without being used. It would also change the source telescope and break
agreement with the general published dependencies. Results that need
finiteness add it themselves.

## Source and adaptation

This is source unit M093.010 in the published NYLL declaration partition
`notes/reuse/nyll-public-port/m073-m096.md`, where it follows
`M093.009.END`. The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. It is kept in the registered
source `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The
relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`,
verified again for this task.

Lines 1–166 of the 381-line original were read for this task. Lines 1–5
carry the attribution. Line 24 declares the universes `u v`. Lines 26–91
hold the published subgroup, quotient, group instance, representation
equivalence, class map, lift and their theorems. The selected definition is
lines 93–101, quoted exactly:

```lean
/-- Identify a norm quotient with any concrete quotient once its defining
subgroup has been identified.  This is the sole public boundary for such
representation changes. -/
def normQuotientEquivOfSubgroupEq
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) :
    NormQuotient K L ≃* Kˣ ⧸ N := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ N)
  exact QuotientGroup.quotientMulEquivOfEq h
```

The docstring is lines 93–95, the declaration lines 96–99 and the body
lines 100–101. The evaluation theorem at lines 103–113 (M093.011),
`normQuotientEquivOfNormSubgroupEq` at lines 115–122 (M093.012) and all
later declarations are excluded.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfSubgroupEq` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq` |

Only the namespace prefix changes. The parameters, their binder kinds, the
result type, the docstring and the two-step body are unchanged. The source
universe `v` is not used by this declaration and is omitted, so `u` is the
only universe. The source's `noncomputable section` is kept. Inside the
namespace, `localNormSubgroup`, `NormQuotient` and the source-side instance
resolve to the published M093.001, M093.002 and M093.003 adaptations of
source lines 27, 31 and 35. The published partition records no patch10
change to this module.

The docstring calls this "the sole public boundary for such representation
changes". In this Library it is one public equivalence among others: the
published `normQuotientConcreteEquiv` is another, and the later source units
M093.012 and M093.014 add more. The docstring is kept verbatim as part of the
source, and its wording does not restrict how clients may use the Library.

In the pinned source tree this definition is used in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/UnramifiedConductor.lean`
line 103,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`
line 173 and
`Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean`
line 915. Those uses belong to later modules and are not ported here.

## Imports, reuse and searches

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U009.Proofs`.
This respects the partition's `M093.009.END` dependency. Its unchanged
published chain is U009 Proofs → U009 Statements → U008 Proofs → U008
Statements → U007 → U006 Proofs → U006 Statements → U005 → U004 → U003 →
U002 → U001 → NormUnits/U002 → `Mathlib.RingTheory.Norm.Transitivity`. That
chain supplies the unit norm, its range, the named quotient and its group
instance, `normClass`, and Mathlib's quotient API, including
`QuotientGroup.quotientMulEquivOfEq`. The development build confirms that
no direct Mathlib import is needed. The source module's direct imports of
`Mathlib.Data.Finset.Basic`, `Mathlib.GroupTheory.QuotientGroup.Basic`,
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` and
`Mathlib.RingTheory.Norm.Basic` are not repeated. The definition uses no
theorem of M092 or M093 and no later M093 declaration. Every imported
Lean/Markdown pair is unchanged.

Fresh searches of TaskHub tasks, the current Library, staged candidates and
the approved Mathlib found no existing `normQuotientEquivOfSubgroupEq` and no
duplicate task. Both revisions of shared draft
`b66bd2bc-abd3-4ea5-ae34-af7cdbeac0a3` contain byte-identical copies of the
source file (same SHA-256); they were not reused. Host declarations also use
`QuotientGroup.quotientMulEquivOfEq` inside more restricted constructions:
`Langlands.LocalClassField.finiteNormResidueEquiv`
(`Langlands/ClassFieldTheory/Local/FiniteArtin.lean` line 76, which needs a
topological field and a finite abelian extension) and the proof of
`unramifiedCyclicNormQuotient`
(`Langlands/ClassFieldTheory/Local/UnramifiedCyclicNormQuotientProof.lean`
line 72). Neither replaces this unrestricted named NYLL equivalence. No host
declaration is changed or compared by a public theorem here.

The errata locations in the workspace, the project and the current Library
were checked for the source registration above and for
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). No
applicable erratum was found.

## Development checks

The approved Lean service (environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) built the module with zero
errors and zero warnings. Inspection of the unapplied declaration reports a
definition with the single universe parameter `u`. It lists only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`, which come
from the Mathlib declarations it uses.

A separate private probe also built without errors. Its only warnings come
from the probe itself, which prints the auxiliary normality theorems. The
probe checks the following:

- the unapplied constant has seven binders with the kinds listed above, and
  its result head is `MulEquiv` applied to four arguments;
- the source `Mul` argument is syntactically the instance that inference
  returns for `Mul (NormQuotient K L)`, the projection of
  `normQuotientCommGroup K L`; the target `Mul` argument is syntactically the
  inferred one for `Kˣ ⧸ N`, the projection of
  `QuotientGroup.Quotient.group N`;
- the elaborated value and the two auxiliary normality theorems described
  above;
- the `rfl` equalities and the transparency failures described above;
- multiplicativity on classes: the product of `normClass K L x` and
  `normClass K L y` goes to the class of `x * y`;
- agreement with `normQuotientConcreteEquiv K L` when `h` is `rfl`;
- uniqueness: any equivalence `NormQuotient K L ≃* Kˣ ⧸ N` that sends each
  `normClass K L x` to the class of `x` equals this one;
- if `L` is not a finite `K`-module, `localNormSubgroup K L = ⊥`;
- instantiation with fields in `Type` and in `Type 3`.

These private checks are not part of the public candidate. They support
independent review. They are not acceptance evidence, and they are not
additional public theorem units.

## Scope

This unit supplies only the group isomorphism from the named norm quotient
to the quotient by an equal subgroup. It gives no Artin map, reciprocity
law, norm-kernel computation, host quotient or evaluation adapter, finiteness
or index result, quotient topology or continuity statement. It leaves the
parent finite reciprocity task open.

## Attribution and changes

The original 2026 Naganori Yamaguchi copyright and author header is kept
verbatim, including “Naganori Yamaguchi (assisted by OpenAI Codex)”. The
source is licensed under Apache-2.0. The Lean file adds an explicit
modification record dated 30 October 2026. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are kept through the
submission's `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Both
files are byte-identical to the original. The source NOTICE has no
third-party entry for NormQuotient, and its Anthropic FLT ValuedFieldTheory
list does not include `NormQuotient.lean`.

Worker 1097 extracted and documented M093.010 on 30 October 2026, added the
namespace prefix and the modification record, replaced the source imports
with the published U009 proof module, and omitted the unused universe and
all other source declarations. No other worker's draft or implementation was
reused.

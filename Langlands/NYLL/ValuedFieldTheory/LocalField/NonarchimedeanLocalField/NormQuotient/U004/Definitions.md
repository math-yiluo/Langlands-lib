# The concrete representation of the general norm quotient

`Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv` is the
multiplicative equivalence from the published general norm quotient
`Langlands.NYLL.LocalFieldTheory.NormQuotient K L` to the concrete quotient
group `Kˣ ⧸ Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L`. Its
complete declaration telescope is

```lean
normQuotientConcreteEquiv.{u} (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Langlands.NYLL.LocalFieldTheory.NormQuotient K L ≃*
      (Kˣ ⧸ Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L)
```

Here `u` is arbitrary and shared by the two fields. `K` and `L` are
explicit, and the three instance arguments are instance-implicit. The
declaration is an ordinary `def` of data, not a proposition.

Mathematically, `NormQuotient K L` is `Kˣ ⧸ N`, where `N` is the published
norm image subgroup `localNormSubgroup K L`. That subgroup is
`(normUnits K L).range`, and `normUnits K L` is
`Units.map (Algebra.norm K)` on `Lˣ`. The equivalence is the identity map
of `Kˣ ⧸ N`, seen as a group isomorphism. Its forward map sends each norm
class to itself, viewed as a coset in the concrete quotient. Its inverse map
sends each coset to itself, viewed as a norm class.

## Representation boundary

As in the source, `NormQuotient K L` is an ordinary (semireducible)
definition whose value is `Kˣ ⧸ localNormSubgroup K L`. The two types are
definitionally equal, but they are different expressions, and
`NormQuotient` is not reducible. For `CommGroup (NormQuotient K L)`,
inference returns the published named instance `normQuotientCommGroup K L`.
For the concrete quotient it returns Mathlib's
`QuotientGroup.Quotient.commGroup (localNormSubgroup K L)`.

The source docstring, kept verbatim, says that clients needing
quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. The equivalence is that explicit bridge. It turns
an element or homomorphism on the named type into one on the concrete
quotient, where Mathlib's `QuotientGroup` API applies. It does this without
asking clients to rely on the unfolding of `NormQuotient`. The equivalence
does not change the group: on both sides the elements are the same cosets
and the operations are the same quotient operations.

The two multiplication structures in the declared type are:

- on the source `NormQuotient K L`, the `Mul` projection of the published
  named instance `normQuotientCommGroup K L` (M093.003). That instance is
  definitionally Mathlib's `QuotientGroup.Quotient.commGroup N`;
- on the target `Kˣ ⧸ N`, the `Mul` projection of Mathlib's
  `QuotientGroup.Quotient.group N` from
  `Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 71–73. Inference
  supplies its normality argument as
  `Subgroup.normal_of_isMulCommutative (localNormSubgroup K L)`, since `Kˣ`
  is commutative.

Both are the standard coset multiplication: the product of the classes of
`x` and `y` is the class of `x * y`. They are equal at Lean's default
transparency. This agreement is what lets the identity equivalence of the
concrete quotient have the declared type.

## Why the general norm convention is kept

There is no finite-dimensional, separable, Galois, local-field, valuation,
or topology hypothesis, exactly as in the source. Both sides of the
equivalence are built from Mathlib's general `Algebra.norm K`, which is
defined for every `K`-algebra `L`. When `L` is not a finite `K`-module, that
norm is constantly `1` (`Algebra.norm_eq_one_of_not_module_finite`). Then
`N` is the trivial subgroup `⊥`, as the private check below verifies, and
both quotients are copies of `Kˣ`.

This convention is kept for three reasons.

- It preserves the source telescope, which the M093 partition and its later
  units rely on.
- The construction needs no hypothesis: the identity equivalence exists for
  every subgroup `N`, so a finiteness premise would only restrict the
  declaration without being used.
- It matches the published `NormQuotient` and `normQuotientCommGroup`, which
  also carry no finiteness premise.

Downstream statements about local fields add finiteness and other
hypotheses where their mathematics needs them. This definition assumes none
and asserts nothing about index, openness or finiteness.

## Original and adapted declaration

This extraction is M093.004 of the accepted NYLL declaration partition.
Its original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Lines 1–5 contain the attribution and line 24 declares the source universes
`u v`. Lines 26–28 contain `localNormSubgroup`, lines 30–32 contain
`NormQuotient` and lines 34–38 contain `normQuotientCommGroup`. Lines 40–47
contain this definition: its docstring is on lines 40–42 and its declaration
on lines 43–47. The original file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete original file was read. In the pinned source tree, the only
other use of this name is in
`Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormApproximation/FinitePlaces.lean`
line 359, which is not part of this unit.

The retained original is in the `n-yamaguchi-0729--ClassFieldTheory/source/`
directory of registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The related attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published partition records no patch10 modification to this module.
The project, workspace and current Library errata locations contain no
applicable erratum for either registered source.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientConcreteEquiv` | `Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv` |

Only the namespace prefix changes. The source parameters, result type,
docstring and two-step tactic body are preserved:

```lean
  change (Kˣ ⧸ localNormSubgroup K L) ≃* Kˣ ⧸ localNormSubgroup K L
  exact MulEquiv.refl _
```

The `change` step exposes the published quotient definition: the goal
becomes the concrete quotient's self-equivalence. Lean accepts this step
because the two goals are definitionally equal, including their `Mul`
structures. The second step uses Mathlib's existing `MulEquiv.refl` from
`Mathlib/Algebra/Group/Equiv/Defs.lean` lines 256–259. That equivalence is
`Equiv.refl` together with the multiplicativity proof `fun _ _ => rfl`, so
both its forward and inverse functions are the identity. No substitute
quotient or equivalence is built.

The elaborated value is
`id (MulEquiv.refl (Kˣ ⧸ localNormSubgroup K L))`. The outer `id` is the
type hint inserted by `change`. The generated equation lemma
`normQuotientConcreteEquiv.eq_1` states exactly this value. Inside the
namespace, `NormQuotient` and `localNormSubgroup` resolve to the published
M093.002 and M093.001 adaptations of source lines 31 and 27. The instance
on the source side is the published M093.003 adaptation of source line 35.
The unused universe `v` is omitted. The source's `noncomputable section` is
retained.

## Imports and dependency pruning

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U003.Definitions`,
which supplies `normQuotientCommGroup`. The current Library's corresponding
Lean and Markdown were checked before reuse. That module imports only the
published M093.002 module `NormQuotient.U002.Definitions`, which imports
only the M093.001 module `NormQuotient.U001.Definitions`. That module in
turn imports only
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
whose sole import is `Mathlib.RingTheory.Norm.Transitivity`. No other NYLL
or Library module is in the import closure.

No extra import is needed. A scan of Mathlib's import headers finds
`Mathlib.Algebra.Group.Equiv.Defs`, which declares `MulEquiv` and
`MulEquiv.refl`, in the transitive closure of
`Mathlib.RingTheory.Norm.Transitivity`. The same is true of
`Mathlib.GroupTheory.QuotientGroup.Defs`, as recorded for M093.003. The
successful build below confirms this. As in M093.002 and M093.003, the
source module's direct imports of `Mathlib.Data.Finset.Basic`,
`Mathlib.GroupTheory.QuotientGroup.Basic`,
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` and
`Mathlib.RingTheory.Norm.Basic` are not repeated.

The partition's dependency `M093.003.END` is met by the published instance.
The equivalence needs none of M092's evaluation, negation or tower results
and no later M093 declaration.

## Machine checks

A Lean-service build and declaration inspection succeeded with Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, without errors or
warnings. Inspection reports a definition with the single universe parameter
`u`. It lists only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, inherited from the Mathlib declarations it uses; no new axiom
occurs.

A separate private check also succeeded without errors or warnings. It
verified the following.

- The unapplied constant has exactly the telescope above. A metaprogram
  confirmed five binders: `K` and `L` explicit and the three instances
  instance-implicit, with result head `MulEquiv` applied to four arguments.
- The source `Mul` argument is syntactically the instance that inference
  returns for `Mul (NormQuotient K L)` under exactly the three instance hypotheses. It
  is the `Mul` projection of `normQuotientCommGroup K L`. The target `Mul`
  argument is syntactically the instance inferred for
  `Mul (Kˣ ⧸ localNormSubgroup K L)`. It is the `Mul` projection of
  `QuotientGroup.Quotient.group (localNormSubgroup K L)` and does not
  mention the named instance. Its normality argument is inferred as
  `Subgroup.normal_of_isMulCommutative`.
- Reflexivity at default transparency proves that the equivalence equals
  `MulEquiv.refl (Kˣ ⧸ localNormSubgroup K L)` and that its underlying
  `Equiv` equals `Equiv.refl`. It also proves that the forward map, the
  inverse map, `toFun` and `invFun` are all `id`, and that each sends an
  element to itself.
- After `change` exposes `NormQuotient K L` as the concrete quotient, the
  forward map is again the identity by reflexivity. After
  `unfold normQuotientConcreteEquiv`, Mathlib's `MulEquiv.refl_apply`
  closes the same goal.
- On the class of a unit `x`, both maps return the class of `x`. The
  equivalence carries the product of two norm classes to the concrete
  product by reflexivity, and the named product of the classes of `x` and
  `y` goes to the class of `x * y`.
- The concrete target quotient equals the quotient by
  `(Units.map (Algebra.norm K : L →* K)).range` by reflexivity.
- If `L` is not a finite `K`-module, `localNormSubgroup K L = ⊥`.

The check also records the transparency boundary with `fail_if_success`.

- The source and target types, and their `Mul` structures, are
  definitionally equal at default transparency. They are not equal at
  reducible transparency, nor the `Mul` structures at
  reducible-and-instances transparency.
- `normQuotientConcreteEquiv` is an ordinary definition. At reducible
  transparency reflexivity therefore does not prove that it acts as the
  identity. At reducible-and-instances transparency it does not prove the
  equality with `MulEquiv.refl`.
- `simp only [MulEquiv.refl_apply]` does not rewrite an application of the
  unexpanded equivalence. Clients obtain the identity behaviour by
  reflexivity at default transparency or after unfolding the definition. A
  `normClass` evaluation lemma for that purpose is the separate later unit
  M093.006.

Together these checks verify the reduced import closure, the preserved
declaration and its identity behaviour. They do not constitute independent
semantic acceptance.

## Host comparison and scope

The existing `Langlands.LocalClassField.NormQuotient` in
`Langlands/ClassFieldTheory/Local/Norms.lean` is an `abbrev` with
independent field universes `u` and `v` and a `[FiniteDimensional K L]`
premise. The full telescopes differ. The private check verified one
specialization by reflexivity: with a shared universe and
`[FiniteDimensional K L]`, the concrete target `Kˣ ⧸ localNormSubgroup K L`
equals the host `NormQuotient K L`, and `localNormSubgroup K L` equals the
host `normSubgroup K L`. The host definitions, instances,
`normQuotientTowerProjection` and `normQuotientTowerNorm` are unchanged, and
no comparison theorem is part of this unit.

The equivalence supplies only the identity group isomorphism between the
named and concrete norm quotients. It makes no assertion about an Artin
map, reciprocity, a norm kernel, finiteness, openness, a quotient topology
or continuity. `normClass` (M093.005), the evaluation lemma
`normQuotientConcreteEquiv_normClass` (M093.006), quotient lifts, the other
equivalences, theorem statements and proofs belong to later units.

## Attribution and changes

The original copyright and author header is retained verbatim, including
Naganori Yamaguchi's 2026 copyright and the author credit
“Naganori Yamaguchi (assisted by OpenAI Codex)”. The source is Apache-2.0.
Its unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain included through
the submission's `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Both are byte-identical to the retained source snapshot. Neither the
original NOTICE nor the supplement's per-directory third-party attribution
files list `NormQuotient.lean`.

Worker 248 extracted and documented M093.004 on 29 October 2026, added the
namespace prefix, replaced the source imports with the published
`normQuotientCommGroup` module, and omitted the unused universe and all
other source declarations. The source telescope, docstring and definition
body were retained. No other worker's draft or patch10 implementation was
reused.

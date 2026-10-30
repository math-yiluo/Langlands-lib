# Homomorphisms descended through the general norm quotient

`Langlands.NYLL.LocalFieldTheory.normQuotientLift` turns a homomorphism on
`Kˣ` that kills every norm into a homomorphism on the published named
quotient `NormQuotient K L`. Its full telescope is

```lean
normQuotientLift.{u, v} {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) :
    Langlands.NYLL.LocalFieldTheory.NormQuotient K L →* M
```

Both universes are arbitrary. The fields `K` and `L` share the universe `u`.
The target group `M` lives in an independent universe `v`. The types `K`, `L`
and `M` are implicit. The instances `Field K`, `Field L`, `Algebra K L` and
`Group M` are instance-implicit. The homomorphism `f` and the hypothesis `h`
are explicit.

This is a data definition of a multiplicative homomorphism. It adds no
finite-dimensionality, separability, Galois, local-field, valuation,
topology, surjectivity or exact-kernel hypothesis.

## Meaning of the inputs and the result

For `N = localNormSubgroup K L`, the published dependencies define

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

So `N` is the actual image of the unit norm map `Lˣ → Kˣ`. The hypothesis
`h : localNormSubgroup K L ≤ f.ker` says that this image lies in the kernel
of `f`. Equivalently, `f (Units.map (Algebra.norm K) y) = 1` for every unit
`y` of `L`. The hypothesis asks only that the kernel contain the norms. It
does not ask that the kernel equal the norm subgroup, and it does not ask
that `f` be surjective.

The source of the result carries the published instance
`normQuotientCommGroup K L`. The target carries the given `Group M`
instance. The result sends the class of `x : Kˣ` to `f x`. This value does
not depend on the chosen representative, because two representatives of a
class differ by an element of `N`, and `f` sends that element to `1`.

## Construction

The source body is preserved exactly:

```lean
  change (Kˣ ⧸ localNormSubgroup K L) →* M
  let N := localNormSubgroup K L
  exact QuotientGroup.lift N f h
```

The first step exposes `NormQuotient` as its concrete quotient. The local
name `N` stands for the existing subgroup. The last step reuses Mathlib's
`QuotientGroup.lift`. In the approved Mathlib,
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 245–250 define it. For a
group `G`, a normal subgroup `N`, a monoid `M`, `φ : G →* M` and
`HN : N ≤ φ.ker`, it gives the homomorphism `G ⧸ N →* M` obtained by
descending `φ`. Lines 252–254 state `lift_mk`: on the class of `g`, the lift
returns `φ g`, and the proof is `rfl`.

The normality instance `N.Normal` that `QuotientGroup.lift` needs is found by
instance search. It is Mathlib's
`Subgroup.normal_of_isMulCommutative (localNormSubgroup K L)`, because `Kˣ`
is commutative. The compiler stores this proof as the auto-generated
auxiliary theorem `normQuotientLift._proof_1`. That theorem is an
implementation detail, not a public interface. The target `Group M` gives
the `Monoid M` structure that `QuotientGroup.lift` uses. This unit introduces
no new quotient, projection, instance or axiom.

The elaborated value is

```lean
id (let N := localNormSubgroup K L; QuotientGroup.lift N f h)
```

The `id` comes from `change`. The generated equation
`normQuotientLift.eq_1` states the same value.

## Transparency and interface boundary

`NormQuotient` and `normQuotientLift` are ordinary semireducible
definitions. Neither is a reducible abbreviation. At Lean's default
transparency the following hold by `rfl`:

- `normQuotientLift f h` is equal to
  `QuotientGroup.lift (localNormSubgroup K L) f h`, viewed on the concrete
  quotient;
- the lift sends `normClass K L x` to `f x`;
- the lift sends the concrete class of `x` to `f x`;
- the composite `(normQuotientLift f h).comp (normClass K L)` is equal to
  `f`.

At reducible transparency, `with_reducible rfl` does not prove the
evaluation on `normClass K L x`. Also, `simp only [QuotientGroup.lift_mk]`
does not rewrite an application of `normQuotientLift`, because simp does not
unfold the name. After `unfold normQuotientLift`, Mathlib's
`QuotientGroup.lift_mk` applies.

The public evaluation theorem `normQuotientLift_normClass` is the separate
later unit M093.008. The public surjectivity theorem
`normQuotientLift_surjective` is the separate unit M093.009. This unit
publishes only the homomorphism data. It contains neither of those theorems,
their statement targets or proofs, and it adds no `simp` lemma. Clients that
need concrete quotient constructions can use the published
`normQuotientConcreteEquiv K L` as the explicit representation boundary.

## General norm convention

The definition uses Mathlib's unrestricted `Algebra.norm K`, as do the
published `normUnits`, `localNormSubgroup` and `NormQuotient`. The algebra
norm is defined without a finite-module hypothesis. If `L` is not a finite
`K`-module, `Algebra.norm_eq_one_of_not_module_finite` says that the norm is
constantly `1`. In `Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define
the norm as the determinant of multiplication, and lines 76–79 state and
prove that theorem. In that case the norm image on units is the trivial
subgroup. Then every homomorphism `Kˣ →* M` satisfies the hypothesis `h`, and
the lift is defined on the quotient by the trivial subgroup.

A finiteness premise would restrict this construction without need. It would
also change the source telescope and break agreement with the general
published dependencies. Results that need finiteness add it themselves. This
definition gives no Artin map, reciprocity law, norm-kernel statement,
finiteness statement or continuity statement.

## Source, adaptation and reuse

This is source unit M093.007 in the published NYLL declaration partition
`notes/reuse/nyll-public-port/m073-m096.md`. There it follows `M093.006.END`.
The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`. It is kept in the
registered source `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

Lines 1–100 of the 381-line original were read in full, and the
declaration headers of the rest of the file were listed. Lines 1–5 carry the
attribution. Line 24 declares the universes `u v`. Lines 26–54 hold the
published subgroup, quotient, group instance, representation equivalence and
projection. Lines 56–63 hold the published M093.006 theorem. Lines 65–66 are
the docstring of this definition, and lines 67–72 are its declaration and
body. The later evaluation theorem (lines 74–81), the surjectivity theorem
(lines 83–91) and all later declarations are excluded.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientLift` | `Langlands.NYLL.LocalFieldTheory.normQuotientLift` |

The telescope, universes, docstring and body are unchanged. Worker 248 added
the namespace prefix, a modification record and this documentation. Worker
248 also replaced the source imports with the published U006 proof module and
omitted all other source declarations. The `noncomputable section` is
retained. The published partition records no patch10 change to this module.
No other worker's draft or implementation was reused.

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U006.Proofs`.
This respects the partition's `M093.006.END` dependency. Its published chain
is U006 Proofs → U006 Statements → U005 → U004 → U003 → U002 → U001 →
NormUnits/U002 → `Mathlib.RingTheory.Norm.Transitivity`. That chain supplies
the unit norm, its range, the named quotient and its group instance, the
representation equivalence, `normClass` and Mathlib's quotient API,
including `QuotientGroup.lift`. No direct Mathlib import is needed. The
definition does not use any M092 theorem, the M093.006 theorem or any later
M093 declaration.

Fresh searches of TaskHub tasks, the current Library, staged candidates and
the approved Mathlib found no existing `normQuotientLift` and no duplicate
task. The host definition `Langlands.LocalClassField.finiteNormQuotientMap`
(`Langlands/ClassFieldTheory/Local/FiniteArtin.lean` lines 60–68) also uses
`QuotientGroup.lift`. However, it needs a topological field with
`IsTopologicalRing K` and a `FiniteAbelianExtension K`, and it takes a
continuous homomorphism into that extension's Galois group. It therefore does
not replace this unrestricted named NYLL lift into an arbitrary group. No
host declaration is changed or compared by a public theorem here.

The related registration `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The errata locations in the workspace, the project and the current Library
were checked for both registrations. No applicable erratum was found.

## Development checks

The approved Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) built the definition with zero
errors and zero warnings. Declaration inspection reports an ordinary
definition with the universe parameters `u` and `v`. It uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

A separate private probe also built without errors. Its only warnings come
from the probe itself, which prints the auxiliary normality theorem. The
probe checks the following:

- the unapplied constant has nine binders with the binder kinds listed
  above;
- the source `MulOne` argument of the result is the inferred projection of
  `normQuotientCommGroup K L`, and the target `MulOne` argument is the
  inferred one from `Group M`;
- the `rfl` equalities and the transparency failures described above;
- equality with the lift over `(Units.map (Algebra.norm K)).range`;
- the equivalence of `h` with `f` killing every unit norm;
- uniqueness: any homomorphism `g` on the named quotient with
  `g.comp (normClass K L) = f` equals the lift, by
  `QuotientGroup.monoidHom_ext`;
- the trivial norm subgroup when `L` is not a finite `K`-module;
- instantiation with fields in `Type` and a target group in `Type 2`;
- with a shared universe and `IsTopologicalRing K`, the underlying
  homomorphism of the host `finiteNormQuotientMap` equals this lift for the
  intermediate field, by `rfl`.

These private checks are not part of the public candidate. They support
independent review. They are not acceptance evidence, and they are not
additional public theorem units.

## Attribution

The original 2026 Naganori Yamaguchi copyright and author header is kept
verbatim, including “Naganori Yamaguchi (assisted by OpenAI Codex)”. The
source is licensed under Apache-2.0. The Lean file adds an explicit
modification record dated 29 October 2026. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are kept through the
submission's `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Both
files are byte-identical to the original. The source NOTICE has no
third-party entry specific to NormQuotient. Worker 248 performed this
extraction. No other project worker contributed code or a reused draft to
this unit.

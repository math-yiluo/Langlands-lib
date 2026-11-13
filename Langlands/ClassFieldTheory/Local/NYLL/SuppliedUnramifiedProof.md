# The NYLL unramified class for supplied local-field data: proof

This module proves

```lean
theorem Langlands.LocalClassField.NYLL.suppliedUnramifiedValuedExtension :
    Langlands.LocalClassField.NYLL.SuppliedUnramifiedValuedExtensionStatement.{u, v}
```

The target is published in
`Langlands.ClassFieldTheory.Local.NYLL.SuppliedUnramifiedStatement`. For a
prime `p`, p-adic fields `F : PadicField.{u} p` and `E : PadicField.{v} p`
with a finite-dimensional algebra `F.Carrier → E.Carrier` that is a scalar
tower over `Padic p`, and arbitrary supplied data `TF`, `TE`, it says: once the
supplied topologies, valuative relations and local-field structures are
installed, every `Valuation.HasExtension` between the two valuations gives

1. `Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier]` for Mathlib's integer algebra; and
2. for every such finiteness instance, NYLL's class
   `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension F.Carrier E.Carrier`
   holds exactly when the ramification index of the maximal ideal of
   `TE.Integers` over `TF.Integers`, computed with
   `PadicField.TopologicalData.relativeIntegerAlgebra TF TE`, is `1`.

The theorem has exactly the published type, with the same universe parameters
`u, v`, and adds no premise.

## The key equation

The proof rests on one equation of algebra structures on
`𝒪[F.Carrier] → 𝒪[E.Carrier]`:

```lean
halg : Valuation.HasExtension.instAlgebraInteger =
    PadicField.TopologicalData.relativeIntegerAlgebra TF TE
```

- `TF.Integers` is by definition `(ValuativeRel.valuation F.Carrier).integer`
  for `TF.valuativeRel`, which is `𝒪[F.Carrier]` once that relation is
  installed. Likewise `TE.Integers` is `𝒪[E.Carrier]`. So both sides of `halg`
  are algebras between the same two types.
- Mathlib's `Valuation.HasExtension.instAlgebraInteger`
  (`Mathlib.RingTheory.Valuation.Extension`) has `algebraMap` equal to
  `(algebraMap F.Carrier E.Carrier).restrict`, so it sends an integral `r` to
  the subtype element with value `algebraMap F.Carrier E.Carrier r`.
- `relativeIntegerAlgebra TF TE` is `(relativeIntegerMap TF TE).toAlgebra`
  (`Langlands.LocalField.RelativeIntegers`). The map `relativeIntegerMap TF TE`
  is the codomain restriction of `algebraMap F.Carrier E.Carrier` composed with
  the subtype inclusion of `TF.Integers`, so it also sends `r` to the subtype
  element with value `algebraMap F.Carrier E.Carrier r`.

The two `algebraMap`s therefore agree on every element by `rfl`. Mathlib's
`Algebra.algebra_ext` (`Mathlib.Algebra.Algebra.Defs`) turns agreement of the
`algebraMap`s into equality of the two `Algebra` structures, including their
scalar actions. Those scalar actions are defined differently and are not
definitionally equal, which is why the proof rewrites along `halg` instead of
using the two algebras interchangeably.

## Proof steps

1. Introduce `p`, the primality instance, `F`, `E`, the three instance
   binders on `F.Carrier → E.Carrier`, and `TF`, `TE`. Install
   `TF.topology`, `TF.valuativeRel`, `TF.localField`, `TE.topology`,
   `TE.valuativeRel` and `TE.localField` with local `let`s, matching the
   statement's `letI`s, and introduce the quantified
   `Valuation.HasExtension` instance.
2. Prove `halg` as above.
3. **First conjunct.** The published theorem
   `Langlands.LocalClassField.NYLL.relativeIntegerStructure p F E TF TE` proves
   `IsIntegralClosure` and `Module.Finite TF.Integers TE.Integers` with
   `relativeIntegerAlgebra TF TE` installed. Its second component, rewritten
   right to left with `halg`, is `Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier]` for
   Mathlib's integer algebra.
4. **Second conjunct.** Take the quantified finiteness instance. The class
   `IsUnramifiedValuedExtension` has a single field,
   `maximalIdeal_ramificationIdx_eq_one`, stating that the ramification index
   of the maximal ideal of `𝒪[E.Carrier]` over `𝒪[F.Carrier]` is `1` for
   Mathlib's integer algebra.
   - Forward: extract the field from the class and rewrite it with `halg`; the
     result is the right-hand side, the same ramification-index equation for
     `relativeIntegerAlgebra TF TE`.
   - Backward: build the class with its anonymous constructor; rewriting the
     goal with `halg` turns the field into the right-hand side, which is the
     hypothesis.

The finiteness instance only appears as a parameter of the class; the
ramification-index equation itself does not depend on it.

## Published inputs and modules

The direct imports are the statement module
`Langlands.ClassFieldTheory.Local.NYLL.SuppliedUnramifiedStatement` and
`Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof`.
The one Library theorem applied is

| Fully qualified theorem | Module |
| --- | --- |
| `Langlands.LocalClassField.NYLL.relativeIntegerStructure` | `Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof` |

The definitions unfolded in the key equation are
`Langlands.PadicField.TopologicalData.relativeIntegerAlgebra` and
`Langlands.PadicField.TopologicalData.relativeIntegerMap`
(`Langlands.LocalField.RelativeIntegers`) and
`Langlands.PadicField.TopologicalData.Integers`
(`Langlands.LocalField.Normalization.Definitions`). From the pinned Mathlib the
proof uses `Algebra.algebra_ext` (`Mathlib.Algebra.Algebra.Defs`) and the
instance `Valuation.HasExtension.instAlgebraInteger`
(`Mathlib.RingTheory.Valuation.Extension`). The proof does not use the NYLL
source proofs; the NYLL class enters only through the statement.

The statement's Lean/Markdown pair and all imported modules are unchanged.
Every instance installed by this proof is local to the theorem; no global
instance or other declaration is added.

## Provenance and authorship

This is a proof of an internal supplied-data bridge; no theorem of the
literature is translated. The same local transport along an `Algebra.algebra_ext`
equation appears in the published
`Langlands.ClassFieldTheory.Local.NYLL.ZeroRamificationHostProof` (its
equation `hA`).

Worker 8 wrote the Lean proof and an initial explanation in an earlier project
instance. Worker 926 rechecked it and shared it unchanged as revision 1 of the
draft of Task 926 (`4b320e90-051e-401c-af0d-7530a66652e3`). Worker 5163
reused the Lean file from that draft without changes for Task 5839
(`11992e30-7045-4dba-aa21-746df362dc81`), rechecked the inputs and the proof,
and rewrote this explanation. No external source code is copied into this
pair.

## Verification

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled
this module against the published statement at Library base
`8ff9abe94fbb8d61ec05e4a00fc92f7cf1534b96` with zero errors or warnings
(diagnostic `eb4b635b-8d95-4ea8-a65a-2bc7d454cbc5`). Inspection of
`suppliedUnramifiedValuedExtension` reported a theorem with universe parameters
`u, v` whose only axioms are `propext`, `Classical.choice` and `Quot.sound`.
These are development checks; independent proof review and the candidate's
exact-target validation and publication are separate.

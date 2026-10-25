# Finite idele invariant restriction from local relative restriction

Worker 21 states the internal supporting target
`Langlands.ClassField.Global.FiniteIdeleInvariantRestrictionStatement.{u}`.
It is a closed `Prop` definition in the arbitrary common universe `u`.
It quantifies every supplied local invariant family
`I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p` and assumes only
`∀ (p : ℕ) [Fact p.Prime], (I p).RelativeRestriction`.
Its conclusion is the published predicate
`Langlands.ClassField.Global.FiniteIdeleInvariantRestriction I`.

Concretely, take number fields `F`, `K`, and `E` in `Type u` in an algebra
tower `F → K → E`, with `E/F` Galois. Take finite places `v` of `F`,
`w` of `K`, and `q` of `E`, with the three lying-over relations
`w/v`, `q/w`, and `q/v`. For every actual degree-two idele-cohomology
class `c` for `E/F`, the conclusion is

```lean
finiteIdeleInvariant I w q (relativeIdeleRestriction F K E 2 c) =
  Module.finrank (v.adicCompletion F) (w.adicCompletion K) •
    finiteIdeleInvariant I v q c
```

Here the `E/K` Galois instance is derived from `E/F`. The degree is the
degree of the actual completed extension, with its existing completion
algebra. The class map is the existing restriction on actual idele
cohomology. The same top place `q` occurs on both sides. There is no
normality hypothesis on `K/F`, no place-choice independence assumption,
and no assumption of local inflation compatibility, relative images,
arithmetic normalization, or conjugacy naturality.

## Internal provenance

This target packages the remaining coordinate restriction obligation
from `IdeleFiniteInvariantTransfer`; it does not redefine that predicate
or any arithmetic object. The intended derivation applies the supplied
local `RelativeRestriction` law to the canonical completed base and
intermediate fields. `CompletionPadicTower` supplies their scalar
compatibility at the common residue prime and identifies the transported
upper invariant with its original canonical invariant for arbitrary `I`.
`IdeleFiniteTower.ideleLocalMap_relativeIdeleRestriction` identifies the
localized global restriction with the local restriction. Thus the target
requires no additional arithmetic theorem or new assertion from the
literature.

This pair contains a statement only. Its proof, the total-family
restriction consequence, and the construction of global idele-class
invariant maps are separate work. In particular, it does not prove
`GlobalInvariantStatement`. Existing statement and imported pairs are
unchanged.

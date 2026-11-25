# The finite tower restriction diagram at field universes zero: proof

The module `Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroRestrictionProof`
proves the published proposition
`Langlands.LocalClassField.UniverseZero.FiniteAbelianRestrictionTypeZeroStatement` with
the theorem

```lean
theorem Langlands.LocalClassField.UniverseZero.finiteAbelianRestrictionTypeZero :
    FiniteAbelianRestrictionTypeZeroStatement
```

Its type is exactly the target. The target is the transparent alias of the Library
proposition `Langlands.LocalClassField.FiniteAbelianRestriction.{0, 0, 0}` in
[`TypeZeroStatement`](TypeZeroStatement.lean). The module imports the target
module and the supporting module
[`FiniteGeometricQuotient`](../FiniteGeometricQuotient.lean). It changes neither
and imports no module under `Langlands/NYLL/`.

## What is proved

Fix a prime `p`, fields `F E L : PadicField.{0} p` in a tower `F ⊆ E ⊆ L`, the
algebra, scalar-tower and finite-dimension instances of the Library proposition,
the hypothesis `IsAbelianGalois F.Carrier L.Carrier`, and an arbitrary supplied
`TF : F.TopologicalData`. Give `F.Carrier` the topology `TF.topology`. The Library
proposition derives `IsAbelianGalois F.Carrier E.Carrier` by `IsAbelianGalois.tower_bot`.
Then there are continuous multiplicative equivalences `rE` and `rL` from the
norm quotients for `E/F` and `L/F` to `Gal(E/F)` and `Gal(L/F)` such that, for
every `a : F.Carrierˣ`, restricting `rL [a]` to `E` with
`AlgEquiv.restrictNormalHom E.Carrier` gives `rE [a]`.

## Proof

1. **Instances.** The proof installs `TF.topology` and the instance
   `IsAbelianGalois F.Carrier E.Carrier` from `IsAbelianGalois.tower_bot`, the
   same term the Library proposition uses. `IsAbelianGalois` is a proposition, so
   any two such instances agree anyway.
2. **The witnesses.** For `D = E` and `D = L`, the Library theorem
   `continuous_geometricArtin F TF D D.canonicalTopologicalData` gives
   continuity of `geometricSymbol F D.Carrier` for `TF.topology`. The supporting
   theorem `exists_quotientEquiv_geometricSymbol` then gives `rE` and `rL`, with
   `rE [a] = geometricSymbol F E.Carrier a` and
   `rL [a] = geometricSymbol F L.Carrier a`. The canonical data of `E` and `L`
   are used only to obtain these continuity proofs. The geometric symbol itself
   does not depend on them.
3. **Restriction.** After rewriting both sides by step 2, the goal is the
   Library theorem `restrictNormalHom_geometricSymbol F L.Carrier E.Carrier a`.

## Scope and provenance

Both witnesses are quotients of the Library's geometric finite Artin symbol. The
proof adds no hypothesis to the target. The mathematical source of the target
is Serre, *Local Fields*, XIII.4, Proposition 12 (source
`serre-1979-local-fields`), in the geometric convention explained in
[`FiniteReciprocityStatement.md`](../FiniteReciprocityStatement.md). The proof
assembles published Library theorems, starting from the Library's own finite
Artin symbol.

The module compiled without errors or warnings with Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
